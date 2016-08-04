use std::fmt;
use std::path::{Path, PathBuf};

use syntax::abi::Abi;
use syntax::ast::{self, ItemKind, Lifetime};
use syntax::codemap::CodeMap;
use syntax::parse;
use syntax::visit::{self, Visitor};

use errors::Error;

/// A bound is either a type or a lifetime.
///
/// As generic types and lifetimes share the same representation it is useful to distinguish them.
#[derive(Clone, Debug)]
pub enum Bound {
    /// A generic type.
    Type(Generic),
    /// A generic lifetime.
    Lifetime(Generic),
}

/// A variant of the fields of a structure or an enum.
#[derive(Clone, Debug)]
pub enum FieldVariant {
    /// A single unit.
    ///
    /// e.g. `struct Unit;` or `A` and `B` in `enum Enum { A, B, }`
    Unit,
    /// The fields of a tuple.
    ///
    /// e.g. `u32` and `String` in`(u32, String)`
    Tuple(Option<Vec<String>>),
    /// The fields of a structure.
    ///
    /// e.g. `one: u32` and `two: String` in `struct Struct { one: u32, two: String }`
    Struct(Option<Vec<Doc<Variable>>>),
}

impl fmt::Display for FieldVariant {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            FieldVariant::Unit => write!(f, ""),
            FieldVariant::Tuple(ref tuple) => {
                write!(f,
                       "({})",
                       tuple.as_ref().map_or("".to_string(), |v| v.join(", ")))
            }
            FieldVariant::Struct(ref opt) => {
                match *opt {
                    Some(ref fields) if !fields.is_empty() => {
                        let fields = fields.iter()
                            .map(|field| {
                                format!("    {},", field.to_string().replace("\n", "\n    "))
                            })
                            .collect::<Vec<_>>()
                            .join("\n");
                        write!(f, " {{\n{}\n}}", fields)
                    }
                    _ => write!(f, " {{}}"),
                }
            }
        }
    }
}

/// Default visibility
#[derive(Clone, Debug)]
pub enum DefaultVisibility {
    Private,
    Public,
}

impl From<bool> for DefaultVisibility {
    fn from(visible: bool) -> DefaultVisibility {
        if visible {
            DefaultVisibility::Public
        } else {
            DefaultVisibility::Private
        }
    }
}

/// A documentation entry.
#[derive(Clone, Debug)]
pub struct Doc<T> {
    /// The documentation comments.
    pub doc_string: Option<String>,
    /// The item being described.
    pub item: T,
}

impl<T> Doc<T> {
    /// Creates a new `Doc` without doc comments.
    pub fn new(item: T) -> Doc<T> {
        Doc {
            doc_string: None,
            item: item,
        }
    }

    /// Creates a new `Doc` with the `doc_string` describing the `item`.
    pub fn with_docs(item: T, doc_string: String) -> Doc<T> {
        if doc_string.is_empty() {
            return Doc::new(item);
        }
        Doc {
            doc_string: Some(doc_string),
            item: item,
        }
    }
}

impl<T> fmt::Display for Doc<T>
    where T: fmt::Display
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(ref doc_string) = self.doc_string {
            for line in doc_string.lines() {
                try!(writeln!(f, "/// {}", line));
            }
        }
        write!(f, "{}", self.item)
    }
}

/// The documentation entries of a file.
///
/// Holds the documentation entries of a file. The entries are listed under the corresponding item
/// types. This makes it easier to search for a specific item.
#[derive(Clone, Debug)]
pub struct FileDoc {
    /// The enum documentations.
    pub enums: Vec<Doc<Enum>>,
    /// The function documentations.
    pub functions: Vec<Doc<FnDecl>>,
    /// The struct documentations.
    pub structs: Vec<Doc<Struct>>,
    path: PathBuf,
}

impl FileDoc {
    /// Creates a new empty `FileDoc`.
    pub fn new() -> FileDoc {
        FileDoc {
            enums: Vec::new(),
            functions: Vec::new(),
            structs: Vec::new(),
            path: PathBuf::new(),
        }
    }

    /// Creates a new `FileDoc` with the given `Path`.
    pub fn with_path(path: &Path) -> FileDoc {
        FileDoc {
            enums: Vec::new(),
            functions: Vec::new(),
            structs: Vec::new(),
            path: path.to_path_buf(),
        }
    }

    /// Adds a `Doc<Enum>` to the enum documentations.
    pub fn add_enum(&mut self, enum_doc: Doc<Enum>) {
        self.enums.push(enum_doc);
    }

    /// Adds a `Doc<FnDecl>` to the function documentations.
    pub fn add_function(&mut self, fn_doc: Doc<FnDecl>) {
        self.functions.push(fn_doc);
    }

    /// Adds a `Doc<Struct>` to the struct documentations.
    pub fn add_struct(&mut self, struct_doc: Doc<Struct>) {
        self.structs.push(struct_doc);
    }

    /// Returns the `Path` of the file.
    pub fn path(&self) -> &Path {
        &self.path
    }

    /// Extracts documentation from the [`path()`].
    ///
    /// [`path()`]: #method.path
    pub fn extract_from_file(&mut self) {
        let session = parse::ParseSess::new();
        let krate = match parse::parse_crate_from_file(self.path(), Vec::new(), &session) {
            Ok(krate) => krate,
            Err(_) => return,
        };
        let mut visitor = DocVisitor {
            docs: self,
            codemap: session.codemap(),
        };
        visit::walk_crate(&mut visitor, &krate);
    }
}

impl Default for FileDoc {
    fn default() -> FileDoc {
        FileDoc::new()
    }
}

/// A public enum declaration.
///
/// All fields are inherently public.
#[derive(Clone, Debug)]
pub struct Enum {
    /// The identifier of the enum.
    pub ident: String,
    /// The fields of the enum.
    pub fields: Vec<Doc<EnumField>>,
    /// The generic types of the enum.
    pub generics: Option<Vec<Generic>>,
    /// The generic lifetimes of the enum.
    pub lifetimes: Option<Vec<Generic>>,
    /// The `where` clause constraining the generic types and lifetimes of the enum.
    pub where_clause: Option<WhereClause>,
}

impl fmt::Display for Enum {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let generics = generic_string(&self.generics, &self.lifetimes);
        let where_clause = self.where_clause
            .as_ref()
            .map_or(" ".to_string(), |clause| format!("\n    {}\n", clause));
        let fields = self.fields
            .iter()
            .map(|field| format!("    {},", field.to_string().replace("\n", "\n    ")))
            .collect::<Vec<_>>()
            .join("\n");
        write!(f,
               "pub enum {ident}{generics}{where_clause}{{\n{fields}\n}}",
               ident = self.ident,
               generics = generics,
               where_clause = where_clause,
               fields = fields)
    }
}

/// A field of an enum
#[derive(Clone, Debug)]
pub struct EnumField {
    /// The identifier of the field.
    pub ident: String,
    /// The body of the field.
    pub body: FieldVariant,
}

impl fmt::Display for EnumField {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}{}", self.ident, self.body)
    }
}

/// A public function declaration.
///
/// The minimal function declaration simply has an identifier, all the other parts are optional
/// e.g. input parameters, output, generics, etc.
/// This only describes the signature of the function. The body is excluded because it does not
/// serve any purpose for the documentation.
///
/// # Examples
///
/// The `FnDecl` of a minimal function can be created as follows:
///
/// ```rust
/// # use rod::parser::FnDecl;
/// pub fn minimal() {
///     // body omitted
/// }
///
/// FnDecl {
///     ident: "minimal".to_string(),
///     args: None,
///     output: None,
///     generics: None,
///     lifetimes: None,
///     where_clause: None,
///     unsafety: false,
///     ext: None,
/// };
/// ```
#[derive(Clone, Debug)]
pub struct FnDecl {
    /// The identifier of the function.
    pub ident: String,
    /// The input parameters of the function.
    pub args: Option<Vec<Variable>>,
    /// The output type of the function.
    pub output: Option<String>,
    /// The generic types of the function.
    pub generics: Option<Vec<Generic>>,
    /// The generic lifetimes of the function.
    pub lifetimes: Option<Vec<Generic>>,
    /// The `where` clause constraining the generic types and lifetimes of the function.
    pub where_clause: Option<WhereClause>,
    /// Whether the function is `unsafe`.
    pub unsafety: bool,
    /// The extern type of the function.
    pub ext: Option<String>,
}

impl fmt::Display for FnDecl {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let generics = generic_string(&self.generics, &self.lifetimes);
        write!(f,
               "pub {unsafety}{ext}fn {ident}{generics}({args}){output}{where_clause}",
               unsafety = if self.unsafety {
                   "unsafe "
               } else {
                   ""
               },
               ext = self.ext.as_ref().map_or("".to_string(), |s| format!("extern \"{}\" ", s)),
               ident = self.ident,
               generics = generics,
               args = self.args.as_ref().map_or("".to_string(), |args| {
                   args.iter().map(|arg| arg.to_string()).collect::<Vec<_>>().join(", ")
               }),
               where_clause = self.where_clause
                   .as_ref()
                   .map_or("".to_string(), |clause| format!("\n    {}", clause)),
               output = self.output.as_ref().map_or("".to_string(), |out| format!(" -> {}", out)))
    }
}

/// A generic type of lifetime that may be bounded.
///
/// A generic type `T`, lifetime `'a` or their bounded version `T: Display`, `'a: 'b + 'c`.
#[derive(Clone, Debug)]
pub struct Generic {
    /// The identifier of the generic.
    pub ident: String,
    /// The bounds constraining the generic.
    pub bounds: Option<Vec<String>>,
}

impl Generic {
    /// Creates a new `Generic` with the given identifier.
    pub fn new(ident: String) -> Generic {
        Generic {
            ident: ident,
            bounds: None,
        }
    }

    /// Creates a new `Generic` with the given identifier and bounds.
    pub fn with_bounds(ident: String, bounds: Vec<String>) -> Generic {
        Generic {
            ident: ident,
            bounds: Some(bounds),
        }
    }

    /// Creates a new `Generic` lifetime from the AST.
    pub fn from_ast_lifetime(lifetime: &Lifetime, bounds: &[Lifetime]) -> Generic {
        let ident = lifetime.name.to_string();
        let bound = if bounds.is_empty() {
            None
        } else {
            Some(bounds.iter().map(|l| l.name.to_string()).collect())
        };
        Generic {
            ident: ident,
            bounds: bound,
        }
    }
}

impl fmt::Display for Generic {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.bounds {
            Some(ref bounds) => write!(f, "{}: {}", self.ident, bounds.join(" + ")),
            None => write!(f, "{}", self.ident),
        }
    }
}

/// A public struct declaration.
///
/// Only public fields are included because private fields are not exposed to the documentation.
///
/// # Examples
///
/// For the documentation only public fields are relevant and therefore private members are
/// omitted from the examples.
/// The following examples show the minimal representation of the three available forms:
///
/// > **Note:** Keep in mind that struct members are by default private and thus require the `pub`
/// keyword.
///
/// ## Unit
///
/// ```rust
/// # use rod::parser::{FieldVariant, Struct};
/// pub struct Unit;
///
/// Struct {
///     ident: "Unit".to_string(),
///     fields: FieldVariant::Unit,
///     generics: None,
///     lifetimes: None,
/// };
/// ```
///
/// ## Tuple
///
/// A tuple contains all types of the respective values.
///
/// ```rust
/// # use rod::parser::{FieldVariant, Struct};
/// pub struct Point(pub i32, pub i32);
///
/// Struct {
///     ident: "Point".to_string(),
///     fields: FieldVariant::Tuple(Some(vec!["i32".to_string(), "i32".to_string()])),
///     generics: None,
///     lifetimes: None,
/// };
/// ```
///
/// ## Classic struct
///
/// A classic struct has named members which use the same declaration as a variable with explicit
/// type annotation. For this reason a member uses the `Variable` representation.
///
/// ```rust
/// # use rod::parser::{Doc, FieldVariant, Struct, Variable};
/// pub struct Classic {
///     pub x: i32,
///     pub y: i32,
/// }
///
/// let x = Variable::new("x".to_string(), "i32".to_string());
/// let y = Variable::new("y".to_string(), "i32".to_string());
/// Struct {
///     ident: "Classic".to_string(),
///     fields: FieldVariant::Struct(Some(vec![Doc::new(x), Doc::new(y)])),
///     generics: None,
///     lifetimes: None,
/// };
/// ```
#[derive(Clone, Debug)]
pub struct Struct {
    /// The identifier of the struct.
    pub ident: String,
    /// The public fields of the struct.
    pub fields: FieldVariant,
    /// The generic types of the struct.
    pub generics: Option<Vec<Generic>>,
    /// The generic lifetimes of the struct.
    pub lifetimes: Option<Vec<Generic>>,
}

impl fmt::Display for Struct {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let generics = generic_string(&self.generics, &self.lifetimes);
        let semicolon = match self.fields {
            FieldVariant::Struct(_) => "".to_string(),
            _ => ";".to_string(),
        };
        write!(f,
               "pub struct {ident}{generics}{fields}{semicolon}",
               ident = self.ident,
               generics = generics,
               fields = self.fields,
               semicolon = semicolon)
    }
}

/// A variable.
///
/// A variable has an identifier and a type, for instance `var: String`.
#[derive(Clone, Debug)]
pub struct Variable {
    /// The identifier of the variable.
    pub ident: String,
    /// The type of the variable.
    pub ty: String,
}

impl Variable {
    /// Creates a new `Variable` with its type.
    pub fn new(ident: String, ty: String) -> Variable {
        Variable {
            ident: ident,
            ty: ty,
        }
    }
}

impl fmt::Display for Variable {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}: {}", self.ident, self.ty)
    }
}

/// A `where` clause of a generic definition.
///
/// Generic types and lifetimes can be constrained in a `where` clause.
#[derive(Clone, Debug)]
pub struct WhereClause {
    /// The the constrained generic types of the function.
    pub generics: Option<Vec<Generic>>,
    /// The the constrained generic lifetimes of the function.
    pub lifetimes: Option<Vec<Generic>>,
}

impl From<Vec<Bound>> for WhereClause {
    fn from(bounds: Vec<Bound>) -> WhereClause {
        let mut generics = Vec::new();
        let mut lifetimes = Vec::new();
        for bound in bounds {
            match bound {
                Bound::Type(generic) => generics.push(generic),
                Bound::Lifetime(lifetime) => lifetimes.push(lifetime),
            }
        }
        let generics = if generics.is_empty() {
            None
        } else {
            Some(generics)
        };
        let lifetimes = if lifetimes.is_empty() {
            None
        } else {
            Some(lifetimes)
        };
        WhereClause {
            generics: generics,
            lifetimes: lifetimes,
        }
    }
}

impl fmt::Display for WhereClause {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f,
               "where {}",
               join_generics_and_lifetimes(&self.generics.as_ref().unwrap_or(&Vec::new()),
                                           &self.lifetimes.as_ref().unwrap_or(&Vec::new())))
    }
}

struct DocVisitor<'a> {
    docs: &'a mut FileDoc,
    codemap: &'a CodeMap,
}

impl<'a> DocVisitor<'a> {
    fn add_item(&mut self, ident: String, doc: String, item: &ItemKind) -> Result<(), Error> {
        match *item {
            ItemKind::Enum(ref enum_def, ref generics) => {
                let fields: Vec<_> = try!(enum_def.variants
                    .iter()
                    .map(|variant| {
                        let ident = variant.node.name.to_string();
                        let doc_string = try!(convert_doc_string(&variant.node.attrs,
                                                                 self.codemap));
                        let body = try!(convert_variantdata(&variant.node.data,
                                                            self.codemap,
                                                            &DefaultVisibility::Public));
                        let enum_field = EnumField {
                            ident: ident,
                            body: body,
                        };
                        Ok(Doc::with_docs(enum_field, doc_string))
                    })
                    .collect::<Result<_, Error>>());
                let lifetimes = convert_lifetimes(&generics.lifetimes);
                let gens = try!(convert_generics(&generics.ty_params, self.codemap));
                let where_clause =
                    try!(convert_where_predicates(&generics.where_clause.predicates, self.codemap));
                let enum_def = Enum {
                    ident: ident,
                    fields: fields,
                    generics: gens,
                    lifetimes: lifetimes,
                    where_clause: where_clause,
                };
                self.docs.add_enum(Doc::with_docs(enum_def, doc));
            }
            ItemKind::Fn(ref fn_decl, ref unsafety, _, ref abi, ref generics, _) => {
                let args = try!(convert_args(&fn_decl.inputs, self.codemap));
                let output = match fn_decl.output {
                    ast::FunctionRetTy::Default(_) => None,
                    _ => {
                        let output = try!(self.codemap.span_to_snippet(fn_decl.output.span()));
                        if output == "()" {
                            None
                        } else {
                            Some(output)
                        }
                    }
                };
                let unsafety = match *unsafety {
                    ast::Unsafety::Unsafe => true,
                    ast::Unsafety::Normal => false,
                };
                let ext = match *abi {
                    Abi::Rust => None,
                    _ => Some(abi.name().to_string()),
                };
                let lifetimes = convert_lifetimes(&generics.lifetimes);
                let gens = try!(convert_generics(&generics.ty_params, self.codemap));
                let where_clause =
                    try!(convert_where_predicates(&generics.where_clause.predicates, self.codemap));
                let function = FnDecl {
                    ident: ident,
                    args: args,
                    output: output,
                    lifetimes: lifetimes,
                    generics: gens,
                    where_clause: where_clause,
                    unsafety: unsafety,
                    ext: ext,
                };
                self.docs.add_function(Doc::with_docs(function, doc));
            }
            ItemKind::Struct(ref data, ref generics) => {
                let fields =
                    try!(convert_variantdata(data, self.codemap, &DefaultVisibility::Private));
                let gens = try!(convert_generics(&generics.ty_params, self.codemap));
                let lifetimes = convert_lifetimes(&generics.lifetimes);
                let st = Struct {
                    ident: ident,
                    fields: fields,
                    generics: gens,
                    lifetimes: lifetimes,
                };
                self.docs.add_struct(Doc::with_docs(st, doc));
            }
            _ => println!("Not supported"),
        }
        Ok(())
    }
}

impl<'a> Visitor for DocVisitor<'a> {
    fn visit_item(&mut self, item: &ast::Item) {
        if ast::Visibility::Public == item.vis {
            let ident = item.ident.to_string();
            let doc_string = match convert_doc_string(&item.attrs, self.codemap) {
                Ok(doc) => doc,
                Err(_) => return,
            };
            if let Err(_) = self.add_item(ident, doc_string, &item.node) {
                return;
            }
        }
        match item.node {
            ItemKind::Mac(_) => (),
            _ => visit::walk_item(self, item),
        }
    }
}

fn convert_args(args: &[ast::Arg], codemap: &CodeMap) -> Result<Option<Vec<Variable>>, Error> {
    if args.is_empty() {
        return Ok(None);
    }
    args.iter()
        .map(|arg| {
            let ty = try!(codemap.span_to_snippet(arg.ty.span));
            let pat = try!(codemap.span_to_snippet(arg.pat.span));
            Ok(Some(Variable::new(pat, ty)))
        })
        .collect()
}

fn convert_doc_string(attrs: &[ast::Attribute], codemap: &CodeMap) -> Result<String, Error> {
    if attrs.is_empty() {
        return Ok("".to_string());
    }
    let res: Vec<_> = try!(attrs.iter()
        .filter(|attr| attr.node.is_sugared_doc)
        .map(|attr| {
            let snippet = try!(codemap.span_to_snippet(attr.span));
            let trim_chars: &[_] = &['/', '!'];
            Ok(snippet.trim_left_matches(trim_chars).trim().to_string())
        })
        .collect::<Result<_, Error>>());
    Ok(res.join("\n"))
}

fn convert_variantdata(data: &ast::VariantData,
                       codemap: &CodeMap,
                       default_vis: &DefaultVisibility)
                       -> Result<FieldVariant, Error> {
    match *data {
        ast::VariantData::Unit(_) => Ok(FieldVariant::Unit),
        ast::VariantData::Tuple(ref fields, _) => {
            if fields.is_empty() {
                Ok(FieldVariant::Tuple(None))
            } else {
                let members: Vec<_> = try!(fields.iter()
                    .map(|field| {
                        if !is_field_visible(&field.vis, &default_vis) {
                            return Ok(None);
                        }
                        let snippet = try!(codemap.span_to_snippet(field.ty.span));
                        Ok(Some(snippet))
                    })
                    .collect::<Result<_, Error>>());
                let members = option_from_vec(members);
                Ok(FieldVariant::Tuple(members))
            }
        }
        ast::VariantData::Struct(ref fields, _) => {
            if fields.is_empty() {
                Ok(FieldVariant::Struct(None))
            } else {
                let members: Vec<_> = try!(fields.iter()
                    .map(|field| {
                        if !is_field_visible(&field.vis, &default_vis) {
                            return Ok(None);
                        }
                        let ident = match field.ident {
                            Some(ident) => ident.to_string(),
                            None => return Ok(None),
                        };
                        let ty = try!(codemap.span_to_snippet(field.ty.span));
                        let doc_string = try!(convert_doc_string(&field.attrs, codemap));
                        let var = Variable::new(ident, ty);
                        Ok(Some(Doc::with_docs(var, doc_string)))
                    })
                    .collect::<Result<_, Error>>());
                let members = option_from_vec(members);
                Ok(FieldVariant::Struct(members))
            }
        }
    }
}

fn convert_generics(types: &[ast::TyParam],
                    codemap: &CodeMap)
                    -> Result<Option<Vec<Generic>>, Error> {
    if types.is_empty() {
        return Ok(None);
    }
    types.iter()
        .map(|ty| {
            let ident = ty.ident.to_string();
            let bounds = try!(convert_param_bounds(&ty.bounds, codemap));
            let generic = Generic {
                ident: ident,
                bounds: bounds,
            };
            Ok(Some(generic))
        })
        .collect()
}

fn convert_lifetimes(lifetimes: &[ast::LifetimeDef]) -> Option<Vec<Generic>> {
    if lifetimes.is_empty() {
        return None;
    }
    lifetimes.iter()
        .map(|life| Some(Generic::from_ast_lifetime(&life.lifetime, &life.bounds)))
        .collect()
}

fn convert_param_bounds(bounds: &[ast::TyParamBound],
                        codemap: &CodeMap)
                        -> Result<Option<Vec<String>>, Error> {
    if bounds.is_empty() {
        return Ok(None);
    }
    let bound = try!(bounds.iter()
        .map(|bound| {
            match *bound {
                ast::TyParamBound::TraitTyParamBound(ref poly_trait, _) => {
                    codemap.span_to_snippet(poly_trait.span)
                }
                ast::TyParamBound::RegionTyParamBound(ref lifetime) => {
                    Ok(lifetime.name.to_string())
                }
            }
        })
        .collect());
    Ok(Some(bound))
}

fn convert_where_predicates(predicates: &[ast::WherePredicate],
                            codemap: &CodeMap)
                            -> Result<Option<WhereClause>, Error> {
    if predicates.is_empty() {
        return Ok(None);
    }
    let where_bounds: Vec<_> = try!(predicates.iter()
        .map(|pred| {
            match *pred {
                ast::WherePredicate::BoundPredicate(ref bound_pred) => {
                    let ident = try!(codemap.span_to_snippet(bound_pred.bounded_ty.span));
                    let bounds = try!(convert_param_bounds(&bound_pred.bounds, codemap));
                    let generic = Generic {
                        ident: ident,
                        bounds: bounds,
                    };
                    Ok(Bound::Type(generic))
                }
                ast::WherePredicate::RegionPredicate(ref region_pred) => {
                    let lifetime = Generic::from_ast_lifetime(&region_pred.lifetime,
                                                              &region_pred.bounds);
                    Ok(Bound::Lifetime(lifetime))
                }
                ast::WherePredicate::EqPredicate(_) => Err(Error::Unsupported),
            }
        })
        .collect::<Result<_, Error>>());
    Ok(Some(WhereClause::from(where_bounds)))
}

fn generic_string(generics: &Option<Vec<Generic>>, lifetimes: &Option<Vec<Generic>>) -> String {
    if generics.is_none() && lifetimes.is_none() {
        "".to_string()
    } else {
        format!("<{}>",
                join_generics_and_lifetimes(&generics.as_ref().unwrap_or(&Vec::new()),
                                            &lifetimes.as_ref().unwrap_or(&Vec::new())))
    }
}

fn is_field_visible(vis: &ast::Visibility, default_vis: &DefaultVisibility) -> bool {
    match (vis, default_vis) {
        (&ast::Visibility::Public, _) |
        (&ast::Visibility::Inherited, &DefaultVisibility::Public) => true,
        _ => false,
    }
}

fn join_generics_and_lifetimes(generics: &[Generic], lifetimes: &[Generic]) -> String {
    let mut gens = generics.iter().map(|gen| gen.to_string()).collect();
    let mut clauses: Vec<_> = lifetimes.iter().map(|life| life.to_string()).collect();
    clauses.append(&mut gens);
    clauses.join(", ")
}

fn option_from_vec<T>(vec: Vec<Option<T>>) -> Option<Vec<T>> {
    let filtered: Option<Vec<_>> = vec.into_iter().filter(|field| field.is_some()).collect();
    match filtered {
        Some(ref vec) if vec.is_empty() => return None,
        None => return None,
        _ => (),
    }
    filtered
}
