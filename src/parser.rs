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

/// A documentation entry.
#[derive(Clone, Debug)]
pub struct Doc<T> {
    /// The documentation comments.
    pub doc_string: String,
    /// The item being described.
    pub item: T,
}

/// The documentation entries of a file.
///
/// Holds the documentation entries of a file. The entries are listed under the corresponding item
/// types. This makes it easier to search for a specific item.
#[derive(Clone, Debug)]
pub struct FileDoc {
    /// The function documentations.
    pub functions: Vec<Doc<FnDecl>>,
    path: PathBuf,
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

struct DocVisitor<'a> {
    docs: &'a mut FileDoc,
    codemap: &'a CodeMap,
}

impl<T> Doc<T> {
    /// Creates a new `Doc` with the `doc_string` describing the `item`.
    pub fn new(doc_string: String, item: T) -> Doc<T> {
        Doc {
            doc_string: doc_string,
            item: item,
        }
    }
}

impl<T> fmt::Display for Doc<T>
    where T: fmt::Display
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for line in self.doc_string.lines() {
            try!(writeln!(f, "/// {}", line));
        }
        write!(f, "{}", self.item)
    }
}

impl FileDoc {
    /// Creates a new empty `FileDoc`.
    pub fn new() -> FileDoc {
        FileDoc {
            functions: Vec::new(),
            path: PathBuf::new(),
        }
    }

    /// Creates a new `FileDoc` with the given `Path`.
    pub fn with_path(path: &Path) -> FileDoc {
        FileDoc {
            functions: Vec::new(),
            path: path.to_path_buf(),
        }
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

impl fmt::Display for FnDecl {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let generics = if self.generics.is_none() && self.lifetimes.is_none() {
            "".to_string()
        } else {
            format!("<{}>",
                    join_generics_and_lifetimes(&self.generics.as_ref().unwrap_or(&Vec::new()),
                                                &self.lifetimes.as_ref().unwrap_or(&Vec::new())))
        };
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

impl<'a> DocVisitor<'a> {
    fn add_item(&mut self, ident: String, doc: String, item: &ItemKind) -> Result<(), Error> {
        match *item {
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
                self.docs.functions.push(Doc::new(doc, function));
            }
            _ => println!("Not supported"),
        }
        Ok(())
    }
}

impl<'a> Visitor for DocVisitor<'a> {
    fn visit_item(&mut self, item: &ast::Item) {
        if let ast::Visibility::Public = item.vis {
            let ident = item.ident.to_string();
            let doc_string = item.attrs
                .iter()
                .filter_map(|attr| {
                    if attr.node.is_sugared_doc {
                        match self.codemap.span_to_snippet(attr.span) {
                            Ok(string) => {
                                let trim_chars: &[_] = &['/', '!'];
                                Some(string.trim_left_matches(trim_chars).trim().to_string())
                            },
                            Err(_) => None,
                        }
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>()
                .join("\n");
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
    let args = try!(args.iter()
        .map(|arg| {
            let ty = try!(codemap.span_to_snippet(arg.ty.span));
            let pat = try!(codemap.span_to_snippet(arg.pat.span));
            Ok(Variable::new(pat, ty))
        })
        .collect::<Result<_, Error>>());
    Ok(Some(args))
}

fn convert_generics(types: &[ast::TyParam],
                    codemap: &CodeMap)
                    -> Result<Option<Vec<Generic>>, Error> {
    if types.is_empty() {
        return Ok(None);
    }
    let gens: Vec<_> = try!(types.iter()
        .map(|ty| {
            let ident = ty.ident.to_string();
            let bounds = try!(convert_param_bounds(&ty.bounds, codemap));
            let generic = Generic {
                ident: ident,
                bounds: bounds,
            };
            Ok(generic)
        })
        .collect::<Result<_, Error>>());
    Ok(Some(gens))
}

fn convert_lifetimes(lifetimes: &[ast::LifetimeDef]) -> Option<Vec<Generic>> {
    if lifetimes.is_empty() {
        return None;
    }
    let lifetimes: Vec<_> = lifetimes.iter()
        .map(|life| Generic::from_ast_lifetime(&life.lifetime, &life.bounds))
        .collect();
    Some(lifetimes)
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
                    let lifetime = Generic::from_ast_lifetime(&region_pred.lifetime, &region_pred.bounds);
                    Ok(Bound::Lifetime(lifetime))
                }
                ast::WherePredicate::EqPredicate(_) => Err(Error::Unsupported),
            }
        })
        .collect::<Result<_, Error>>());
    Ok(Some(WhereClause::from(where_bounds)))
}

fn join_generics_and_lifetimes(generics: &[Generic], lifetimes: &[Generic]) -> String {
    let mut gens = generics.iter().map(|gen| gen.to_string()).collect();
    let mut clauses: Vec<_> = lifetimes.iter().map(|life| life.to_string()).collect();
    clauses.append(&mut gens);
    clauses.join(", ")
}