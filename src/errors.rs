use std::error;
use std::fmt;

use syntex_pos::SpanSnippetError;

#[derive(Debug, PartialEq)]
pub enum Error {
    Snippet(SpanSnippetError),
    InvalidInput,
    Unsupported,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::Snippet(_) => write!(f, "failed to read snippet"),
            Error::InvalidInput => write!(f, "invalid input"),
            Error::Unsupported => write!(f, "unsupported"),
        }
    }
}

impl error::Error for Error {
    fn description(&self) -> &str {
        match *self {
            Error::Snippet(_) => "Failed to read code snippet",
            Error::InvalidInput => "Invalid input",
            Error::Unsupported => "Unsupported",
        }
    }
}

impl From<SpanSnippetError> for Error {
    fn from(err: SpanSnippetError) -> Error {
        Error::Snippet(err)
    }
}
