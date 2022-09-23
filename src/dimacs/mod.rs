// Copyright (c) 2015-2021 Frank Fischer <frank-fischer@shadow-soft.de>
//
// This program is free software: you can redistribute it and/or
// modify it under the terms of the GNU General Public License as
// published by the Free Software Foundation, either version 3 of the
// License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful, but
// WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
// General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see  <http://www.gnu.org/licenses/>
//

//! Reading files in DIMACS format.

pub mod max;
pub mod min;

pub mod graph;
pub use self::graph::read as read_graph;

use std::error;
use std::fmt;
use std::io::{self, BufRead, BufReader, Read};
use std::str::{FromStr, SplitWhitespace};

/// Error when reading a file in DIMACS format.
#[derive(Debug)]
pub enum Error {
    Io(io::Error),
    Format { line: usize, msg: String },
    Data { line: usize, msg: String },
}

impl From<io::Error> for Error {
    fn from(err: io::Error) -> Self {
        Error::Io(err)
    }
}

impl fmt::Display for Error {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> std::result::Result<(), fmt::Error> {
        use self::Error::*;
        match self {
            Io(err) => err.fmt(fmt),
            Format { line, msg } => write!(fmt, "Format error on line {}: {}", line, msg),
            Data { line, msg } => write!(fmt, "Data error on line {}: {}", line, msg),
        }
    }
}

impl error::Error for Error {
    fn cause(&self) -> Option<&dyn error::Error> {
        match self {
            Error::Io(err) => Some(err),
            _ => None,
        }
    }
}

pub type Result<T> = std::result::Result<T, Error>;

pub struct DimacsReader<R: Read> {
    io: BufReader<R>,

    line: String,
    line_number: usize,
}

impl<R: Read> DimacsReader<R> {
    pub fn new(reader: R) -> Self {
        DimacsReader {
            io: BufReader::new(reader),
            line: String::new(),
            line_number: 0,
        }
    }

    fn read_line(&mut self) -> Result<Option<Tokens>> {
        let line = &mut self.line;
        loop {
            line.clear();
            if self.io.read_line(line)? == 0 {
                return Ok(None);
            }

            self.line_number += 1;
            let mut it = line.char_indices();
            while let Some((i, c)) = it.next() {
                if char::is_whitespace(c) {
                    continue;
                }
                if c == 'c' || c == '\n' {
                    break;
                }
                return Ok(Some(Tokens {
                    it: line[i..].split_whitespace(),
                    line: self.line_number,
                }));
            }
        }
    }

    // Expect a line with the given descriptor.
    //
    // If the next line does not have this descriptor, an error is returned.
    // Otherwise the *remaining* tokens are returned.
    fn expect_line(&mut self, descriptor: char) -> Result<Tokens> {
        let line_number = self.line_number;
        let mut toks = self.read_line()?.ok_or_else(|| Error::Format {
            line: line_number,
            msg: format!("unexpected end of file, expected '{}' line", descriptor),
        })?;
        match toks.next() {
            Some(d) if d.len() == 1 && d.starts_with(descriptor) => Ok(toks),
            Some(d) => Err(Error::Format {
                line: line_number,
                msg: format!("unexpected line, expected '{}', got '{}'", descriptor, d),
            }),
            None => Err(Error::Format {
                line: line_number,
                msg: "unexpected empty line".to_string(),
            }),
        }
    }

    // Read the next line with one of the given descriptors.
    //
    // If the next line does not have this descriptor, `Ok(None)`.
    // Otherwise the descriptor and the *remaining* tokens are returned.
    fn read_one_line_of(&mut self, descriptors: &[&str]) -> Result<Option<(&str, Tokens)>> {
        let line_number = self.line_number;
        if let Some(mut toks) = self.read_line()? {
            match toks.next() {
                Some(d) if descriptors.iter().find(|&desc| d.starts_with(desc)).is_some() => Ok(Some((d, toks))),
                Some(d) => Err(Error::Format {
                    line: line_number,
                    msg: format!(
                        "unexpected line, expected on of '{}', got '{}'",
                        descriptors.join("', '"),
                        d
                    ),
                }),
                None => Err(Error::Format {
                    line: line_number,
                    msg: "unexpected empty line".to_string(),
                }),
            }
        } else {
            Ok(None)
        }
    }
}

/// Iterates over the tokens in a line.
pub struct Tokens<'a> {
    it: SplitWhitespace<'a>,
    pub line: usize,
}

impl<'a> Iterator for Tokens<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<&'a str> {
        self.it.next()
    }
}

impl<'a> Tokens<'a> {
    /// Return an error if the next token is not the given token.
    pub fn expect(&mut self, tok: &str) -> Result<()> {
        let nxt = self.str()?;
        if nxt == tok {
            Ok(())
        } else {
            Err(Error::Format {
                line: self.line,
                msg: format!("expected '{}', got '{}", tok, nxt),
            })
        }
    }

    /// Return an error if the next token is not the given token list.
    pub fn expect_one_of(&mut self, toks: &[&str]) -> Result<()> {
        let nxt = self.str()?;
        if toks.iter().find(|&&tok| tok == nxt).is_some() {
            Ok(())
        } else {
            Err(Error::Format {
                line: self.line,
                msg: format!("expected one of '{}', got '{}", toks.join("', '"), nxt),
            })
        }
    }

    /// Returns the next token as `&str`.
    pub fn str(&mut self) -> Result<&'a str> {
        self.it.next().ok_or_else(|| Error::Format {
            line: self.line,
            msg: "expected token".to_string(),
        })
    }

    /// Returns the next token converted to a number.
    pub fn number<T>(&mut self) -> Result<T>
    where
        T: FromStr,
        T::Err: fmt::Display,
    {
        self.it
            .next()
            .ok_or_else(|| Error::Format {
                line: self.line,
                msg: "expected number".to_string(),
            })?
            .parse()
            .or_else(|e| {
                Err(Error::Format {
                    line: self.line,
                    msg: format!("{}", e),
                })
            })
    }

    /// Ensures that there is no next token.
    pub fn end(&mut self) -> Result<()> {
        if let Some(s) = self.it.next() {
            Err(Error::Format {
                line: self.line,
                msg: format!("unexpected token at end of line: {}", s),
            })
        } else {
            Ok(())
        }
    }
}

/// Read a DIMACS file.
///
/// - `fin` is the buffered reader with the file content
/// - `f` is callback called once for each non-comment line with
///   `(c,toks)`, where `c` is the descripter of the line and `toks`
///   an iterator over the tokens
pub(self) fn read_dimacs<R, F>(fin: &mut R, f: &mut F) -> Result<()>
where
    R: io::BufRead,
    F: FnMut(char, &mut Tokens) -> Result<()>,
{
    let mut nline = 0;
    let mut line = String::new();

    while {
        line.clear();
        fin.read_line(&mut line)
    }? > 0
    {
        nline += 1;
        let mut it = line.chars();
        while let Some(c) = it.next() {
            match c {
                _ if char::is_whitespace(c) => continue,
                'c' | '\n' => break,
                _ => {
                    let mut tok = Tokens {
                        it: it.as_str().split_whitespace(),
                        line: nline,
                    };
                    f(c, &mut tok)?;
                    break;
                }
            }
        }
    }

    Ok(())
}
