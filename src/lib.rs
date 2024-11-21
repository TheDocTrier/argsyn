//! # Argument Syntax
//!
//! This crate provides a complete implementation of the argument parsing algorithm described in \
//! <https://www.gnu.org/software/libc/manual/html_node/Argument-Syntax.html>
//!
//! Arguments are converted into basics, flags, pairs, and a few other types according to the GNU-style.
//! Here is a visual example of how a sequence of arguments is converted with `"xy"` specified as short pairs:
//!
//! ```text
//! $ program arg1 -abcx12 -y 3 --long --key=value - arg2 -- -kh --ignore
//!   |       |     ||||    |     |      |         | |    |  |   |
//!   Basic(program)||||    |     |      |         | |    |  Basic(-kh)
//!           Basic(arg1)   |     |      |         | |    |      Basic(--ignore)
//!                 Flag(a) |     |      |         | |    |
//!                  Flag(b)|     |      |         | |    |
//!                   Flag(c)     |      |         | |    |
//!                    Pair(x,12) |      |         | |    |
//!                         Pair(y,3)    |         | |    |
//!                               Flag(long)       | |    |
//!                                      Pair(key,value)  |
//!                                                Stdin  |
//!                                                  Basic(arg2)
//!                                                       Done
//! ```
//!
//! The easiest way to use this crate is with [`ArgsExt::opts`] and [`Opt::simplify`].
//! The extension trait is implemented for every [`Iterator`] which returns [`String`].
//! This includes [`std::env::Args`].
//! For example:
//!
//! ```
//! use argsyn::ArgsExt;
//!
//! fn main() {
//!   for opt in std::env::args().opts("xy").unwrap() {
//!     println!("{:?}", opt.simplify());
//!   }
//! }
//! ```

use ref_cast::RefCast;

use core::str;
use std::collections::VecDeque;
use std::fmt::{Debug, Display};

/// Converts [`Iterator`] of [`String`]s into an iterator of [`Opt`]s.
pub trait ArgsExt: IntoIterator<Item = String> + Sized {
    /// Parses an [`Iterator`] using [`Parser`].
    ///
    /// Returns `None` if `short_pairs` has non-alphanumeric characters.
    ///
    /// # Examples
    ///
    /// ```text
    /// $ program arg1 -abcx12 -y 3 --long --key=value - arg2 -- -kh --ignore
    /// ```
    ///
    /// The following code simulates parsing of the command above:
    ///
    /// ```
    /// use argsyn::ArgsExt;
    ///
    /// let cmd = "program arg1 -abcx12 -y 3 --long --key=value - arg2 -- -kh --ignore";
    ///
    /// let args = cmd
    ///   .split_ascii_whitespace()
    ///   .into_iter()
    ///   .map(|s| s.to_string());
    ///
    /// for opt in args.opts("xy").unwrap() {
    ///   println!("{:?}", opt);
    /// }
    /// ```
    ///
    /// Running the above code produces the following output:
    ///
    /// ```text
    /// NonOption("program")
    /// NonOption("arg1")
    /// Short("a")
    /// Short("b")
    /// Short("c")
    /// ShortPair("x", "12")
    /// ShortPair("y", "3")
    /// Long("long")
    /// LongPair("key", "value")
    /// Dash
    /// NonOption("arg2")
    /// Terminator
    /// NonOption("-kh")
    /// NonOption("--ignore")
    /// ```
    fn opts(self, short_pairs: &str) -> Result<Parser, NonAlphaNumError> {
        Parser::new(self.into_iter().collect(), short_pairs)
    }
}

impl<T> ArgsExt for T where T: Iterator<Item = String> {}

/// Alternative labeling of [`Opt`] which is easier to use in `match` statements.
///
/// For each variant below, we describe which [`Opt`] variant that it is derived from.
///
/// # Examples
///
/// Here we use [`Opt::simplify`] to perform the borrowing:
///
/// ```
/// # use argsyn::{SimpleOpt::Flag, Opt::Long};
/// let x = Long("verbose".to_string());
///
/// match x.simplify() {
///   Flag("v" | "verbose") => println!("Verbose option captured!"),
///   _ => panic!(),
/// }
/// ```
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum SimpleOpt<'a> {
    /// [`NonOption`]
    Basic(&'a str),
    /// [`Dash`]
    Stdin,
    /// [`Short`] or [`Long`]
    Flag(&'a str),
    /// [`ShortPair`] or [`LongPair`]
    Pair(&'a str, &'a str),
    /// [`Terminator`]
    Done,
    /// All other [`Opt`] variants not covered
    Other(&'a Opt),
}

use SimpleOpt::*;

/// All possible options/non-options which can be parsed from arguments
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Opt {
    /// `file` (plain non-option argument)
    NonOption(String),
    /// `-` (just a dash; usually for stdin)
    Dash,
    /// `-x` alphanumeric character "x"
    Short(String),
    /// `-xBAR` or `-x BAR`
    ShortPair(String, String),
    /// `-x <EOF>` (expected pair; found EOF)
    ShortIncomplete(String),
    /// `--example`
    Long(String),
    /// `--example=[value]`
    LongPair(String, String),
    /// `--` (forces all later arguments to be non-options)
    Terminator,
}

use Opt::*;

impl Opt {
    /// Converts an [`Opt`] into a [`SimpleOpt`].
    ///
    /// See [`SimpleOpt`] variants for a description of the variant conversion.
    ///
    /// # Examples
    ///
    /// Consider the following command:
    ///
    /// ```text
    /// $ program arg1 -abcx12 -y 3 --long --key=value - arg2 -- -kh --ignore
    /// ```
    ///
    /// The following code simulates parsing of the command above:
    ///
    /// ```
    /// use argsyn::ArgsExt;
    ///
    /// let cmd = "program arg1 -abcx12 -y 3 --long --key=value - arg2 -- -kh --ignore";
    ///
    /// let args = cmd
    ///   .split_ascii_whitespace()
    ///   .into_iter()
    ///   .map(|s| s.to_string());
    ///
    /// for opt in args.opts("xy").unwrap() {
    ///   println!("{:?}", opt.simplify());
    /// }
    /// ```
    ///
    /// Running the above code produces the following output:
    ///
    /// ```text
    /// Basic("program")
    /// Basic("arg1")
    /// Flag("a")
    /// Flag("b")
    /// Flag("c")
    /// Pair("x", "12")
    /// Pair("y", "3")
    /// Flag("long")
    /// Pair("key", "value")
    /// Stdin
    /// Basic("arg2")
    /// Done
    /// Basic("-kh")
    /// Basic("--ignore")
    /// ```
    ///
    /// See [`ArgsExt::opts`] for the same example but without simplification.
    pub fn simplify(&self) -> SimpleOpt {
        match self {
            NonOption(s) => Basic(s),
            Dash => Stdin,
            Short(f) | Long(f) => Flag(f),
            ShortPair(k, v) | LongPair(k, v) => Pair(k, v),
            Terminator => Done,
            _ => Other(self),
        }
    }
}

/// Flexible parser which converts arguments into [`Opt`]s
#[non_exhaustive]
#[derive(Debug)]
pub struct Parser {
    /// Underlying [`Iterator`] of [`String`]s
    pub args: VecDeque<String>,

    /// All shorts which will expect a value after them
    pub short_pairs: Vec<AlphaNum>,

    /// True causes all arguments to be parsed as [`NonOption`]
    ///
    /// This field is set to true after encountering [`Terminator`].
    pub terminated: bool,
}

impl Parser {
    /// Creates a new parser with the shorts expecting a value given by `short_pairs`
    ///
    /// Using a custom iterator can allow for complex parsing behaviors such as `-T <file>` from GNU tar.
    ///
    /// # Examples
    ///
    /// ```
    /// use argsyn::Parser;
    ///
    /// let args = vec!["a".into(), "-bc".into(), "val".into()];
    /// let parser = Parser::new(args.into(), "c");
    /// ```
    pub fn new(args: VecDeque<String>, short_pairs: &str) -> Result<Self, NonAlphaNumError> {
        Ok(Parser {
            args,
            short_pairs: alpha_num_from_bytes(short_pairs.as_bytes())?,
            terminated: false,
        })
    }

    /// Parses a single option/non-option
    fn parse_opt(&mut self) -> Option<Opt> {
        let next_arg = self.args.pop_front()?;
        if self.terminated {
            // option parsing has been terminated
            NonOption(next_arg).into()
        } else if let Some(long_kv) = next_arg.strip_prefix("--") {
            // --[key=value]
            if long_kv == "" {
                // -- (signals termination of argument parsing)
                self.terminated = true;
                Terminator.into()
            } else if let Some((key, value)) = long_kv.split_once('=') {
                // --key=value
                LongPair(key.to_owned(), value.to_owned()).into()
            } else {
                // --long
                Long(long_kv.to_owned()).into()
            }
        } else if let Some(shorts_str) = next_arg.strip_prefix('-') {
            // -[ashorts]
            if let Some((a, other_str)) = split_first_alpha_num(shorts_str) {
                let s_a = a.to_string();

                // -a[shorts]
                // Note, `shorts_chars.as_str()` is the leftover shorts
                if self.short_pairs.contains(&a) {
                    // -a[BAR]
                    if other_str.is_empty() {
                        // -a [BAR]
                        if let Some(value) = self.args.pop_front() {
                            // -a BAR
                            ShortPair(s_a, value).into()
                        } else {
                            // -a <EOF>
                            ShortIncomplete(s_a).into()
                        }
                    } else {
                        // -aBAR
                        ShortPair(s_a, other_str.to_owned()).into()
                    }
                } else {
                    // -ashorts
                    // Push the leftover shorts back into the arguments
                    self.args.push_front(format!("-{}", other_str));
                    Short(s_a).into()
                }
            } else {
                // -
                Dash.into()
            }
        } else {
            // basic argument (guaranteed to exist by next_arg)
            NonOption(next_arg).into()
        }
    }
}

impl Iterator for Parser {
    type Item = Opt;

    fn next(&mut self) -> Option<Self::Item> {
        self.parse_opt()
    }
}

// UTILS

/// An error returned by [`Parser::new`] when a non-alphanumeric short pair is given.
#[derive(Debug)]
pub struct NonAlphaNumError(pub u8);

impl Display for NonAlphaNumError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "character {:x?} is not alphanumeric", self.0)
    }
}

impl std::error::Error for NonAlphaNumError {}

fn split_first_alpha_num(s: &str) -> Option<(AlphaNum, &str)> {
    let (a, ss) = s.split_at_checked(1)?;
    let a = AlphaNum::new(a.bytes().next()?).ok()?;
    Some((a, ss))
}

/// Store an alpha numeric byte which can be used as a short option
#[derive(Clone, Copy, PartialEq, Eq, RefCast)]
#[repr(transparent)]
pub struct AlphaNum(u8);

impl AlphaNum {
    /// Check that `a` can be used as a short
    pub fn new(a: u8) -> Result<Self, NonAlphaNumError> {
        match a {
            b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9' => Ok(AlphaNum(a)),
            x => Err(NonAlphaNumError(x)),
        }
    }

    pub fn as_str(&self) -> &str {
        self.as_ref()
    }
}

impl Debug for AlphaNum {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "b'{}'", self.0.escape_ascii())
    }
}

impl AsRef<str> for AlphaNum {
    fn as_ref(&self) -> &str {
        std::str::from_utf8(std::slice::from_ref(&self.0))
            .expect("valid alpha numeric should be checked at creation")
    }
}

impl Display for AlphaNum {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_ref())
    }
}

fn alpha_num_from_bytes(b: &[u8]) -> Result<Vec<AlphaNum>, NonAlphaNumError> {
    // Eventually replace with `try_collect`
    b.into_iter()
        .map(|a| AlphaNum::new(*a))
        .try_fold(vec![], |mut v, ra| ra.map(|a| v.push(a)).and(Ok(v)))
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn integrate() {
        let s = "program arg1 -abcx12 -y 3 --long --key=value - arg2 -- -kh --ignore";
        let v = s.split(' ').map(|a| a.to_string()).collect::<Vec<_>>();

        let parser = Parser::new(v.into(), "xy").unwrap();
        let parsed = parser.into_iter().collect::<Vec<_>>();
        let simple_parsed = parsed.iter().map(|o| o.simplify()).collect::<Vec<_>>();

        use SimpleOpt::*;
        assert_eq!(
            simple_parsed,
            vec![
                Basic("program"),
                Basic("arg1"),
                Flag("a"),
                Flag("b"),
                Flag("c"),
                Pair("x", "12"),
                Pair("y", "3"),
                Flag("long"),
                Pair("key", "value"),
                Stdin,
                Basic("arg2"),
                Done,
                Basic("-kh"),
                Basic("--ignore")
            ]
        );
    }
}
