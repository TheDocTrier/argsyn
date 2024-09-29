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

use std::collections::{HashSet, VecDeque};
use std::str;

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
    fn opts(self, short_pairs: &str) -> Option<Parser> {
        Parser::new(self.into_iter().collect(), short_pairs.chars().collect())
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
    pub short_pairs: HashSet<char>,

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
    /// # let args = vec!["a", "-bc", "val"].into_iter().map(|s| s.to_string());
    /// use argsyn::Parser;
    ///
    /// let parser = Parser::new(args.collect(), "c".chars().collect());
    /// ```
    pub fn new(args: VecDeque<String>, short_pairs: HashSet<char>) -> Option<Self> {
        // Check short_pairs only contains alphanumeric characters
        short_pairs
            .iter()
            .all(|&a| is_alpha_num(a))
            .then_some(Parser {
                args,
                short_pairs,
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
                // -a[shorts]
                // Note, `shorts_chars.as_str()` is the leftover shorts
                if self.short_pairs.contains(&a) {
                    // -a[BAR]
                    if other_str.is_empty() {
                        // -a [BAR]
                        if let Some(value) = self.args.pop_front() {
                            // -a BAR
                            ShortPair(a.to_string(), value).into()
                        } else {
                            // -a <EOF>
                            ShortIncomplete(a.to_string()).into()
                        }
                    } else {
                        // -aBAR
                        ShortPair(a.to_string(), other_str.to_owned()).into()
                    }
                } else {
                    // -ashorts
                    // Push the leftover shorts back into the arguments
                    self.args.push_front(format!("-{}", other_str));
                    Short(a.to_string()).into()
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

fn is_alpha_num(a: char) -> bool {
    match a {
        'a'..='z' | 'A'..='Z' | '0'..='9' => true,
        _ => false,
    }
}

fn split_first_alpha_num(s: &str) -> Option<(char, &str)> {
    let mut c = s.chars();
    let a = c.next()?;
    is_alpha_num(a).then_some((a, c.as_str()))
}
