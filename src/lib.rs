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
//!   for opt in std::env::args().opts("xy") {
//!     println!("{:?}", opt.simplify());
//!   }
//! }
//! ```

/// Converts [`Iterator`] of [`String`]s into an iterator of [`Opt`]s.
pub trait ArgsExt: Iterator<Item = String> + Sized {
  /// Parses an [`Iterator`] using [`Parser`].
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
  /// for opt in args.opts("xy") {
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
  fn opts<S>(self, short_pairs: S) -> Parser<Self>
  where
    S: Into<String>,
  {
    Parser::new(self, short_pairs)
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
  /// `-x`
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
  /// for opt in args.opts("xy") {
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
      Short(s) | Long(s) => Flag(s),
      ShortPair(k, v) | LongPair(k, v) => Pair(k, v),
      Terminator => Done,
      _ => Other(self),
    }
  }
}

/// Flexible parser which converts arguments into [`Opt`]s
#[non_exhaustive]
#[derive(Debug)]
pub struct Parser<I: Iterator<Item = String>> {
  /// Underlying [`Iterator`] of [`String`]s
  pub args: I,

  /// All shorts which were part a combined short and have not finished being processed
  ///
  /// For example, the argument `-abc` may first produce `Short("a")`.
  /// At that point, `working_shorts` will contain `"bc"`.
  /// Then, the parser may produce `Short("b")`.
  /// At that point, `working_shorts` will contain `"c"`.
  pub working_shorts: Option<String>,

  /// All shorts which will expect a value after them
  pub short_pairs: String,

  /// True causes all arguments to be parsed as [`NonOption`]
  ///
  /// This field is set to true after encountering [`Terminator`].
  pub terminated: bool,
}

// TODO: generalize to <A: Into<String>, I: Iterator<Item = A>>
// this would allow an iterator of &str
impl<I: Iterator<Item = String>> Parser<I> {
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
  /// let parser = Parser::new(args, "c");
  /// ```
  pub fn new<S: Into<String>>(args: I, short_pairs: S) -> Self {
    Parser {
      args,
      working_shorts: None,
      short_pairs: short_pairs.into(),
      terminated: false,
    }
  }

  /// Parses a single option/non-option
  fn parse_opt(&mut self) -> Option<Opt> {
    if self.terminated {
      // option parsing has been terminated
      NonOption(self.args.next()?).into()
    } else if let Some(opt) = self.parse_working_shorts() {
      // use up one of the working shorts
      opt.into()
    } else if let Some(raw_opt) = self.args.next() {
      // found next argument
      if let Some(long_kv) = raw_opt.strip_prefix("--") {
        if long_kv == "" {
          // -- (signals termination of argument parsing)
          self.terminated = true;
          Terminator.into()
        } else if let Some((key, value)) = long_kv.split_once("=") {
          // --example=[value]
          LongPair(key.to_string(), value.to_string()).into()
        } else {
          // --example
          Long(long_kv.to_string()).into()
        }
      } else if let Some(shorts) = raw_opt.strip_prefix("-") {
        // -abc
        self.working_shorts = shorts.to_string().into();
        self.parse_working_shorts()
      } else {
        // file (plain argument)
        NonOption(raw_opt).into()
      }
    } else {
      // end of arguments
      None
    }
  }

  /// Attempts to parse and reduce `working_shorts`
  fn parse_working_shorts(&mut self) -> Option<Opt> {
    if let Some(working) = &self.working_shorts {
      // parse shorts from previously combined shorts
      if working.is_empty() {
        // - (just a dash; usually for stdin)
        self.working_shorts = None;
        Dash.into()
      } else {
        let old_shorts = working.clone();
        let (c, r) = old_shorts.split_at(1);
        self.working_shorts = if r.is_empty() {
          None
        } else {
          r.to_string().into()
        };

        if self.short_pairs.contains(c) {
          // -x <VALUE>
          if r.is_empty() {
            if let Some(value) = self.args.next() {
              // -x BAR (with space)
              ShortPair(c.to_string(), value).into()
            } else {
              // -x <EOF> (missing argument)
              ShortIncomplete(c.to_string()).into()
            }
          } else {
            // -xBAR (with no space)
            self.working_shorts = None;
            ShortPair(c.to_string(), r.to_string()).into()
          }
        } else {
          Short(c.to_string()).into()
        }
      }
    } else {
      None
    }
  }
}

impl<I: Iterator<Item = String>> Iterator for Parser<I> {
  type Item = Opt;

  fn next(&mut self) -> Option<Self::Item> {
    self.parse_opt()
  }
}
