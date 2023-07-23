# `argsyn`, an Argument Parser for GNU-style Syntax

This crate provides a complete implementation of GNU-style argument parsing as described at \
<https://www.gnu.org/software/libc/manual/html_node/Argument-Syntax.html>

Arguments are converted into basics, flags, pairs, and a few other types according to the GNU-style.
Here is a visual example of how a sequence of arguments is converted with `"xy"` specified as short pairs:

```text
$ program arg1 -abcx12 -y 3 --long --key=value - arg2 -- -kh --ignore
  |       |     ||||    |     |      |         | |    |  |   |
  Basic(program)||||    |     |      |         | |    |  Basic(-kh)
          Basic(arg1)   |     |      |         | |    |      Basic(--ignore)
                Flag(a) |     |      |         | |    |
                 Flag(b)|     |      |         | |    |
                  Flag(c)     |      |         | |    |
                   Pair(x,12) |      |         | |    |
                        Pair(y,3)    |         | |    |
                              Flag(long)       | |    |
                                     Pair(key,value)  |
                                               Stdin  |
                                                 Basic(arg2)
                                                      Done
```

In Rust, to print all arguments parsed, it is as simple as:

```rust
for opt in std::env::args().opts("xy") {
  println!("{:?}", opt.simplify());
}
```
