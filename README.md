# `coq-prelude` [![Build Status](https://travis-ci.org/ANSSI-FR/coq-prelude.svg?branch=master)](https://travis-ci.org/ANSSI-FR/coq-prelude)

Originally inspired by the Haskell standard library (Prelude),
`coq-prelude` now strives to be a convenient addition to the Coq
standard library in order to ease *software development* (as opposed
to theorem proving).

The pretty-printed source tree is [available
online.](https://anssi-fr.github.io/coq-prelude/toc.html)

Here are some features provided by this library:

- `Equality` typeclass: to be used in place of built-in Leibniz
  equality
- Alternative string types: `text` (unicode text) and `bytes` (raw
  list of `byte`) whose string notations support escape characters
  such as `\n` or `\t`.
- `Monad` typeclasses hierarchy, with notations inspired by both the
  Haskell do-notation and the OCaml monadic operators

## Getting Started

### Installing From Source

This project uses `dune` as its build system.

```bash
dune build
```

For convenience purpose, a `Makefile` is provided, with the default rule being a
call to `dune build`. Hence, one can just type:

```bash
make
```

One can also generate `coq-prelude` pretty-printed source tree thanks to `make`:

```bash
make html
```
