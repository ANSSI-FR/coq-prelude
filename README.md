# `coq-prelude` [![Build Status](https://travis-ci.org/ANSSI-FR/coq-prelude.svg?branch=master)](https://travis-ci.org/ANSSI-FR/coq-prelude)

An opinionated Prelude for Coq, inspired by Haskell.

The pretty-printed source tree is [available
online.](https://anssi-fr.github.io/coq-prelude/toc.html)

## Getting Started

### Installing From Source

This project uses `dune` as its build system.

```bash
dune install
```

For convenience purpose, a `Makefile` is provided, with the default rule being a
call to `dune install`. Hence, one can just type:

```bash
make
```

One can also generate `coq-prelude` pretty-printed source tree thanks to `make`:

```bash
make html
```
