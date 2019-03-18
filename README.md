# `coq-prelude` [![Build Status](https://travis-ci.org/ANSSI-FR/coq-prelude.svg?branch=master)](https://travis-ci.org/ANSSI-FR/coq-prelude)

An opinionated Prelude for Coq, inspired by Haskell.

The pretty-printed source tree is [available
online.](https://anssi-fr.github.io/coq-prelude/toc.html)

## Getting Started

### Installing From Source

To install it from source, just use the `Makefile` provided with the source tree:

```bash
sudo make install
```

To uninstall it, you can just delete the directory `Prelude` in
`/usr/lib/coq/user-contrib`, that is:

```bash
sudo rm -r /usr/lib/coq/user-contrib/Prelude
```
