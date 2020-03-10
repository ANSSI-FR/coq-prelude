.PHONY: build html

build:
	dune build @install

install: build
	dune install

html: build
	./configure.sh
	make -f Makefile.coq html
