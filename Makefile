.PHONY: build html

build:
	dune build

html: build
	./configure.sh
	make -f Makefile.coq html
