.PHONY: all build test sync

build:
	opam exec -- dune build

clean:
	dune clean

test:
	opam exec -- dune runtest bin --always-show-command-line

sync:
	git submodule sync
	git submodule update --remote