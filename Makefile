.PHONY: all build test sync

build:
	dune build

clean:
	dune clean

test:
	dune runtest bin --always-show-command-line

sync:
	git submodule sync
	git submodule update --remote