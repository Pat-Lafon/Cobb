.PHONY: all build test sync

build:
	dune build

test:
	dune runtest bin

sync:
	git submodule sync
	git submodule update --remote