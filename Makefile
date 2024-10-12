.PHONY: all build test sync

build:
	opam exec -- dune build

clean:
	dune clean

test:
	opam exec -- dune runtest bin --always-show-command-line

proof:
	cd underapproximation_type/data/validation/proofs && make

sync:
	git submodule sync
	git submodule update --remote