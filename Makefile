.PHONY: all build test sync

build:
	opam exec -- dune build

clean:
	dune clean

test:
	opam exec -- dune runtest bin --always-show-command-line

axioms:
	cd underapproximation_type && dune exec -- bin/main.exe coq-axioms meta-config.json > test.v

proof:
	cd underapproximation_type/data/validation/proofs && make

config:
	python3 scripts/check_config.py underapproximation_type/data/validation

subck:
	python3 scripts/subtype_check.py underapproximation_type/data/subtyping/

results:
	python3 scripts/results.py

sync:
	git submodule sync
	git submodule update --remote