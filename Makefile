.PHONY: all build test sync proof config subck results

build:
	opam exec -- dune build

clean:
	dune clean

test:
	opam exec -- dune runtest bin --always-show-command-line

proof:
	cd underapproximation_type/formalization && make

config:
	python3 scripts/check_config.py ../integration_tests

subck:
	python3 scripts/subtype_check.py ../integration_tests

results:
	uv run scripts/results.py

sync:
	git submodule sync
	git submodule update --remote