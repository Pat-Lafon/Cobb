.PHONY: all build test abduce sync proof config subck results

build:
	opam exec -- dune build

clean:
	dune clean

test:
	opam exec -- dune runtest bin --always-show-command-line

abduce: build
	@fail=0; for f in ../integration_tests/*/*_gen_synth_prog*.ml; do \
	  if (cd underapproximation_type && ../_build/default/bin/main.exe abduction ../$$f >/dev/null 2>abduce.err); then \
	    echo "ok   $$f"; \
	  else echo "FAIL $$f"; tail -n 5 underapproximation_type/abduce.err; fail=1; fi; \
	done; rm -f underapproximation_type/abduce.err; exit $$fail

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