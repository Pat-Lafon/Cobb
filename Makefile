test:
	dune runtest

sync:
	git submodule sync
	git submodule update --remote