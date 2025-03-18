# Cobb

One who searches underneath the bottom of consciousness: Inception(2010)

## Getting started

1. [Install opam](https://opam.ocaml.org/doc/Install.html)
2. [`opam switch create ./ --deps-only`](https://opam.ocamXl.org/blog/opam-local-switches/#A-reminder-about-switches)
3. Inside the `Cobb` directory run `eval $(opam env)`
4. Build with `dune build`
5. Run with `dune exec Cobb`

### Updating submodules

1. `git submodule sync`
2. `git submodule update --remote`

## Running benchmarks

`cd underapproximation_type/ && dune exec Cobb -- synthesis data/validation/sizedlist/ prog1.ml`

or

`python scripts/synth.py underapproximation_type/data/validation/sizedlist/`

## Typechecking a specific example

`dune exec -- bin/main.exe type-check meta-config.json data/issue/singleton_unique.ml`

## Memory profiling

`MEMTRACE=trace.ctf dune exec Cobb --no-buffer -- synthesis data/validation/sortedlist prog3.ml > test.log`

`memtrace-viewer trace.ctf`

## Getting the list of axioms as Coq

`dune exec -- bin/main.exe coq-axioms meta-config.json`

## Getting lines of code

`brew install cloc`
`cloc bin`

## Useful links for Development

### Axiom Profiler

- The actual tool:
<https://viperproject.github.io/axiom-profiler-2/>

- Some guidance on how to instrument and use:
<https://github.com/viperproject/axiom-profiler-2>
