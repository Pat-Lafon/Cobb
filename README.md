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

The corpus is `../integration_tests/<bench>/`. Cobb expects `underapproximation_type/` as its working
directory, and `meta-config.json`'s paths are authored relative to it.

`cd underapproximation_type/ && dune exec Cobb -- synthesis ../../integration_tests/sizedlist/sizedlist_gen_synth_prog1.ml`

`python3 scripts/synth.py ../integration_tests/sizedlist` synthesizes every `progN.ml` under a
directory (`abduce.py` likewise abduces). `../totem_runner/` drives the whole pipeline.

## Collecting results

Each synthesis run writes `<prog>.ml.result.csv` beside its program. `make results` gathers them into
`data/benchmark_results.tex`; `uv run scripts/chart_results.py` plots the sketch rows to `charts/`.
Their dependencies live in `scripts/pyproject.toml`; `uv sync --project scripts` builds the
`scripts/.venv` the editor's Python interpreter points at. A row with blank fields is a run that never finished, and the chart refuses
it by name.

`python3 scripts/frequify.py <out-dir>` rewrites each `.syn` into a frequency-weighted generator under
`<out-dir>/<bench>/progN_syn.ml`.

## Typechecking a specific example

`cd underapproximation_type/ && dune exec -- bin/main.exe type-check -config ../../integration_tests/sizedlist/meta-config.json ../../integration_tests/sizedlist/sizedlist_gen.ml`

## Getting lines of code

`brew install cloc`
`cloc bin`

## Adding a new function

Often this is hit with an error message like `(len: none) =? none`. Add the type
signature in the files pointed to by the `normal_typing` and `coverage_typing`
fields in your `meta-config.json` file.

A measure defined as `let rec` in `program.ml` is the exception: its relational signature is derived
automatically, so adding a `val` for one to `normal_typing` is wrong even though the error asks for it.

## Useful links for Development

### Axiom Profiler

- The actual tool:
<https://viperproject.github.io/axiom-profiler-2/>

- Some guidance on how to instrument and use:
<https://github.com/viperproject/axiom-profiler-2>
