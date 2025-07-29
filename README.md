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

`cd underapproximation_type/ && dune exec Cobb -- synthesis data/validation/sizedlist/prog1.ml`

or

`python scripts/synth.py underapproximation_type/data/validation/sizedlist/`

## Running excess benchmarks and comparing results

### What are excess benchmarks?

Excess benchmarks test how a most precise set of components affect synthesis
performance. Each `_excess` directory contains fewer components than its base
counterpart. Why is it called excess if there are fewer components? Originally
this was flipped, but we decided to add more components to the main evaluation to
create the contrast instead. I never updated the names

### Running the benchmarks

1. **Run base benchmarks** (if not already done)

2. **Run excess benchmarks**:

   ```bash
   python scripts/synth.py underapproximation_type/data/validation/sizedlist_excess/
   python scripts/synth.py underapproximation_type/data/validation/uniquelist_excess/
   python scripts/synth.py underapproximation_type/data/validation/sortedlist_excess/
   python scripts/synth.py underapproximation_type/data/validation/duplicatelist_excess/
   python scripts/synth.py underapproximation_type/data/validation/even_list_excess/
   python scripts/synth.py underapproximation_type/data/validation/complete_tree_excess/
   python scripts/synth.py underapproximation_type/data/validation/depthtree_excess/
   python scripts/synth.py underapproximation_type/data/validation/depth_bst_excess/
   ```

### Comparing results

Compare performance differences:

```bash
python scripts/excess_results.py
```

This generates CSV comparison files in the `data/` folder.

## Running imprecise benchmarks

### What are imprecise benchmarks?

Imprecise benchmarks test synthesis process when missing a key component. Each
`_imprecise` directory contains programs with a hand selected list of components
from the excess benchmarks minus one crucial component

### Running the imprecise benchmarks

**Run imprecise benchmarks**:

```bash
python scripts/synth_imprecise.py underapproximation_type/data/validation/sizedlist_imprecise/
python scripts/synth_imprecise.py underapproximation_type/data/validation/uniquelist_imprecise/
python scripts/synth_imprecise.py underapproximation_type/data/validation/sortedlist_imprecise/
python scripts/synth_imprecise.py underapproximation_type/data/validation/duplicatelist_imprecise/
python scripts/synth_imprecise.py underapproximation_type/data/validation/even_list_imprecise/
python scripts/synth_imprecise.py underapproximation_type/data/validation/complete_tree_imprecise/
python scripts/synth_imprecise.py underapproximation_type/data/validation/depthtree_imprecise/
python scripts/synth_imprecise.py underapproximation_type/data/validation/depth_bst_imprecise/
python scripts/synth_imprecise.py underapproximation_type/data/validation/rbtree_imprecise/
```

## Typechecking a specific example

`dune exec -- bin/main.exe type-check meta-config.json data/issue/singleton_unique.ml`

## Getting the list of axioms as Coq

`dune exec -- bin/main.exe coq-axioms meta-config.json`

## Getting lines of code

`brew install cloc`
`cloc bin`

## Adding a new function

Often this is hit with an error message like `(len: none) =? none`. Add the type
signature in the files pointed to by the `normal_typing` and `coverage_typing`
fields in your `meta-config.json` file.

## Useful links for Development

### Axiom Profiler

- The actual tool:
<https://viperproject.github.io/axiom-profiler-2/>

- Some guidance on how to instrument and use:
<https://github.com/viperproject/axiom-profiler-2>
