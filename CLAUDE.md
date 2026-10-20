# Cobb — coverage-type program synthesizer

Cobb repairs test input generators using coverage types (underapproximation refinement types), building
on the Poirot type checker.

New behavior earns an end-to-end benchmark under `../integration_tests/` (see its `README.md §Adding a
benchmark`), not a `ppx_inline_test` / `ppx_expect` assertion on an internal helper. `make axioms` and
`make proof` shell out to `underapproximation_type/` rather than building here.

## Running Cobb

`meta-config.json`'s `prim_path` entries resolve against the CWD and are authored relative to
`underapproximation_type/` — running from `Cobb/` gives a misleading `data_type_decls.ml: No such file
or directory`. A run that dies with `A running dune instance has locked the build directory` (exit 101)
is a background editor holding `_build/.lock` through `dune ocaml-merlin` or `vsrocqtop`, not a
synthesis crash; use the prebuilt binary or quiesce the LSP. `scripts/runner.py` makes that `chdir`
for every script, so they take `../integration_tests/` paths directly.

## Project Architecture

`test/` is an empty `dune` stub — the real suite is `../integration_tests/`. The whole Z3 interface
lives in the `zutils/` submodule.

### Abduction depends on the typechecker, never the reverse

The arrow runs one way: `abduction → CoverageType`. Abduction is built *on* `term_type_infer` /
`value_type_infer` rather than being a leaf the checker calls down into, which is the easy wrong model.
`grep -rn abduction underapproximation_type/typing/` must come back empty.

## Configuration

`meta-config.json` is a string-keyed map of four typed sections, each owned by the library that reads
it: `zutils` (`zutils/config/zUtilsConfig.ml`), `typechecker`
(`underapproximation_type/typechecker_config/`), `abduction` (`abduction/abductionConfig.ml`), and
`cobb` (`bin/cobbConfig.ml`). The parse is strict — unknown fields within a section fail it — so read
those modules for the field rosters.

`log_tags` appears in two sections, each enabling only the trace channels its owning library emits:
`zutils.log_tags` for `zutils/config/zUtilsLog.ml` and `typechecker.log_tags` for
`underapproximation_type/typechecker_config/typecheckerLog.ml`. Those two modules name every legal tag;
a tag put in the wrong section is silently ignored, since the lists are unvalidated strings. `queries`
is the one channel both libraries write — zutils dumps the SMT query, the checker announces the
subtyping query that produced it — so it lives on the zutils list and one switch covers the pair.

Two shapes the loud parse error won't teach. `smt_encoding` is a ppx-encoded variant, so it is written
`["Axiom"]` or `["Both"]`, brackets and all; it defaults to `Axiom`, solving on the quantified
method-predicate axioms alone, while `["Both"]` additionally races the `define-fun-rec` body and
requires the program to define `let rec` measures.

`zutils.pred_extension_rules` defaults to `[]` and its absence is silent. Each rule must list its full
transitive closure; see `pred_extension` in `zutils/prop/axiom.ml`.
