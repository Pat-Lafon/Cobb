# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Cobb is a program synthesizer that uses coverage types (underapproximation refinement types) to repair test input generators. It builds on the Poirot type checker from the PLDI 2023 paper "Covering All the Bases: Type-based Verification of Test Input Generators."

The synthesizer performs:
1. **Abduction** - Infers missing coverage (what inputs the generator fails to produce)
2. **Localization** - Identifies program locations that need repair
3. **Synthesis** - Generates repair code using type-guided enumeration

## Build Commands

```bash
# Build the project
dune build
# or
make build

# Run tests
make test
# or
dune runtest bin --always-show-command-line

# Clean build artifacts
dune clean
```

## Running Cobb

```bash
# Run synthesis on a benchmark
cd underapproximation_type && dune exec Cobb -- synthesis data/validation/sizedlist/prog1.ml

# Run a batch of benchmarks via Python script
python scripts/synth.py underapproximation_type/data/validation/sizedlist/

# Run imprecise benchmarks (testing with missing components)
python scripts/synth_imprecise.py underapproximation_type/data/validation/sizedlist_imprecise/

# Type-check a specific example
dune exec -- bin/main.exe type-check meta-config.json data/issue/singleton_unique.ml

# Generate Coq axioms
dune exec -- bin/main.exe coq-axioms meta-config.json
```

## Project Architecture

### Top-Level Structure

- **bin/** - Main synthesizer executable and core synthesis modules
- **underapproximation_type/** - The Poirot type system library (submodule)
- **language_utils/** - Language parsing and AST utilities (submodule)
- **scripts/** - Python scripts for running benchmarks and processing results

### Synthesis Pipeline (bin/)

1. **main.ml** - Entry point with CLI commands: `synthesis`, `abduction`, `config`, `localize`
2. **preprocess.ml** - Prepares source code and extracts function structure
3. **localization.ml** - Identifies repair locations using type information
4. **pieces.ml** - Extracts seeds and components for synthesis from typing context
5. **blocks.ml** - Core enumeration logic coordinating synthesis
6. **postprocess.ml** - Reconstructs final program from synthesized repairs

### Enumeration System (bin/enumeration/)

Type-guided bottom-up enumerative synthesis:
- **block.ml** - Represents synthesis terms with their types
- **blockmap.ml** - Maps types to synthesized terms
- **blockset.ml** - Ordered sets of blocks using partial order
- **synthesiscollection.ml** - Priority-based synthesis state management
- **relation.ml** - Subtyping relations between blocks

### Type System Library (underapproximation_type/)

- **backend/** - Z3 SMT solver interface (`check.ml`, `smtquery.ml`, `z3aux.ml`)
- **typing/** - Type checking (`termcheck.ml`) and synthesis (`termsyn.ml`)
- **subtyping/** - Refinement type subtyping via SMT
- **syntax/** - AST definitions for terms and refinement types
- **frontend_opt/** - Type context and optimizations
- **preprocessing/** - Code normalization and preparation
- **coq_proof/** - Coq formalization of the type system

### Language Utilities (language_utils/)

- **metalang/** - Meta-language for type annotations
- **normal5ty/** - Normal typing utilities
- **ocaml5_parser/** - OCaml 5 parser adaptation
- **zzdatatype/** - Common data structures

## Configuration

The `meta-config.json` file controls:
- **prim_path** - Paths to predefined types, templates, and axioms
- **debug_tags** - Control debug output ("preprocess", "ntyping", "typing", "queries", "result")
- **logfile/resfile/abdfile** - Output file extensions

Benchmark-specific configs are in each benchmark directory (e.g., `underapproximation_type/data/validation/sizedlist/meta-config.json`).

## Adding New Functions

When you encounter an error like `(len: none) =? none`, add the type signature to the files referenced in `meta-config.json`:
- `normal_typing` - Standard typing
- `coverage_typing` - Coverage type annotations

## Git Submodules

Update submodules:
```bash
git submodule sync
git submodule update --remote
```

## Coq Proofs

Build Coq proofs for the type system soundness:
```bash
make proof
# or
cd underapproximation_type/coq_proof && make
```

## Dependencies

Key OCaml dependencies:
- **z3** (4.15.1) - SMT solver
- **core/core_unix** - Jane Street standard library
- **pomap** - Partially ordered maps
- **ocamlformat** (0.26.1) - Code formatting

Requires OCaml 5.1.0+. Use `opam switch create ./ --deps-only` for local setup.
