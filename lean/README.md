# Lean formalizations

This directory is a Lake project (Lean 4 `v4.33.1`, Mathlib `v4.33.1`, commit `0df444a`) containing the formal proofs of the results in this repository.

| Result | Statement (fixed before the proofs) | Proofs | Main declarations |
|---|---|---|---|
| 001 Disanto–Rosenberg conjecture | [`ComparatorChallenges/AncestralConfigurations.lean`](ComparatorChallenges/AncestralConfigurations.lean) | [`KOS/Phylogenetics/AncestralConfigurations/Main.lean`](KOS/Phylogenetics/AncestralConfigurations/Main.lean) | `KOS.AncestralConfigurations.disanto_rosenberg`, `…disanto_rosenberg_unique`, `…disanto_rosenberg_minimum` |
| | | [`KOS/Phylogenetics/AncestralConfigurations/Independent.lean`](KOS/Phylogenetics/AncestralConfigurations/Independent.lean) (independent second proof) | `KOS.AncestralConfigurationsIndependent.disanto_rosenberg`, `…_unique`, `…_unique_shape`, `…_min` |
| 002 OEIS A100475 | [`ComparatorChallenges/OEISA100475.lean`](ComparatorChallenges/OEISA100475.lean) | [`KOS/NumberTheory/OEIS/A100475.lean`](KOS/NumberTheory/OEIS/A100475.lean) | `OeisA100475.not_conjecture` |
| 003 Dickey–Rosenberg Conjecture 14 | [`ComparatorChallenges/DickeyRosenberg.lean`](ComparatorChallenges/DickeyRosenberg.lean) | [`KOS/Phylogenetics/LabeledHistories/Main.lean`](KOS/Phylogenetics/LabeledHistories/Main.lean) | `DickeyRosenberg.conjecture14i`, `DickeyRosenberg.conjecture14ii`, `DickeyRosenberg.ustar_iso_canonical`, `DickeyRosenberg.conjecture14i_paper`, `DickeyRosenberg.conjecture14ii_paper` |

Every proof file begins with a verbatim copy of the definitions and the theorem statement of its challenge file (for `Independent.lean` only the namespace differs, so that both proofs can be imported together). The formalization catalogue is [`formalization.yaml`](formalization.yaml).

## Building and checking

```sh
cd lean
lake exe cache get        # download the Mathlib build
lake build                # builds KOS (all proofs); a few minutes after the cache is in place
lake build ComparatorChallenges   # the statements (each ends in `sorry` by design)
python3 scripts/check_statements.py   # definitions and statements in the proofs = challenge files
lake env lean scripts/CheckAxioms.lean    # prints the axioms of every main theorem
```

`scripts/CheckAxioms.lean` must report `[propext, Classical.choice, Quot.sound]` for every theorem. No proof uses `sorry`, `native_decide`, or additional axioms; all finite computations are checked by the Lean kernel (`decide`, `decide +kernel`).

## Comparator

The challenge files also come with [Comparator](https://github.com/leanprover/comparator) configurations, in the same format as [openai/math](https://github.com/openai/math):
[`ComparatorChallenges/AncestralConfigurations.json`](ComparatorChallenges/AncestralConfigurations.json) (statement vs. `KOS/Phylogenetics/AncestralConfigurations/Main.lean`), [`ComparatorChallenges/OEISA100475.json`](ComparatorChallenges/OEISA100475.json) and [`ComparatorChallenges/DickeyRosenberg.json`](ComparatorChallenges/DickeyRosenberg.json).
Comparator checks that the solution proves exactly the challenge statement, that every constant occurring in the statement (including the custom definitions) is identical in both modules, and that only `propext`, `Quot.sound` and `Classical.choice` are used.
Install `comparator`, `landrun` and `lean4export` and make them available on `PATH`; then, from `lean/`:

```sh
lake env comparator ComparatorChallenges/AncestralConfigurations.json
lake env comparator ComparatorChallenges/OEISA100475.json
lake env comparator ComparatorChallenges/DickeyRosenberg.json
```

All three report `Your solution is okay!`. We used comparator `v4.33.0` rebuilt with Lean `v4.33.1`, lean4export `15f6055`, and landrun `v0.1.17`. As negative controls, changing the body of `drMax`, changing the statement of `not_conjecture`, or removing `Classical.choice` from the permitted axioms each make Comparator fail.

### Second kernel

With `"enable_nanoda": true` in a configuration, Comparator also checks the solution with [nanoda](https://github.com/ammkrn/nanoda_lib), an independent implementation of Lean's type checker written in Rust (it must be on `PATH` as `nanoda_bin`). We ran all three configurations this way with nanoda commit `d0a02cc` (crate version 0.4.30); nanoda and the Lean kernel both accept all three solutions. We also ran nanoda directly on the exported solution modules (`Main`, `Independent` and `A100475` of result 001 and 002, and the module of result 003), which re-checks every declaration, including the kernel computations of result 002, with nanoda's own arithmetic. As negative controls, nanoda rejects exports in which a computed constant or a proof has been altered. The published configurations keep `"enable_nanoda": false`, as in openai/math, so that they run without nanoda.

## What is trusted

The trusted part of each formalization is its challenge file: the definitions and the statement.

- For result 001, `BTree` is the type of plane binary trees, `BTree.Iso` swaps children, shapes are classes of the equivalence relation generated by `Iso`, `BTree.prunings` lists the trees obtained by cutting the tree along a cut, and `BTree.rootConfigs T` counts the shapes of the non-trivial prunings. Section 2 of the manuscript explains why this equals the number of non-equivalent root ancestral configurations in the sense of Disanto and Rosenberg.
- For result 003, a tree is the finite parent-closed set of its internal vertices in the heap numbering of the infinite binary tree, `canonical n` is the breadth-first tree with internal vertices `1, …, n-1`, `E T z` counts surjections onto `Fin z` increasing along child-to-parent edges, and `Isomorphic` is a bijection of internal vertices preserving the parent relation. The paper's own recursive tree `ustar` is defined in the proof file and shown isomorphic to `canonical n`.
- For result 002, the definitions are copied verbatim from `FormalConjectures/OEIS/100475.lean` of [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures). The proof was also checked against that repository directly, by importing its module.
