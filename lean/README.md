# Lean formalizations

This directory is a Lake project (Lean 4 `v4.33.1`, Mathlib `v4.33.1`, commit `0df444a`) containing the formal proofs of the results in this repository.

| Result | Statement (fixed before the proofs) | Proofs | Main declarations |
|---|---|---|---|
| 001 Disanto–Rosenberg conjecture | [`ComparatorChallenges/AncestralConfigurations.lean`](ComparatorChallenges/AncestralConfigurations.lean) | [`KOS/Phylogenetics/AncestralConfigurations/Main.lean`](KOS/Phylogenetics/AncestralConfigurations/Main.lean) | `KOS.AncestralConfigurations.disanto_rosenberg`, `…disanto_rosenberg_unique`, `…disanto_rosenberg_minimum` |
| | | [`KOS/Phylogenetics/AncestralConfigurations/Independent.lean`](KOS/Phylogenetics/AncestralConfigurations/Independent.lean) (independent second proof) | `KOS.AncestralConfigurationsIndependent.disanto_rosenberg`, `…_unique`, `…_unique_shape`, `…_min` |
| | | [`KOS/Phylogenetics/AncestralConfigurations/PaperDefinitions.lean`](KOS/Phylogenetics/AncestralConfigurations/PaperDefinitions.lean) (the paper's own definitions) | `KOS.AncestralConfigurations.disanto_rosenberg_paper`, `…disanto_rosenberg_realizations`, `…paperRootConfigsNonequiv_eq_rootConfigs`, `…realizationConfigs_eq_configsAt` |
| 002 OEIS A100475 | [`ComparatorChallenges/OEISA100475.lean`](ComparatorChallenges/OEISA100475.lean) | [`KOS/NumberTheory/OEIS/A100475.lean`](KOS/NumberTheory/OEIS/A100475.lean) | `OeisA100475.not_conjecture` |
| 003 Dickey–Rosenberg Conjecture 14 | [`ComparatorChallenges/DickeyRosenberg.lean`](ComparatorChallenges/DickeyRosenberg.lean) | [`KOS/Phylogenetics/LabeledHistories/Main.lean`](KOS/Phylogenetics/LabeledHistories/Main.lean) | `DickeyRosenberg.conjecture14i`, `DickeyRosenberg.conjecture14ii`, `DickeyRosenberg.ustar_iso_canonical`, `DickeyRosenberg.conjecture14i_paper`, `DickeyRosenberg.conjecture14ii_paper` |
| 004 Liu–Diwan–Zhang Problem 5.5 (forcing numbers) | [`ComparatorChallenges/ForcingNumbers.lean`](ComparatorChallenges/ForcingNumbers.lean) | [`KOS/GraphTheory/ForcingNumbers/Main.lean`](KOS/GraphTheory/ForcingNumbers/Main.lean) | `Forcing.problem55` |
| 005 Minimum-variance trees (disproof) | [`ComparatorChallenges/DepthVariance.lean`](ComparatorChallenges/DepthVariance.lean) | [`KOS/Phylogenetics/DepthVariance/Main.lean`](KOS/Phylogenetics/DepthVariance/Main.lean) | `DepthVariance.minimum_variance_depth_unique_false`, `DepthVariance.explicit_counterexample` |
| 006 Dede–Popat Conjecture 1 and Corollary 2 (disproof) | [`ComparatorChallenges/LocalEnergy.lean`](ComparatorChallenges/LocalEnergy.lean) | [`KOS/ChemicalGraphTheory/LocalEnergy/Main.lean`](KOS/ChemicalGraphTheory/LocalEnergy/Main.lean) | `DedePopat.not_conjecture1`, `DedePopat.not_conjecture1NonEquienergetic`, `DedePopat.not_corollary2`, `DedePopat.order10_counterexample` |
| 007 Liu–Wu–Zhu conjectures (coset leaders) | [`ComparatorChallenges/TwoLargestCosetLeaders.lean`](ComparatorChallenges/TwoLargestCosetLeaders.lean) | [`KOS/CodingTheory/TwoLargestCosetLeaders/Main.lean`](KOS/CodingTheory/TwoLargestCosetLeaders/Main.lean) | `CosetA.conjecturesA` |
| 008 Liu–Li–Guo–Song Conjecture 25 (disproof) | [`ComparatorChallenges/ThirdLargestCosetLeader.lean`](ComparatorChallenges/ThirdLargestCosetLeader.lean) | [`KOS/CodingTheory/ThirdLargestCosetLeader/Main.lean`](KOS/CodingTheory/ThirdLargestCosetLeader/Main.lean) | `CosetB.conjecture25_false`, `CosetB.counterexample_q4_m12` |

Every proof file begins with a verbatim copy of the definitions of its challenge file and contains its theorem statements verbatim (for `Independent.lean` only the namespace differs, so that both proofs can be imported together). For the disproofs (005, 006, 008) the challenge statements are negations of the conjectures. The formalization catalogue is [`formalization.yaml`](formalization.yaml).

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
[`ComparatorChallenges/AncestralConfigurations.json`](ComparatorChallenges/AncestralConfigurations.json) (statement vs. `KOS/Phylogenetics/AncestralConfigurations/Main.lean`), [`OEISA100475.json`](ComparatorChallenges/OEISA100475.json), [`DickeyRosenberg.json`](ComparatorChallenges/DickeyRosenberg.json), [`ForcingNumbers.json`](ComparatorChallenges/ForcingNumbers.json), [`DepthVariance.json`](ComparatorChallenges/DepthVariance.json), [`LocalEnergy.json`](ComparatorChallenges/LocalEnergy.json), [`TwoLargestCosetLeaders.json`](ComparatorChallenges/TwoLargestCosetLeaders.json) and [`ThirdLargestCosetLeader.json`](ComparatorChallenges/ThirdLargestCosetLeader.json).
Comparator checks that the solution proves exactly the challenge statement, that every constant occurring in the statement (including the custom definitions) is identical in both modules, and that only `propext`, `Quot.sound` and `Classical.choice` are used.
Install `comparator`, `landrun` and `lean4export` and make them available on `PATH`; then, from `lean/`:

```sh
lake env comparator ComparatorChallenges/AncestralConfigurations.json
lake env comparator ComparatorChallenges/OEISA100475.json
lake env comparator ComparatorChallenges/DickeyRosenberg.json
lake env comparator ComparatorChallenges/ForcingNumbers.json
lake env comparator ComparatorChallenges/DepthVariance.json
lake env comparator ComparatorChallenges/LocalEnergy.json
lake env comparator ComparatorChallenges/TwoLargestCosetLeaders.json
lake env comparator ComparatorChallenges/ThirdLargestCosetLeader.json
```

All eight report `Your solution is okay!`. We used comparator `v4.33.0` rebuilt with Lean `v4.33.1`, lean4export `15f6055`, and landrun `v0.1.17`. As negative controls, changing the body of `drMax`, changing the statement of `not_conjecture`, or removing `Classical.choice` from the permitted axioms each make Comparator fail.

### Second kernel

With `"enable_nanoda": true` in a configuration, Comparator also checks the solution with [nanoda](https://github.com/ammkrn/nanoda_lib), an independent implementation of Lean's type checker written in Rust (it must be on `PATH` as `nanoda_bin`). We ran all eight configurations this way with nanoda commit `d0a02cc` (crate version 0.4.30); nanoda and the Lean kernel both accept all eight solutions. For results 001–003 we also ran nanoda directly on the exported solution modules (`Main`, `Independent` and `A100475` of result 001 and 002, and the module of result 003), which re-checks every declaration, including the kernel computations of result 002, with nanoda's own arithmetic. As negative controls, nanoda rejects exports in which a computed constant or a proof has been altered. The published configurations keep `"enable_nanoda": false`, as in openai/math, so that they run without nanoda.

## What is trusted

The trusted part of each formalization is its challenge file: the definitions and the statement.

- For result 001, `BTree` is the type of plane binary trees, `BTree.Iso` swaps children, shapes are classes of the equivalence relation generated by `Iso`, `BTree.prunings` lists the trees obtained by cutting the tree along a cut, and `BTree.rootConfigs T` counts the shapes of the non-trivial prunings. That this equals the number of non-equivalent root ancestral configurations in the sense of Disanto and Rosenberg is itself proved in `PaperDefinitions.lean`, which defines configurations through realizations of the gene tree as in Sect. 2.3 of their paper (see [`PAPER_DEFINITIONS.md`](KOS/Phylogenetics/AncestralConfigurations/PAPER_DEFINITIONS.md)); the only remaining modeling step is the description of a realization by coalescence times above the speciation times.
- For result 003, a tree is the finite parent-closed set of its internal vertices in the heap numbering of the infinite binary tree, `canonical n` is the breadth-first tree with internal vertices `1, …, n-1`, `E T z` counts surjections onto `Fin z` increasing along child-to-parent edges, and `Isomorphic` is a bijection of internal vertices preserving the parent relation. The paper's own recursive tree `ustar` is defined in the proof file and shown isomorphic to `canonical n`.
- For result 002, the definitions are copied verbatim from `FormalConjectures/OEIS/100475.lean` of [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures). The proof was also checked against that repository directly, by importing its module.
- For result 004, graphs are Mathlib `SimpleGraph`s on a finite vertex type, a perfect matching is a finset of edges in which every vertex has exactly one partner, the forcing number of a perfect matching is the smallest size of a subset contained in no other perfect matching, and `minForcingNumber`/`maxForcingNumber` are the minimum and maximum over all perfect matchings. Bipartiteness is Mathlib's `SimpleGraph.IsBipartite`, and the ceiling $\lceil n/k\rceil$ is written $(n+k-1)/k$.
- For result 005, trees are ordered binary trees (`BTree`), `leafDepths` is the multiset of leaf depths, and `depthObjective T` is $nQ-S^2=n^2V(T)$. Since all quantities are invariant under swapping children, ordered trees represent the paper's unordered shapes. The challenge statement is the negation of the universally quantified uniqueness statement.
- For result 006, the energy of a graph is the sum of the absolute values of the eigenvalues of its real adjacency matrix (`Matrix.IsHermitian.eigenvalues`), `G - v` is the induced subgraph on the complement of `{v}`, and the conjecture is read as a statement about connected, non-isomorphic pairs of the same order; `K_n` is `⊤ : SimpleGraph (Fin n)` and `C_n` is Mathlib's `cycleGraph n`. `Corollary2` adds the hypothesis that the order is at most 10, and `Conjecture1NonEquienergetic` replaces non-isomorphism by different energies.
- For results 007 and 008, `IsCosetLeader q n x` says `x < n` and `x ≤ x q^i mod n` for all `i`, which for `gcd(q, n) = 1` means that `x` is the smallest element of its cyclotomic coset; the rank of a leader is formalized by counting larger leaders. The formulas are transcribed from the papers with natural-number division, which is exact in every case used. Result 007 is stated for prime powers `q` and odd `m ≥ 3` (the conjectures fail for `m = 1`); result 008 refutes the branch `m = 2^r t + 2^(r-1)` of Conjecture 25, which the full conjecture contains.
