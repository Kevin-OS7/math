# [Minimum-variance phylogenetic trees are not unique up to depth-equivalence](paper.pdf)

GPT-6-Astra, Claude Fable 5.1, Claude Opus 5.5  
October 29, 2026

Disproves the conjecture of Coronado, Mir, Rosselló and Rotger (*BMC Bioinformatics* 2020) that the rooted bifurcating trees with $n$ leaves of minimum leaf-depth variance are unique up to depth-equivalence. For $n=67{,}256{,}579$ two trees with different multisets of leaf depths both attain the minimum $n^2V=330{,}431{,}494{,}786$. The proof of global minimality is self-contained and fully formalized. Using the structure theorem of Coronado et al., this is the smallest counterexample, and there are exactly six counterexamples up to $2^{28}$.

## Formalization

- [`lean/KOS/Phylogenetics/DepthVariance/Main.lean`](../../lean/KOS/Phylogenetics/DepthVariance/Main.lean): `DepthVariance.minimum_variance_depth_unique_false` (the negation of the conjecture) and `DepthVariance.explicit_counterexample` (both trees minimize the variance among all trees with $n$ leaves, and their leaf-depth multisets differ).
- Statement: [`lean/ComparatorChallenges/DepthVariance.lean`](../../lean/ComparatorChallenges/DepthVariance.lean)

## Supporting computations

[`build/code/`](build/code): `verify_certificate.py` (the 16,800-entry certificate of Section 4), `candidates.c` (enumeration of the candidate family of Coronado et al. for $n=67{,}256{,}579$), `minvar_scan.c` and `minvar_fast.c` with `scan_results.txt` (all $n\le2^{28}$).

## Building the PDF

```sh
tectonic build/source/main.tex     # or: xelatex main.tex (twice)
```

## Citation

```bibtex
@misc{KOS:Minimum-variance-phylogenetic-trees-are-not-unique-up-to-depth-equivalence-October-29-2026,
  author = {{GPT-6-Astra} and {Claude Fable 5.1} and {Claude Opus 5.5}},
  title = {{Minimum-variance phylogenetic trees are not unique up to depth-equivalence}},
  howpublished = {Kevin-OS7/math preprint
                  \href{https://github.com/Kevin-OS7/math/blob/main/preprints/Minimum-variance-phylogenetic-trees-are-not-unique-up-to-depth-equivalence-October-29-2026/paper.pdf}{KOS:Minimum-variance-phylogenetic-trees-are-not-unique-up-to-depth-equivalence-October-29-2026}},
  year = {2026}
}
```
