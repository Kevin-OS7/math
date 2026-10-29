# [The third largest coset leader modulo q^m+1: a counterexample to a conjecture of Liu, Li, Guo and Song](paper.pdf)

GPT-6-Astra, Claude Opus 5.5  
October 29, 2026

Disproves Conjecture 25 of Liu, Li, Guo and Song (*Discrete Math.* 2023): for $q=4$ and $m=12$ the conjectured third largest coset leader modulo $q^m+1$ is not a coset leader. In computations the conjectured formula fails exactly in the family $m=3\cdot2^{r-1}\ge12$; we propose a corrected formula, which agrees with a theorem of Liu, Li, Fu, Lu and Rao for $q=2$, $m=12$.

## Formalization

- [`lean/KOS/CodingTheory/ThirdLargestCosetLeader/Main.lean`](../../lean/KOS/CodingTheory/ThirdLargestCosetLeader/Main.lean): `CosetB.conjecture25_false` (the negation of the conjecture) and `CosetB.counterexample_q4_m12` (the explicit counterexample).
- Statement: [`lean/ComparatorChallenges/ThirdLargestCosetLeader.lean`](../../lean/ComparatorChallenges/ThirdLargestCosetLeader.lean)

## Supporting computations

[`build/code/`](build/code): `conj25_check.py` (all computations of Section 3, exact integer arithmetic) and its output.

## Building the PDF

```sh
tectonic build/source/main.tex     # or: xelatex main.tex (twice)
```

## Citation

```bibtex
@misc{KOS:A-counterexample-to-a-conjecture-of-Liu-Li-Guo-and-Song-on-coset-leaders-October-29-2026,
  author = {{GPT-6-Astra} and {Claude Opus 5.5}},
  title = {{The third largest coset leader modulo q^m+1: a counterexample to a conjecture of Liu, Li, Guo and Song}},
  howpublished = {Kevin-OS7/math preprint
                  \href{https://github.com/Kevin-OS7/math/blob/main/preprints/A-counterexample-to-a-conjecture-of-Liu-Li-Guo-and-Song-on-coset-leaders-October-29-2026/paper.pdf}{KOS:A-counterexample-to-a-conjecture-of-Liu-Li-Guo-and-Song-on-coset-leaders-October-29-2026}},
  year = {2026}
}
```
