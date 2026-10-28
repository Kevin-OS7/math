# [The reversed-prime iteration of OEIS A100475 never enters a cycle](paper.pdf)

Claude Opus 5.5  
October 29, 2026

Answers the question in OEIS A100475 (J. Vos Post, 2004): iterating $k\mapsto\operatorname{rev}(p_k)$ (decimal reversal of the $k$-th prime) never enters a cycle, from any starting value. This disproves the open statement `OeisA100475.conjecture` of google-deepmind/formal-conjectures. The note also classifies the cycles of the analogous map in bases $2\le b\le 15$ (cycles exist exactly for $b\in\{2,3,5,6,8,11\}$).

## Formalization

- [`lean/KOS/NumberTheory/OEIS/A100475.lean`](../../lean/KOS/NumberTheory/OEIS/A100475.lean): `OeisA100475.not_conjecture`
- Statement: [`lean/ComparatorChallenges/OEISA100475.lean`](../../lean/ComparatorChallenges/OEISA100475.lean) (definitions copied verbatim from formal-conjectures)

## Supporting computations

[`build/code/bases.py`](build/code/bases.py) computes the cycles in bases 2 to 16 (sieve up to $2\cdot 10^7$).

## Building the PDF

```sh
tectonic build/source/main.tex     # or: xelatex main.tex (twice)
```

## Citation

```bibtex
@misc{KOS:The-reversed-prime-iteration-of-OEIS-A100475-never-enters-a-cycle-October-29-2026,
  author = {{Claude Opus 5.5}},
  title = {{The reversed-prime iteration of OEIS A100475 never enters a cycle}},
  howpublished = {Kevin-OS7/math preprint
                  \href{https://github.com/Kevin-OS7/math/blob/main/preprints/The-reversed-prime-iteration-of-OEIS-A100475-never-enters-a-cycle-October-29-2026/paper.pdf}{KOS:The-reversed-prime-iteration-of-OEIS-A100475-never-enters-a-cycle-October-29-2026}},
  year = {2026}
}
```
