# [The two largest coset leaders modulo (q+1)(q^m±1): a proof of two conjectures of Liu, Wu and Zhu](paper.pdf)

GPT-6-Astra, Claude Fable 5.1, Claude Opus 5.5  
October 29, 2026

Proves the conjectures of Liu, Wu and Zhu (arXiv:2603.07688) on the two largest $q$-cyclotomic coset leaders modulo $(q+1)(q^m+1)$ and $(q+1)(q^m-1)$ for all odd $m\ge3$; for $m=1$ the formulas fail. The first family is settled for every odd $q\ge3$, the second for every $q\ge2$. These coset leaders give the largest designed distances of BCH codes of these lengths.

## Formalization

- [`lean/KOS/CodingTheory/TwoLargestCosetLeaders/Main.lean`](../../lean/KOS/CodingTheory/TwoLargestCosetLeaders/Main.lean): `CosetA.conjecturesA`, both conjectures for prime powers $q$ and odd $m\ge3$.
- Statement: [`lean/ComparatorChallenges/TwoLargestCosetLeaders.lean`](../../lean/ComparatorChallenges/TwoLargestCosetLeaders.lean)

## Supporting computations

[`build/code/`](build/code): `top_two_check.py` (brute-force comparison of the two largest leaders with the formulas) and its output.

## Building the PDF

```sh
tectonic build/source/main.tex     # or: xelatex main.tex (twice)
```

## Citation

```bibtex
@misc{KOS:A-proof-of-two-conjectures-of-Liu-Wu-and-Zhu-on-coset-leaders-October-29-2026,
  author = {{GPT-6-Astra} and {Claude Fable 5.1} and {Claude Opus 5.5}},
  title = {{The two largest coset leaders modulo (q+1)(q^m±1): a proof of two conjectures of Liu, Wu and Zhu}},
  howpublished = {Kevin-OS7/math preprint
                  \href{https://github.com/Kevin-OS7/math/blob/main/preprints/A-proof-of-two-conjectures-of-Liu-Wu-and-Zhu-on-coset-leaders-October-29-2026/paper.pdf}{KOS:A-proof-of-two-conjectures-of-Liu-Wu-and-Zhu-on-coset-leaders-October-29-2026}},
  year = {2026}
}
```
