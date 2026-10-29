# [Connected locally equienergetic graphs: counterexamples to a conjecture of Dede and Popat](paper.pdf)

GPT-6-Astra, Claude Fable 5.1, Claude Opus 5.5  
October 29, 2026

Disproves Conjecture 1 and Corollary 2 of Dede and Popat (*MATCH Commun. Math. Comput. Chem.* 2025) on graphs with equal local energy. Besides $(K_n,C_n)$ for odd $n$, there are exactly 58 pairs of connected locally equienergetic graphs of order at most 10, all of order 10, all with the same eigenvalues and angles. At order 16, the rook's graph $K_4\square K_4$, the Shrikhande graph and the complement of the Clebsch graph all have local energy 64, although the last has a different energy. Cospectral walk-regular graphs, and strongly regular graphs satisfying a sign condition, give infinite families of counterexamples.

## Formalization

- [`lean/KOS/ChemicalGraphTheory/LocalEnergy/Main.lean`](../../lean/KOS/ChemicalGraphTheory/LocalEnergy/Main.lean): `DedePopat.not_conjecture1` (the pair rook/Shrikhande), `DedePopat.not_conjecture1NonEquienergetic` (the pair rook/co-Clebsch, which has different energies), `DedePopat.not_corollary2` and `DedePopat.order10_counterexample` (the pair of order 10 with 16 edges).
- Statement: [`lean/ComparatorChallenges/LocalEnergy.lean`](../../lean/ComparatorChallenges/LocalEnergy.lean)

## Supporting computations

[`build/code/order10/`](build/code/order10): the exhaustive search over connected graphs of order at most 10 (`le_scan.py`, `exact_check.py`, `exact_pairs.py`, `hp_check.py`) with its outputs, the list `pairs10.txt` of the 58 pairs, `verify58.py`, and the certificate generator for the formal proof. [`build/code/`](build/code): checks of the graphs of order 16, the strongly regular families and the 12-vertex example.

## Building the PDF

```sh
tectonic build/source/main.tex     # or: xelatex main.tex (twice)
```

## Citation

```bibtex
@misc{KOS:Connected-locally-equienergetic-graphs-October-29-2026,
  author = {{GPT-6-Astra} and {Claude Fable 5.1} and {Claude Opus 5.5}},
  title = {{Connected locally equienergetic graphs: counterexamples to a conjecture of Dede and Popat}},
  howpublished = {Kevin-OS7/math preprint
                  \href{https://github.com/Kevin-OS7/math/blob/main/preprints/Connected-locally-equienergetic-graphs-October-29-2026/paper.pdf}{KOS:Connected-locally-equienergetic-graphs-October-29-2026}},
  year = {2026}
}
```
