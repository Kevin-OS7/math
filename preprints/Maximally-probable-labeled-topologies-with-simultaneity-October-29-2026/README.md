# [Maximally probable labeled topologies with simultaneity: a proof of a conjecture of Dickey and Rosenberg](paper.pdf)

GPT-6-Astra, Claude Fable 5.1, Claude Opus 5.5  
October 29, 2026

Proves Conjecture 14 of E. H. Dickey and N. A. Rosenberg (*Discrete Appl. Math.* 2026, arXiv:2511.16799; also Conjecture 20 of arXiv:2602.07426): the Harding–Hammersley–Grimmett tree $U^*_n$ uniquely maximizes the number $N(T)$ of tie-permitting labeled histories and maximizes the number $E(T,z)$ with $z$ events for every $z$. In fact, for every label bound $m$ the multivariate generating polynomial of strict labelings of $U^*_n$ coefficientwise dominates that of every other tree with $n$ leaves, so $U^*_n$ maximizes the number of histories with any prescribed ordered sequence of event sizes.

## Formalization

- [`lean/KOS/Phylogenetics/LabeledHistories/Main.lean`](../../lean/KOS/Phylogenetics/LabeledHistories/Main.lean): `DickeyRosenberg.conjecture14i`, `DickeyRosenberg.conjecture14ii` (with the breadth-first tree `canonical n`), `DickeyRosenberg.ustar_iso_canonical` (the paper's recursively defined $U^*_n$ is isomorphic to `canonical n`), and `conjecture14i_paper`, `conjecture14ii_paper` (both parts stated with $U^*_n$ itself). Uniqueness is proved directly, without assuming the Harding–Hammersley–Grimmett theorem.
- Statement: [`lean/ComparatorChallenges/DickeyRosenberg.lean`](../../lean/ComparatorChallenges/DickeyRosenberg.lean)

## Supporting computations

[`build/code/`](build/code): `explore.py` (split comparison for all splits with $n\le 512$), `qsym_check.py` (multivariate split comparison), `switching_check.py` (exhaustive audit of the switching map), `split_case_check.py` (the case analysis of the split lemma).

## Building the PDF

```sh
tectonic build/source/main.tex     # or: xelatex main.tex (twice)
```

## Citation

```bibtex
@misc{KOS:Maximally-probable-labeled-topologies-with-simultaneity-October-29-2026,
  author = {{GPT-6-Astra} and {Claude Fable 5.1} and {Claude Opus 5.5}},
  title = {{Maximally probable labeled topologies with simultaneity: a proof of a conjecture of Dickey and Rosenberg}},
  howpublished = {Kevin-OS7/math preprint
                  \href{https://github.com/Kevin-OS7/math/blob/main/preprints/Maximally-probable-labeled-topologies-with-simultaneity-October-29-2026/paper.pdf}{KOS:Maximally-probable-labeled-topologies-with-simultaneity-October-29-2026}},
  year = {2026}
}
```
