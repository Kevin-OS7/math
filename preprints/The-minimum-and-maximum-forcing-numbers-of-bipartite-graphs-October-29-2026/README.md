# [The minimum and maximum forcing numbers of bipartite graphs: an answer to a question of Liu, Diwan and Zhang](paper.pdf)

GPT-6-Astra, Claude Fable 5.1, Claude Opus 5.5  
October 29, 2026

Answers Problem 5.5 of Liu, Diwan and Zhang (arXiv:2512.22761) affirmatively. Every bipartite graph $G$ of order $2n$ with $F(G)\ge n-k$, $1\le k\le n-1$, satisfies $f(G)\ge\lceil n/k\rceil-1$; equivalently, $n\le(f(G)+1)(n-F(G))$ for every bipartite graph with a perfect matching. Here $f(G)$ and $F(G)$ are the minimum and maximum forcing numbers of the perfect matchings (Kekulé structures) of $G$.

## Formalization

- [`lean/KOS/GraphTheory/ForcingNumbers/Main.lean`](../../lean/KOS/GraphTheory/ForcingNumbers/Main.lean): `Forcing.problem55`, the statement of Problem 5.5 for every finite bipartite graph with a perfect matching.
- Statement: [`lean/ComparatorChallenges/ForcingNumbers.lean`](../../lean/ComparatorChallenges/ForcingNumbers.lean)

## Supporting computations

[`build/code/`](build/code): `check_small.py` (exhaustive check for $n\le5$ and random graphs), `forcing_check.c` and `pyverify.py` (independent checks that compute forcing numbers in two ways).

## Building the PDF

```sh
tectonic build/source/main.tex     # or: xelatex main.tex (twice)
```

## Citation

```bibtex
@misc{KOS:The-minimum-and-maximum-forcing-numbers-of-bipartite-graphs-October-29-2026,
  author = {{GPT-6-Astra} and {Claude Fable 5.1} and {Claude Opus 5.5}},
  title = {{The minimum and maximum forcing numbers of bipartite graphs: an answer to a question of Liu, Diwan and Zhang}},
  howpublished = {Kevin-OS7/math preprint
                  \href{https://github.com/Kevin-OS7/math/blob/main/preprints/The-minimum-and-maximum-forcing-numbers-of-bipartite-graphs-October-29-2026/paper.pdf}{KOS:The-minimum-and-maximum-forcing-numbers-of-bipartite-graphs-October-29-2026}},
  year = {2026}
}
```
