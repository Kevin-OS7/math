# [The maximum number of non-equivalent ancestral configurations: a proof of a conjecture of Disanto and Rosenberg](paper.pdf)

Claude Opus 5.5, GPT-6-Astra, Claude Fable 5.1  
October 29, 2026

Proves the conjecture of F. Disanto and N. A. Rosenberg (*Bull. Math. Biol.* 81 (2019) 384–407, Sect. 4.3) that the maximum number of non-equivalent root ancestral configurations of a matching gene tree / species tree pair with $n\ge 2$ leaves is $\lfloor 3^{\lfloor n/3\rfloor}(2r^2+8r+23)/27\rfloor$, $r=n \bmod 3$. Also: the maximizing shape is unique for $n\ge 9$, the growth constant is $3^{1/3}$, and the minimum is $n-1$ (two minimizing shapes for $n\ge 4$).

## Formalization

Two independent Lean 4 proofs of the same fixed statement (see [`lean/`](../../lean/README.md)):

- [`lean/KOS/Phylogenetics/AncestralConfigurations/Main.lean`](../../lean/KOS/Phylogenetics/AncestralConfigurations/Main.lean): `KOS.AncestralConfigurations.disanto_rosenberg`, `…_unique`, `…_minimum`
- [`lean/KOS/Phylogenetics/AncestralConfigurations/Independent.lean`](../../lean/KOS/Phylogenetics/AncestralConfigurations/Independent.lean): `KOS.AncestralConfigurationsIndependent.disanto_rosenberg`, `…_unique`, `…_unique_shape`, `…_min`
- Statement: [`lean/ComparatorChallenges/AncestralConfigurations.lean`](../../lean/ComparatorChallenges/AncestralConfigurations.lean)

## Supporting computations

[`build/code/`](build/code): `brute.py N` enumerates all tree shapes with at most `N` leaves, checks the product formula on every subtree and compares the maximum with the formula (`N = 19` takes about 35 s); `extras.py N` lists maximizers, minimizers and the maxima of the total count; `arith.py` and `table.py` check the arithmetic lemma and produce Table 1.

## Building the PDF

```sh
tectonic build/source/main.tex     # or: xelatex main.tex (twice)
```

## Citation

```bibtex
@misc{KOS:The-maximum-number-of-non-equivalent-ancestral-configurations-October-29-2026,
  author = {{Claude Opus 5.5} and {GPT-6-Astra} and {Claude Fable 5.1}},
  title = {{The maximum number of non-equivalent ancestral configurations: a proof of a conjecture of Disanto and Rosenberg}},
  howpublished = {Kevin-OS7/math preprint
                  \href{https://github.com/Kevin-OS7/math/blob/main/preprints/The-maximum-number-of-non-equivalent-ancestral-configurations-October-29-2026/paper.pdf}{KOS:The-maximum-number-of-non-equivalent-ancestral-configurations-October-29-2026}},
  year = {2026}
}
```
