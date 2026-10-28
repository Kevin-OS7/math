# Mathematics manuscript collection

**3 manuscripts covering 3 result families.**

[**Read the overview PDF**](overview.pdf).

## Manuscript map

Each result description is followed by its constituent manuscripts and their abstracts. Paper titles link directly to PDFs.

<table>
<thead><tr><th>Result</th></tr></thead>
<tbody><tr>
<td>

**001. The maximum number of non-equivalent ancestral configurations.** *Mathematical biology (phylogenetics); enumerative combinatorics.* Proves the conjecture of Disanto and Rosenberg (Bull. Math. Biol. 2019) that the maximum number of non-equivalent root ancestral configurations of a matching gene tree / species tree pair with <i>n</i> ≥ 2 leaves is ⌊3<sup>⌊<i>n</i>/3⌋</sup>(2<i>r</i><sup>2</sup>+8<i>r</i>+23)/27⌋, <i>r</i> = <i>n</i> mod 3. The maximizing shape is unique for <i>n</i> ≥ 9, the growth constant is 3<sup>1/3</sup>, and the minimum is <i>n</i> − 1. Formalized in Lean (two independent proofs).

</td>
</tr></tbody>
<tbody><tr>
<td>

&emsp;[The maximum number of non-equivalent ancestral configurations: a proof of a conjecture of Disanto and Rosenberg](preprints/The-maximum-number-of-non-equivalent-ancestral-configurations-October-29-2026/paper.pdf)

Ancestral configurations are the combinatorial objects that underlie the computation of gene tree probabilities under the multispecies coalescent. For a species tree with <i>n</i> leaves and a gene tree of the same labeled topology, Disanto and Rosenberg studied the number <i>c</i><sup>*</sup>(<i>T</i>) of non-equivalent root ancestral configurations and conjectured that its maximum over all tree shapes with <i>n</i> ≥ 2 leaves equals ⌊3<sup>⌊<i>n</i>/3⌋</sup>(2<i>r</i><sup>2</sup>+8<i>r</i>+23)/27⌋, having verified this for <i>n</i> ≤ 20. We prove the conjecture for all <i>n</i>. We further show that for every <i>n</i> ≥ 9 the maximizing tree shape is unique; that the exponential growth constant of the maximum is exactly 3<sup>1/3</sup>, which settles the value of a constant left undetermined by Disanto and Rosenberg; and that the minimum of <i>c</i><sup>*</sup>(<i>T</i>) is <i>n</i> − 1, attained by exactly two tree shapes for every <i>n</i> ≥ 4. The proof rests on an exact product formula for the number of pruned shapes of a tree together with an elementary but delicate arithmetic inequality.

</td>
</tr></tbody>
<tbody><tr>
<td>

**002. The reversed-prime iteration of OEIS A100475.** *Elementary number theory.* Answers the question in OEIS A100475 (2004): iterating <i>k</i> ↦ rev(<i>p<sub>k</sub></i>), the decimal reversal of the <i>k</i>-th prime, never enters a cycle. This disproves the open statement `OeisA100475.conjecture` of google-deepmind/formal-conjectures. Formalized in Lean.

</td>
</tr></tbody>
<tbody><tr>
<td>

&emsp;[The reversed-prime iteration of OEIS A100475 never enters a cycle](preprints/The-reversed-prime-iteration-of-OEIS-A100475-never-enters-a-cycle-October-29-2026/paper.pdf)

Let <i>p<sub>k</sub></i> be the <i>k</i>-th prime and rev(<i>m</i>) the integer whose decimal digits are those of <i>m</i> in reverse order. The OEIS sequence A100475 iterates <i>k</i> ↦ rev(<i>p<sub>k</sub></i>) from 1, and its entry asks whether the iteration, started anywhere other than 1, ever goes into a loop. We show that it never does: for every starting value <i>x</i> ≥ 1 the orbit is not eventually periodic. The proof combines the monotonicity of the number of digits along an orbit with the bound π(10<sup><i>d</i></sup>) &lt; 10<sup><i>d</i>−1</sup> for <i>d</i> ≥ 5 and a finite check. In contrast, in base 6 and in base 8 the analogous map has a fixed point.

</td>
</tr></tbody>
<tbody><tr>
<td>

**003. Maximally probable labeled topologies with simultaneity.** *Mathematical biology (phylogenetics); combinatorics of posets.* Proves Conjecture 14 of Dickey and Rosenberg (Discrete Appl. Math. 2026): the Harding–Hammersley–Grimmett tree <i>U</i><sup>*</sup><sub><i>n</i></sub> uniquely maximizes the number of tie-permitting labeled histories and maximizes the number with any fixed number of simultaneous-event times. A coefficientwise multivariate strengthening holds. Formalized in Lean, including uniqueness and the paper's recursive definition of <i>U</i><sup>*</sup><sub><i>n</i></sub>.

</td>
</tr></tbody>
<tbody><tr>
<td>

&emsp;[Maximally probable labeled topologies with simultaneity: a proof of a conjecture of Dickey and Rosenberg](preprints/Maximally-probable-labeled-topologies-with-simultaneity-October-29-2026/paper.pdf)

A labeled history of a rooted binary tree is an ordering of its internal vertices compatible with ancestry; when several vertices may share an event time one obtains tie-permitting labeled histories. For a binary tree shape <i>T</i> with <i>n</i> leaves let <i>E</i>(<i>T</i>,<i>z</i>) be the number of tie-permitting labeled histories with exactly <i>z</i> events, and <i>N</i>(<i>T</i>) = Σ<sub><i>z</i></sub> <i>E</i>(<i>T</i>,<i>z</i>). Dickey and Rosenberg conjectured that the tree <i>U</i><sup>*</sup><sub><i>n</i></sub> of Harding, Hammersley and Grimmett, which uniquely maximizes the number of ordinary labeled histories, also uniquely maximizes <i>N</i>(<i>T</i>) and maximizes <i>E</i>(<i>T</i>,<i>z</i>) for every admissible <i>z</i>. We prove this conjecture in a stronger form: for every bound <i>m</i>, the multivariate generating polynomial of strictly order-preserving labelings of the internal vertices of <i>T</i> by {1,…,<i>m</i>} is coefficientwise dominated by that of <i>U</i><sup>*</sup><sub><i>n</i></sub>. The proof combines a switching injection for pairs of labelings of a union and an intersection of trees, with different label bounds on the two sides, and an induction that follows the dyadic structure of <i>U</i><sup>*</sup><sub><i>n</i></sub>. Both parts of the conjecture, including uniqueness, have been formally verified in Lean 4 with Mathlib.

</td>
</tr></tbody>
</table>
