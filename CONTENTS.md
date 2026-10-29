# Mathematics manuscript collection

**8 manuscripts covering 8 result families.**

[**Read the overview PDF**](overview.pdf).

## Manuscript map

Each result description is followed by its constituent manuscripts and their abstracts. Paper titles link directly to PDFs.

<table>
<thead><tr><th>Result</th></tr></thead>
<tbody><tr>
<td>

**001. The maximum number of non-equivalent ancestral configurations.** *Mathematical biology (phylogenetics); enumerative combinatorics.* Proves the conjecture of Disanto and Rosenberg (Bull. Math. Biol. 2019) that the maximum number of non-equivalent root ancestral configurations of a matching gene tree / species tree pair with <i>n</i> ≥ 2 leaves is ⌊3<sup>⌊<i>n</i>/3⌋</sup>(2<i>r</i><sup>2</sup>+8<i>r</i>+23)/27⌋, <i>r</i> = <i>n</i> mod 3. The maximizing shape is unique for <i>n</i> ≥ 9, the growth constant is 3<sup>1/3</sup>, and the minimum is <i>n</i> − 1. Formalized in Lean (two independent proofs), starting from the paper's original definition of ancestral configurations.

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
<tbody><tr>
<td>

**004. The minimum and maximum forcing numbers of bipartite graphs.** *Graph theory; mathematical chemistry (Kekulé structures).* Answers Problem 5.5 of Liu, Diwan and Zhang (arXiv:2512.22761) affirmatively: every bipartite graph <i>G</i> of order 2<i>n</i> with a perfect matching satisfies <i>n</i> ≤ (<i>f</i>(<i>G</i>)+1)(<i>n</i> − <i>F</i>(<i>G</i>)), where <i>f</i> and <i>F</i> are the minimum and maximum forcing numbers. Formalized in Lean.

</td>
</tr></tbody>
<tbody><tr>
<td>

&emsp;[The minimum and maximum forcing numbers of bipartite graphs: an answer to a question of Liu, Diwan and Zhang](preprints/The-minimum-and-maximum-forcing-numbers-of-bipartite-graphs-October-29-2026/paper.pdf)

For a perfect matching <i>M</i> of a graph <i>G</i>, the forcing number <i>f</i>(<i>G</i>,<i>M</i>) is the smallest size of a subset of <i>M</i> contained in no other perfect matching; the minimum and maximum of <i>f</i>(<i>G</i>,<i>M</i>) over all perfect matchings are denoted <i>f</i>(<i>G</i>) and <i>F</i>(<i>G</i>). The notion goes back to the "innate degree of freedom" of Kekulé structures in chemistry. Liu, Diwan and Zhang asked whether every bipartite graph <i>G</i> of order 2<i>n</i> with <i>F</i>(<i>G</i>) ≥ <i>n</i> − <i>k</i>, where 1 ≤ <i>k</i> ≤ <i>n</i> − 1, satisfies <i>f</i>(<i>G</i>) ≥ ⌈<i>n</i>/<i>k</i>⌉ − 1; they proved this for <i>k</i> = 1, 2. We answer the question affirmatively for all <i>k</i>. Equivalently, every bipartite graph of order 2<i>n</i> with a perfect matching satisfies <i>n</i> ≤ (<i>f</i>(<i>G</i>)+1)(<i>n</i> − <i>F</i>(<i>G</i>)). The proof combines the triangular structure of a bipartite graph with a unique perfect matching, an interval representation of an arbitrary perfect matching, and the greedy algorithm for interval scheduling. The result has been formally verified in Lean 4 with Mathlib.

</td>
</tr></tbody>
<tbody><tr>
<td>

**005. Minimum-variance phylogenetic trees are not unique.** *Mathematical biology (phylogenetics, tree balance).* Disproves the conjecture of Coronado, Mir, Rosselló and Rotger (BMC Bioinformatics 2020) that the bifurcating trees of minimum leaf-depth variance are unique up to depth-equivalence: two trees with 67,256,579 leaves and different leaf-depth multisets tie. This is the smallest counterexample. Formalized in Lean, including global minimality.

</td>
</tr></tbody>
<tbody><tr>
<td>

&emsp;[Minimum-variance phylogenetic trees are not unique up to depth-equivalence](preprints/Minimum-variance-phylogenetic-trees-are-not-unique-up-to-depth-equivalence-October-29-2026/paper.pdf)

Coronado, Mir, Rosselló and Rotger studied the variance <i>V</i>(<i>T</i>) of the depths of the leaves of a rooted bifurcating tree <i>T</i>, the balance index originally proposed by Sackin. They gave an algorithm for the minimum of <i>V</i> over the bifurcating trees with <i>n</i> leaves, ran it for every <i>n</i> ≤ 2<sup>20</sup>, and conjectured that for every <i>n</i> the minimizing trees are unique up to depth-equivalence, that is, they all have the same multiset of leaf depths. We show that the conjecture is false. For <i>n</i> = 67,256,579 there are two bifurcating trees with different multisets of leaf depths that both attain the minimum, <i>n</i><sup>2</sup><i>V</i> = 330,431,494,786. Using the structure theorem of Coronado et al., an exact search shows that this is the smallest such <i>n</i>, and that up to 2<sup>28</sup> there are exactly six values of <i>n</i> with two minimizing profiles. The proof of global minimality is self-contained. Cutting an arbitrary tree at a suitable level reduces the problem to a relaxed integer problem whose optimal solutions have a rigid normal form, and a certificate of 16,800 exact integer evaluations completes the argument. The disproof, including the construction of the two trees and their global minimality among all bifurcating trees with <i>n</i> leaves, is formalized and checked in Lean 4.

</td>
</tr></tbody>
<tbody><tr>
<td>

**006. Connected locally equienergetic graphs.** *Mathematical chemistry (graph energy); spectral graph theory.* Disproves Conjecture 1 and Corollary 2 of Dede and Popat (MATCH Commun. Math. Comput. Chem. 2025): besides (<i>K<sub>n</sub></i>, <i>C<sub>n</sub></i>) for odd <i>n</i>, there are exactly 58 pairs of connected locally equienergetic graphs of order ≤ 10, all of order 10, and further pairs of order 16, including a pair with different energies. Formalized in Lean.

</td>
</tr></tbody>
<tbody><tr>
<td>

&emsp;[Connected locally equienergetic graphs: counterexamples to a conjecture of Dede and Popat](preprints/Connected-locally-equienergetic-graphs-October-29-2026/paper.pdf)

The energy of a graph is the sum of the absolute values of the eigenvalues of its adjacency matrix. The local energy of a graph is the sum, over all vertices <i>v</i>, of the decrease of the energy when <i>v</i> is deleted. Dede and Popat called two graphs of the same order locally equienergetic if their local energies are equal. On the basis of a computer search they stated that, up to order 10, the only pairs of connected locally equienergetic graphs are (<i>K<sub>n</sub></i>, <i>C<sub>n</sub></i>) with <i>n</i> odd, and they conjectured that there are no other pairs at all. We show that both statements are false. Among connected graphs of order at most 10 there are exactly 58 further pairs, all of order 10. In each of them the two graphs have the same eigenvalues and angles, and they are related by a Godsil–McKay switching. At order 16, the 4 × 4 rook's graph, the Shrikhande graph and the complement of the Clebsch graph all have local energy 64, although the energy of the last graph is 40 and that of the other two is 36. More generally, cospectral walk-regular graphs are locally equienergetic, and a strongly regular graph of order <i>n</i> whose eigenvalues <i>k</i> &gt; <i>r</i> ≥ 0 &gt; <i>s</i> satisfy a sign condition has local energy 2<i>n</i>|<i>s</i>|. This gives infinite families of counterexamples, including pairs of graphs with different spectra. The counterexamples of orders 10 and 16 are verified in Lean 4.

</td>
</tr></tbody>
<tbody><tr>
<td>

**007. The two largest coset leaders modulo (<i>q</i>+1)(<i>q<sup>m</sup></i> ± 1).** *Coding theory (BCH codes); number theory.* Proves the two conjectures of Liu, Wu and Zhu (arXiv:2603.07688) on the two largest <i>q</i>-cyclotomic coset leaders modulo (<i>q</i>+1)(<i>q<sup>m</sup></i>+1) and (<i>q</i>+1)(<i>q<sup>m</sup></i>−1), for all odd <i>m</i> ≥ 3; for <i>m</i> = 1 the formulas fail. Formalized in Lean.

</td>
</tr></tbody>
<tbody><tr>
<td>

&emsp;[The two largest coset leaders modulo (q+1)(q^m±1): a proof of two conjectures of Liu, Wu and Zhu](preprints/A-proof-of-two-conjectures-of-Liu-Wu-and-Zhu-on-coset-leaders-October-29-2026/paper.pdf)

The largest <i>q</i>-cyclotomic coset leaders modulo <i>n</i> determine the largest designed distances of BCH codes of length <i>n</i> over F<sub><i>q</i></sub>. Liu, Wu and Zhu (arXiv 2026) studied BCH codes of length λ(<i>q<sup>m</sup></i>+1) with λ | <i>q</i>−1. For the lengths (<i>q</i>+1)(<i>q<sup>m</sup></i>+1) and (<i>q</i>+1)(<i>q<sup>m</sup></i>−1), which their methods do not cover, they conjectured explicit formulas for the two largest coset leaders when <i>m</i> is odd, on the basis of computations. We prove both conjectures for all odd <i>m</i> ≥ 3. For the length (<i>q</i>+1)(<i>q<sup>m</sup></i>+1) the formulas hold for every odd <i>q</i> ≥ 3, and for (<i>q</i>+1)(<i>q<sup>m</sup></i>−1) for every <i>q</i> ≥ 2; in particular, for every odd prime power, respectively every prime power, <i>q</i>. For <i>m</i> = 1 the formulas fail. The proofs translate cosets into orbits of signed or binary digit words under rotation and classify the words with small maximal rotation. Both results are formalized and checked in Lean 4.

</td>
</tr></tbody>
<tbody><tr>
<td>

**008. The third largest coset leader modulo <i>q<sup>m</sup></i>+1.** *Coding theory (antiprimitive BCH codes).* Disproves Conjecture 25 of Liu, Li, Guo and Song (Discrete Math. 2023): for <i>q</i> = 4 and <i>m</i> = 12 the conjectured third largest coset leader is not a coset leader. Formalized in Lean; computations suggest a corrected formula.

</td>
</tr></tbody>
<tbody><tr>
<td>

&emsp;[The third largest coset leader modulo q^m+1: a counterexample to a conjecture of Liu, Li, Guo and Song](preprints/A-counterexample-to-a-conjecture-of-Liu-Li-Guo-and-Song-on-coset-leaders-October-29-2026/paper.pdf)

The largest coset leaders of <i>q</i>-cyclotomic cosets modulo <i>n</i> determine the largest designed distances of BCH codes of length <i>n</i>. For <i>n</i> = <i>q<sup>m</sup></i>+1 with <i>q</i> a power of two and <i>m</i> = 2<sup><i>r</i></sup><i>t</i>+2<sup><i>r</i>−1</sup> (<i>r</i> ≥ 2, <i>t</i> ≥ 1), Liu, Li, Guo and Song proved a formula for the largest coset leader δ<sub>1</sub> and conjectured formulas for the second and third largest ones (Discrete Math. 2023, Conjecture 25). We show that the conjecture is false: for <i>q</i> = 4 and <i>m</i> = 12 the conjectured third largest coset leader 5875062 is not a coset leader at all, since 5875062 · 4<sup>6</sup> ≡ 5724774 (mod 4<sup>12</sup>+1). This is verified in Lean 4. In computations with <i>q</i> ∈ {2,4,8,16}, 2 ≤ <i>r</i> ≤ 4 and 1 ≤ <i>t</i> ≤ 3, the conjectured δ<sub>2</sub> was a coset leader in every case and the second largest leader in every case we could check, while the conjectured δ<sub>3</sub> failed exactly when <i>t</i> = 1 and <i>r</i> ≥ 3, that is, for <i>m</i> = 3·2<sup><i>r</i>−1</sup> ≥ 12; in each of these cases it is not even a coset leader. For <i>q</i> = 2 and <i>m</i> = 12 the conjectured value also contradicts a theorem of Liu, Li, Fu, Lu and Rao. In every case we could check, the third largest coset leader for <i>t</i> = 1 equals δ<sub>2</sub> − (<i>q</i>−1)<i>q</i><sup>2<sup><i>r</i>−2</sup>+1</sup>∏<sub><i>j</i>=1</sub><sup><i>r</i>−2</sup>(<i>q</i><sup>2<sup><i>j</i></sup></sup>−1), which we propose as a corrected conjecture.

</td>
</tr></tbody>
</table>
