# History

For any withdrawn papers, their README files will explain the gap and link to the retracted manuscript. For any updated papers, previously published editions remain accessible through the git history.

## October 29, 2026 (third release)

**Formalization addition**

- *The maximum number of non-equivalent ancestral configurations.* The reduction from the original definitions of Disanto and Rosenberg is now machine-checked: `PaperDefinitions.lean` defines ancestral configurations through realizations of the gene tree (their Sect. 2.3), proves the decomposition of their Sect. 2.4 and the count of their eq. (5), defines the restricted trees and the equivalence of their Sect. 3.1 literally, reproduces their worked examples, and proves that the number of non-equivalent root configurations equals the quantity used in the main formalization. The manuscript was updated accordingly.

## October 29, 2026 (second release)

**New result**

- *Maximally probable labeled topologies with simultaneity: a proof of a conjecture of Dickey and Rosenberg.* Proves Conjecture 14 of Dickey and Rosenberg (Discrete Appl. Math. 2026) in a stronger, coefficientwise form. Lean formalization of both parts, including uniqueness, and of the identification of the paper's recursively defined tree with the breadth-first tree used in the proof.

**Verification improvements**

- All three Comparator statements were also checked with the independent kernel [nanoda](https://github.com/ammkrn/nanoda_lib) in addition to the Lean kernel.
- The README now records how earlier work was searched for, including GitHub.

## October 29, 2026 (initial release)

**Initial release**

- *The maximum number of non-equivalent ancestral configurations: a proof of a conjecture of Disanto and Rosenberg.* Proves the conjectured formula for the maximum, uniqueness of the maximizer for n ≥ 9, the growth constant 3^(1/3), and the minimum n − 1. Two independent Lean formalizations.
- *The reversed-prime iteration of OEIS A100475 never enters a cycle.* Negative answer to the question in OEIS A100475, with a Lean proof of the negation of the corresponding formal-conjectures statement.
