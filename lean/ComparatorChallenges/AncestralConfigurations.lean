import Mathlib

/-!
# The Disanto–Rosenberg conjecture on non-equivalent ancestral configurations

F. Disanto and N. A. Rosenberg, *On the number of non-equivalent ancestral configurations for
matching gene trees and species trees*, Bull. Math. Biol. 81 (2019) 384–407
(doi:10.1007/s11538-017-0342-x), conjecture following eq. (16) in Section 4.3:
for every `n ≥ 2`, the maximum over unlabeled rooted binary (species) trees with `n` leaves of the
number of non-equivalent root ancestral configurations of the matching gene tree is
`⌊3^⌊n/3⌋ (2r² + 8r + 23) / 27⌋`, where `r = n mod 3`.

For a matching gene tree / species tree pair with tree `T`, root ancestral configurations
correspond to the cuts of `T` other than the trivial cut `{root}`; two configurations are
equivalent iff the trees obtained from `T` by deleting everything strictly below the nodes of the
cut are isomorphic as unordered rooted trees.  Hence the number of non-equivalent root
configurations is the number of isomorphism classes of non-trivial prunings of `T`.
-/

namespace KOS.AncestralConfigurations


/-- Plane (ordered) rooted binary trees.  Unordered tree shapes are their classes modulo `Iso`. -/
inductive BTree where
  | leaf : BTree
  | node : BTree → BTree → BTree
  deriving DecidableEq, Repr

namespace BTree

/-- Number of leaves. -/
def leaves : BTree → ℕ
  | leaf => 1
  | node l r => l.leaves + r.leaves

/-- Isomorphism of unordered rooted binary trees: the children of any node may be swapped. -/
inductive Iso : BTree → BTree → Prop
  | leaf : Iso leaf leaf
  | node {a b c d : BTree} : Iso a c → Iso b d → Iso (node a b) (node c d)
  | swap {a b c d : BTree} : Iso a d → Iso b c → Iso (node a b) (node c d)

/-- Tree shapes (unlabeled unordered rooted binary trees). (`EqvGen Iso` coincides with `Iso`.) -/
def shapeSetoid : Setoid BTree := Relation.EqvGen.setoid Iso

/-- The prunings of `T`: the trees obtained from `T` by choosing a cut (a set of nodes meeting
every root-to-leaf path exactly once) and deleting all nodes strictly below the cut.  The cut
`{root}` gives `leaf`; otherwise the root survives and the cut restricts to cuts of both
subtrees. -/
def prunings : BTree → Finset BTree
  | leaf => {leaf}
  | node l r => insert leaf ((l.prunings ×ˢ r.prunings).image fun p => node p.1 p.2)

/-- The number `c*(r)` of non-equivalent root ancestral configurations for the matching gene
tree / species tree pair of shape `T`: the number of isomorphism classes of non-trivial
prunings of `T`. -/
noncomputable def rootConfigs (T : BTree) : ℕ :=
  Nat.card {s : Quotient shapeSetoid // ∃ P ∈ T.prunings, P ≠ leaf ∧ Quotient.mk _ P = s}

end BTree

/-- The conjectured maximum `⌊3^⌊n/3⌋ (2r² + 8r + 23) / 27⌋`, `r = n mod 3`. -/
def drMax (n : ℕ) : ℕ := 3 ^ (n / 3) * (2 * (n % 3) ^ 2 + 8 * (n % 3) + 23) / 27

/-- **Disanto–Rosenberg conjecture.** For `n ≥ 2`, `drMax n` is the maximum number of
non-equivalent root ancestral configurations over trees with `n` leaves. -/
theorem disanto_rosenberg (n : ℕ) (hn : 2 ≤ n) :
    IsGreatest {k | ∃ T : BTree, T.leaves = n ∧ T.rootConfigs = k} (drMax n) := by
  sorry

end KOS.AncestralConfigurations
