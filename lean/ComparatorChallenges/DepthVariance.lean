import Mathlib

/-!
Source: T. M. Coronado, A. Mir, F. Rosselló and L. Rotger,
"On Sackin's original proposal: the variance of the leaves' depths as a
phylogenetic balance index", BMC Bioinformatics 21 (2020), 154.
https://doi.org/10.1186/s12859-020-3405-1
The quoted definitions are from this CC BY 4.0 article:
https://creativecommons.org/licenses/by/4.0/

Ordered representatives are used for the paper's unordered tree shapes.
Every shape has such a representative, and the quantities below are
unchanged by ordering the children. Thus this does not change the claim.
-/

namespace DepthVariance

/-- "A tree is bifurcating when all its internal nodes have out-degree 2."
The one-vertex tree is represented by `leaf`. -/
inductive BTree where
  | leaf : BTree
  | fork : BTree → BTree → BTree
  deriving DecidableEq

/-- "the multiset of depths of the leaves of T, where each depth appears
with multiplicity the number of leaves with this depth".
Depth is the "length (in number of arcs)" of the path from the root. -/
def leafDepths : BTree → Multiset ℕ
  | .leaf => {0}
  | .fork l r => (leafDepths l + leafDepths r).map Nat.succ

/-- "the spaces ... of ... bifurcating trees with n leaves".
This is the number of leaves, counting multiplicities in the depth multiset. -/
def leafCount (T : BTree) : ℕ := (leafDepths T).card

/-- "the Sackin index S(T) ... defined as the sum of its leaves' depths". -/
def depthSum (T : BTree) : ℤ := ((leafDepths T).map (fun d => (d : ℤ))).sum

/-- "S^{(2)}(T) = ∑_{x ∈ L(T)} δ_T(x)^2". -/
def depthSquareSum (T : BTree) : ℤ :=
  ((leafDepths T).map (fun d => (d : ℤ) ^ 2)).sum

/-- Equation (3): "V(T) = (1/n) S^{(2)}(T) - (1/n^2) S(T)^2".
This integer is exactly `n^2 * V(T)`. At fixed positive leaf count,
minimizing it is equivalent to minimizing the paper's variance. -/
def depthObjective (T : BTree) : ℤ :=
  ((leafCount T) : ℤ) * (depthSquareSum T) - (depthSum T) ^ 2

/-- "the minimum value of V on BT*_n".
The comparison is with every full binary tree with exactly n leaves. -/
def MinimizesDepthVariance (n : ℕ) (T : BTree) : Prop :=
  (leafCount T) = n ∧
    ∀ U : BTree, (leafCount U) = n → (depthObjective T) ≤ (depthObjective U)

/-- Discussion, first conjecture: "the tree in BT*_n with minimum V value
is unique up to depth-equivalence"; depth-equivalence means Δ(T) = Δ(T').
The conjecture is false; this is the negation of its universal statement. -/
theorem minimum_variance_depth_unique_false :
    ¬ (∀ (n : ℕ), 1 ≤ n → ∀ (T T' : BTree),
      MinimizesDepthVariance n T → MinimizesDepthVariance n T' →
      leafDepths T = leafDepths T') := by sorry

end DepthVariance
