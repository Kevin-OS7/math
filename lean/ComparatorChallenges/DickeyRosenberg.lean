import Mathlib

/-!
Faithful statement of Dickey--Rosenberg Conjecture 14.

A full binary tree is encoded by its internal vertices in the infinite binary
heap: root 1, children 2*v and 2*v+1. Its internal vertices form a finite
ancestor-closed set. Missing children are leaves. Ordered embeddings represent
all unordered shapes, and `Isomorphic` explicitly forgets left/right order.

The statements below are definitions, not claims of completed Lean proofs.
-/

namespace DickeyRosenberg

structure Shape where
  nodes : Finset ℕ
  positive : ∀ v ∈ nodes, 0 < v
  closed : ∀ v ∈ nodes, 1 < v → v / 2 ∈ nodes

def Shape.leaves (T : Shape) : ℕ := T.nodes.card + 1

/-- Two internal vertices joined by a child-to-parent edge. -/
def Parent (u v : ℕ) : Prop := 1 < u ∧ u / 2 = v

/-- The canonical tree has internal vertices 1,...,n-1. -/
def canonical (n : ℕ) : Shape where
  nodes := Finset.Ico 1 n
  positive := by intro v hv; simp only [Finset.mem_Ico] at hv; omega
  closed := by
    intro v hv h
    simp only [Finset.mem_Ico] at hv ⊢
    constructor <;> omega

/-- An isomorphism of the internal-node rooted trees; no planar order is imposed. -/
def Isomorphic (T S : Shape) : Prop :=
  ∃ e : {v // v ∈ T.nodes} ≃ {v // v ∈ S.nodes},
    ∀ u v, Parent u.val v.val ↔ Parent (e u).val (e v).val

/-- Labels use Fin z, i.e. 0,...,z-1; adding 1 gives the paper's [z]. -/
def IsHistory (T : Shape) (z : ℕ)
    (f : {v // v ∈ T.nodes} → Fin z) : Prop :=
  Function.Surjective f ∧ ∀ u v, Parent u.val v.val → f u < f v

noncomputable def E (T : Shape) (z : ℕ) : ℕ :=
  Nat.card {f : {v // v ∈ T.nodes} → Fin z // IsHistory T z f}

noncomputable def N (T : Shape) : ℕ :=
  ∑ z ∈ Finset.range (T.nodes.card + 1), E T z

def Conjecture14i : Prop :=
  ∀ T : Shape, N T ≤ N (canonical T.leaves) ∧
    (N T = N (canonical T.leaves) → Isomorphic T (canonical T.leaves))

def Conjecture14ii : Prop :=
  ∀ (T : Shape) (z : ℕ), Nat.clog 2 T.leaves ≤ z → z ≤ T.leaves - 1 →
    E T z ≤ E (canonical T.leaves) z

/-- Dickey–Rosenberg Conjecture 14 (i), with the breadth-first tree `canonical n`
(isomorphic to the paper's recursively defined `U*_n`; see `ustar_iso_canonical`). -/
theorem conjecture14i : Conjecture14i := by
  sorry

/-- Dickey–Rosenberg Conjecture 14 (ii). -/
theorem conjecture14ii : Conjecture14ii := by
  sorry

end DickeyRosenberg
