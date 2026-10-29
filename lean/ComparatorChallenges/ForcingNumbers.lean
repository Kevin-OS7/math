import Mathlib

/-!
Liu--Diwan--Zhang, arXiv:2512.22761v1, Problem 5.5.
Source: https://arxiv.org/html/2512.22761v1
The ambient graphs are finite and simple; connectedness is not assumed.
The quotations below are short excerpts of the definitions in Section 1.
-/

namespace Forcing

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Paper: "a matching that saturates every vertex".
An edge finset in which each vertex has exactly one partner. -/
def IsPerfectMatching (G : SimpleGraph V) (M : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ M, e ∈ G.edgeSet) ∧ ∀ v, ∃! w, s(v, w) ∈ M

/-- Paper: "not contained in any other perfect matching". -/
def IsForcingSet (G : SimpleGraph V) (M S : Finset (Sym2 V)) : Prop :=
  S ⊆ M ∧ ∀ N, IsPerfectMatching G N → S ⊆ N → N = M

/-- Paper: "smallest cardinality" of a forcing set. -/
noncomputable def forcingNumber (G : SimpleGraph V) (M : Finset (Sym2 V)) : ℕ :=
  sInf {r | ∃ S, IsForcingSet G M S ∧ S.card = r}

/-- Paper: "minimum forcing number"; minimum over perfect matchings. -/
noncomputable def minForcingNumber (G : SimpleGraph V) : ℕ :=
  sInf {r | ∃ M, IsPerfectMatching G M ∧ forcingNumber G M = r}

/-- Paper: "maximum forcing number"; maximum over perfect matchings. -/
noncomputable def maxForcingNumber (G : SimpleGraph V) : ℕ :=
  sSup {r | ∃ M, IsPerfectMatching G M ∧ forcingNumber G M = r}

/-- Problem 5.5. Natural-number division expresses ceil(n/k) as (n+k-1)/k.
The perfect-matching hypothesis makes explicit the paper's standing convention. -/
theorem problem55 (G : SimpleGraph V) (n k : ℕ)
    (hG : G.IsBipartite) (horder : Fintype.card V = 2 * n)
    (hpm : ∃ M, IsPerfectMatching G M)
    (hk : 1 ≤ k) (hkn : k ≤ n - 1)
    (hF : n - k ≤ maxForcingNumber G) :
    (n + k - 1) / k - 1 ≤ minForcingNumber G := by sorry

end Forcing
