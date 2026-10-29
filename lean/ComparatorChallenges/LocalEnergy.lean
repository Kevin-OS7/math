import Mathlib

/-!
# Conjecture 1 of Dede–Popat, "Locally Equienergetic Graphs"

C. Dede, K. M. Popat, *Locally Equienergetic Graphs*,
MATCH Commun. Math. Comput. Chem. **93** (2025) 759–766, doi:10.46793/match.93-3.759D,
arXiv:2604.14686 (identical wording in both versions).

All graphs are finite simple (undirected, loopless) graphs, i.e. `SimpleGraph V` with
`[Fintype V]`.  We formalize the paper's definitions and state the **negation** of its
Conjecture 1.
-/

namespace DedePopat

/-- Paper, §1: "The adjacency matrix `A(G)` of `G` is defined such that `a_ij` equals 1 if
vertices `v_i` and `v_j` are adjacent, and 0 otherwise, for `i, j = 1, 2, …, n`. The eigenvalues
of `A(G)` are called the eigenvalues of `G`. The energy `𝓔(G)` of the graph `G` is defined as the
sum of the absolute values of its eigenvalues."

We take the real adjacency matrix `G.adjMatrix ℝ`; it is symmetric, hence Hermitian, and
`Matrix.IsHermitian.eigenvalues` lists its (real) eigenvalues with multiplicity, indexed by the
vertex type. -/
noncomputable def energy {V : Type*} [Fintype V] (G : SimpleGraph V) : ℝ := by
  classical
  exact ∑ i, |(G.isHermitian_adjMatrix ℝ).eigenvalues i|

/-- Paper, §1: "Let `G^(j)` be the graph obtained from `G` by deleting vertex `v_j`. The quantity
`𝓔(G) − 𝓔(G^(j))` represents the variation in the energy of `G` when vertex `v_j` is deleted.
This variation is called the local energy of `G` at vertex `v_j` and is denoted by `𝓔_G(v_j)`."

The vertex-deleted graph `G − v` is the subgraph induced on `V \ {v}`. -/
noncomputable def localVertexEnergy {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V) : ℝ := by
  classical
  exact energy G - energy (G.induce ({v}ᶜ : Set V))

/-- Paper, §1: "The local energy of graph `G` is defined in [Espinal–Rada] as
`e(G) = ∑_{v ∈ V(G)} 𝓔_G(v)`." -/
noncomputable def localEnergy {V : Type*} [Fintype V] (G : SimpleGraph V) : ℝ :=
  ∑ v, localVertexEnergy G v

/-- Paper, §3: "Two graphs `G₁` and `G₂` of the same order are said to be locally equienergetic
if `e(G₁) = e(G₂)`." -/
def LocallyEquienergetic {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂]
    (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂) : Prop :=
  Fintype.card V₁ = Fintype.card V₂ ∧ localEnergy G₁ = localEnergy G₂

/-- Paper, §3, **Conjecture 1**: "There exists no simple, undirected, and connected locally
equienergetic graph other than the pair of locally equienergetic graphs `(K_n, C_n)` for odd `n`."

(Preceded by Corollary 2: "There exists no simple, undirected, and connected locally
equienergetic graph of order `n ≤ 10` except the pair `(K_n, C_n)` for odd `n`.")

Formal reading: whenever `G₁` and `G₂` are connected simple graphs which are *not isomorphic*
(a graph is trivially locally equienergetic with itself or with an isomorphic copy, so the
paper's "pairs" are pairs of non-isomorphic graphs) and are locally equienergetic, then their
common order `n` is odd and `{G₁, G₂}` is `{K_n, C_n}` up to isomorphism.  Here `K_n` is the
complete graph `⊤` on `Fin n` and `C_n` is Mathlib's `SimpleGraph.cycleGraph n`. -/
def Conjecture1 : Prop :=
  ∀ (V₁ V₂ : Type) [Fintype V₁] [Fintype V₂] (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂),
    G₁.Connected → G₂.Connected → IsEmpty (G₁ ≃g G₂) → LocallyEquienergetic G₁ G₂ →
      Odd (Fintype.card V₁) ∧
        ((Nonempty (G₁ ≃g (⊤ : SimpleGraph (Fin (Fintype.card V₁)))) ∧
            Nonempty (G₂ ≃g SimpleGraph.cycleGraph (Fintype.card V₁))) ∨
          (Nonempty (G₁ ≃g SimpleGraph.cycleGraph (Fintype.card V₁)) ∧
            Nonempty (G₂ ≃g (⊤ : SimpleGraph (Fin (Fintype.card V₁))))))

/-- A *weaker* form of Conjecture 1 (hence a stronger refutation): in the spirit of the convention
that equienergetic graphs are required to be non-cospectral, consider only pairs that are **not
equienergetic** (in particular non-cospectral and non-isomorphic).  The paper's pairs `(K_n, C_n)`
(`n ≥ 5` odd) are such pairs. -/
def Conjecture1NonEquienergetic : Prop :=
  ∀ (V₁ V₂ : Type) [Fintype V₁] [Fintype V₂] (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂),
    G₁.Connected → G₂.Connected → energy G₁ ≠ energy G₂ → LocallyEquienergetic G₁ G₂ →
      Odd (Fintype.card V₁) ∧
        ((Nonempty (G₁ ≃g (⊤ : SimpleGraph (Fin (Fintype.card V₁)))) ∧
            Nonempty (G₂ ≃g SimpleGraph.cycleGraph (Fintype.card V₁))) ∨
          (Nonempty (G₁ ≃g SimpleGraph.cycleGraph (Fintype.card V₁)) ∧
            Nonempty (G₂ ≃g (⊤ : SimpleGraph (Fin (Fintype.card V₁))))))

/-- Paper, Corollary 2: "There exists no simple, undirected, and connected locally equienergetic
graph of order `n ≤ 10` except the pair `(K_n, C_n)` for odd `n`."  (Same reading as
`Conjecture1`, restricted to order at most 10.) -/
def Corollary2 : Prop :=
  ∀ (V₁ V₂ : Type) [Fintype V₁] [Fintype V₂] (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂),
    Fintype.card V₁ ≤ 10 →
    G₁.Connected → G₂.Connected → IsEmpty (G₁ ≃g G₂) → LocallyEquienergetic G₁ G₂ →
      Odd (Fintype.card V₁) ∧
        ((Nonempty (G₁ ≃g (⊤ : SimpleGraph (Fin (Fintype.card V₁)))) ∧
            Nonempty (G₂ ≃g SimpleGraph.cycleGraph (Fintype.card V₁))) ∨
          (Nonempty (G₁ ≃g SimpleGraph.cycleGraph (Fintype.card V₁)) ∧
            Nonempty (G₂ ≃g (⊤ : SimpleGraph (Fin (Fintype.card V₁))))))

/-- **Main theorem.** Conjecture 1 of Dede–Popat is false. -/
theorem not_conjecture1 : ¬ Conjecture1 := by sorry

/-- Even the restriction of Conjecture 1 to non-equienergetic pairs is false. -/
theorem not_conjecture1NonEquienergetic : ¬ Conjecture1NonEquienergetic := by sorry

/-- The paper's Corollary 2 (its claimed exhaustive result for order `≤ 10`) is false. -/
theorem not_corollary2 : ¬ Corollary2 := by sorry

end DedePopat
