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

/-! ## Proof

**Counterexample.** The `4 × 4` rook's graph `R = K₄ □ K₄` and the Shrikhande graph `S`, both
realised as Cayley graphs on `(ℤ/4)² = Fin 4 × Fin 4`.  They are connected, non-isomorphic (`R`
contains `K₄`, `S` does not) and have the same order 16, which is even; neither is `K₁₆` or `C₁₆`.

Equality `e(R) = e(S)` is certified in two independent ways:

* **Similarity certificate.** Both graphs are vertex-transitive, so `e(G) = 16 (𝓔(G) − 𝓔(G − 0))`.
  An explicit integer matrix `P` with `P Pᵀ = 4 I` and `P A_R = A_S P` shows that `A_R`, `A_S` are
  similar, hence `𝓔(R) = 𝓔(S)`; `P` fixes the vertex `0`, and its restriction to the other 15
  vertices does the same for `R − 0` and `S − 0`.  (`P` comes from a Godsil–McKay switching of `R`
  with respect to a transversal, followed by an isomorphism onto `S`; see `SOLUTION.md`.)
* **Exact values.** From minimal-polynomial identities and traces of powers of the adjacency
  matrices: `𝓔(R) = 𝓔(S) = 36`, `𝓔(R − v) = 𝓔(S − v) = 32`, so `e(R) = e(S) = 64`.

**Stronger counterexample.** The complement `Q` of the Clebsch graph (strongly regular with
parameters `(16, 10, 6, 6)`) has `𝓔(Q) = 40`, `𝓔(Q − v) = 36`, so `e(Q) = 64 = e(R)` although
`𝓔(Q) ≠ 𝓔(R)`: the pair `(R, Q)` is locally equienergetic but not even equienergetic (in particular
not cospectral).  This refutes Conjecture 1 also under the stricter reading which only considers
non-equienergetic pairs (`not_conjecture1NonEquienergetic` below).
-/

open Matrix

section General

/-- For a real symmetric matrix, the sum of the absolute values of the eigenvalues equals the sum
of the absolute values of the roots (with multiplicity) of the characteristic polynomial. -/
lemma sum_abs_eigenvalues_eq {n : Type*} [Fintype n] {_ : DecidableEq n} {A : Matrix n n ℝ}
    (hA : A.IsHermitian) :
    ∑ i, |hA.eigenvalues i| = (A.charpoly.roots.map (fun x : ℝ => |x|)).sum := by
  rw [hA.roots_charpoly_eq_eigenvalues, Multiset.map_map, RCLike.ofReal_real_eq_id,
    Function.id_comp]
  rfl

lemma energy_eq_roots {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    energy G = ((G.adjMatrix ℝ).charpoly.roots.map (fun x : ℝ => |x|)).sum := by
  unfold energy
  rw [sum_abs_eigenvalues_eq]
  congr!

/-- Graphs whose real adjacency matrices have the same characteristic polynomial have the same
energy. -/
lemma energy_eq_of_charpoly_eq {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W]
    [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj]
    [DecidableRel H.Adj] (h : (G.adjMatrix ℝ).charpoly = (H.adjMatrix ℝ).charpoly) :
    energy G = energy H := by
  rw [energy_eq_roots, energy_eq_roots, h]

/-- Energy is an isomorphism invariant. -/
lemma energy_iso {V W : Type*} [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) : energy G = energy H := by
  classical
  apply energy_eq_of_charpoly_eq
  rw [← e.reindex_adjMatrix ℝ, Matrix.charpoly_reindex]

/-- An integer intertwiner `P` with `P Pᵀ = c I` (`c ≠ 0`) and `P A = B P` shows that `A` and `B`
have the same characteristic polynomial over `ℝ`. -/
lemma charpoly_eq_of_intertwiner {n : Type*} [Fintype n] [DecidableEq n]
    (A B P : Matrix n n ℤ) (c : ℤ) (hc : c ≠ 0) (h1 : P * A = B * P)
    (h2 : P * Pᵀ = c • (1 : Matrix n n ℤ)) :
    (A.map (Int.castRingHom ℝ)).charpoly = (B.map (Int.castRingHom ℝ)).charpoly := by
  set f := Int.castRingHom ℝ
  have h1' : P.map f * A.map f = B.map f * P.map f := by
    rw [← Matrix.map_mul, h1, Matrix.map_mul]
  have h2' : P.map f * (P.map f)ᵀ = (c : ℝ) • (1 : Matrix n n ℝ) := by
    rw [← Matrix.transpose_map, ← Matrix.map_mul, h2]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp [f]
  set Q := (c : ℝ)⁻¹ • (P.map f)ᵀ
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hPQ : P.map f * Q = 1 := by
    simp only [Q, Matrix.mul_smul, h2', smul_smul, inv_mul_cancel₀ hc', one_smul]
  have hQP : Q * P.map f = 1 := mul_eq_one_comm.mp hPQ
  have hB : B.map f = P.map f * (A.map f * Q) := by
    rw [← Matrix.mul_assoc, h1', Matrix.mul_assoc, hPQ, Matrix.mul_one]
  rw [hB, Matrix.charpoly_mul_comm, Matrix.mul_assoc, hQP, Matrix.mul_one]

/-- If `f : W ↪ V` has range `s`, then `G.comap f ≃g G.induce s`. -/
noncomputable def isoComapInduce {V W : Type*} (G : SimpleGraph V) (f : W ↪ V) (s : Set V)
    (hf : Set.range f = s) : G.comap f ≃g G.induce s where
  toEquiv := (Equiv.ofInjective f f.injective).trans (Equiv.setCongr hf)
  map_rel_iff' := Iff.rfl

lemma adjMatrix_real {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    G.adjMatrix ℝ = (Int.castRingHom ℝ).mapMatrix (G.adjMatrix ℤ) := by
  ext i j
  by_cases h : G.Adj i j <;> simp [h]

lemma trace_pow_adjMatrix {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ) :
    ((G.adjMatrix ℝ) ^ k).trace = ((((G.adjMatrix ℤ) ^ k).trace : ℤ) : ℝ) := by
  rw [adjMatrix_real, ← map_pow, RingHom.mapMatrix_apply,
    ← AddMonoidHom.map_trace (Int.castRingHom ℝ)]
  rfl

section Spectral

open Polynomial

/-- If `p(A) = 0` and `g` agrees with `|·|` on the real roots of `p`, then the sum of the absolute
values of the eigenvalues of the real symmetric matrix `A` equals `tr g(A)`. -/
lemma sum_abs_eigenvalues_eq_trace {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (p g : ℝ[X]) (hp : aeval A p = 0)
    (hg : ∀ x : ℝ, p.eval x = 0 → |x| = g.eval x) :
    ∑ i, |hA.eigenvalues i| = (aeval A g).trace := by
  have hsa : IsSelfAdjoint A := hA
  have hroot : ∀ i, p.eval (hA.eigenvalues i) = 0 := by
    intro i
    have h0 : cfc p.eval A = cfc (fun _ : ℝ => (0 : ℝ)) A := by
      rw [cfc_polynomial p A, hp, cfc_const_zero]
    exact eqOn_of_cfc_eq_cfc h0 p.continuous.continuousOn continuousOn_const hsa
      (hA.eigenvalues_mem_spectrum_real i)
  calc ∑ i, |hA.eigenvalues i| = ∑ i, g.eval (hA.eigenvalues i) :=
        Finset.sum_congr rfl fun i _ => hg _ (hroot i)
    _ = (aeval A g).trace := by
        rw [← cfc_polynomial g A, Matrix.trace_eq_neg_charpoly_coeff, hA.charpoly_cfc_eq,
          ← Finset.card_univ,
          Polynomial.prod_X_sub_C_coeff_card_pred _ _ Finset.univ_nonempty.card_pos]
        simp

lemma energy_eq_trace {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (p g : ℝ[X]) (hp : aeval (G.adjMatrix ℝ) p = 0)
    (hg : ∀ x : ℝ, p.eval x = 0 → |x| = g.eval x) :
    energy G = (aeval (G.adjMatrix ℝ) g).trace := by
  rw [energy_eq_roots, ← sum_abs_eigenvalues_eq (G.isHermitian_adjMatrix ℝ)]
  exact sum_abs_eigenvalues_eq_trace _ p g hp hg

lemma trace_aeval_cubic {V : Type*} [Fintype V] [DecidableEq V] (A : Matrix V V ℝ)
    (a b c d : ℝ) :
    (aeval A (C a + C b * X + C c * X ^ 2 + C d * X ^ 3)).trace =
      a * Fintype.card V + b * A.trace + c * (A ^ 2).trace + d * (A ^ 3).trace := by
  simp [Algebra.algebraMap_eq_smul_one, Matrix.trace_add, Matrix.trace_smul]

/-- Energy from integer data: if `p(A) = 0` and `g = a + b x + c x² + d x³` agrees with `|·|` on
the roots of `p`, then `𝓔(G) = a n + c tr A² + d tr A³` (as `tr A = 0`). -/
lemma energy_of_data {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (p : ℝ[X]) (a b c d : ℝ) (hp : aeval (G.adjMatrix ℝ) p = 0)
    (hg : ∀ x : ℝ, p.eval x = 0 →
      |x| = (C a + C b * X + C c * X ^ 2 + C d * X ^ 3 : ℝ[X]).eval x)
    (t2 t3 : ℤ) (h2 : ((G.adjMatrix ℤ) ^ 2).trace = t2)
    (h3 : ((G.adjMatrix ℤ) ^ 3).trace = t3) :
    energy G = a * Fintype.card V + c * t2 + d * t3 := by
  rw [energy_eq_trace G p _ hp hg, trace_aeval_cubic, trace_pow_adjMatrix, trace_pow_adjMatrix,
    SimpleGraph.trace_adjMatrix, h2, h3]
  ring

/-- `|x| = 3/2 + x²/8` on the roots `6, 2, -2`. -/
lemma hg_six (x : ℝ) (hx : ((X - C 6) * (X - C 2) * (X + C 2) : ℝ[X]).eval x = 0) :
    |x| = (C (3/2) + C 0 * X + C (1/8) * X ^ 2 + C 0 * X ^ 3 : ℝ[X]).eval x := by
  simp only [eval_mul, eval_sub, eval_add, eval_X, eval_C, eval_pow] at hx ⊢
  rcases mul_eq_zero.mp hx with h | h
  · rcases mul_eq_zero.mp h with h | h
    · rw [show x = 6 by linarith]; norm_num
    · rw [show x = 2 by linarith]; norm_num
  · rw [show x = -2 by linarith]; norm_num

/-- `|x| = 5/3 + x²/12` on the roots `10, 2, -2`. -/
lemma hg_ten (x : ℝ) (hx : ((X - C 10) * (X - C 2) * (X + C 2) : ℝ[X]).eval x = 0) :
    |x| = (C (5/3) + C 0 * X + C (1/12) * X ^ 2 + C 0 * X ^ 3 : ℝ[X]).eval x := by
  simp only [eval_mul, eval_sub, eval_add, eval_X, eval_C, eval_pow] at hx ⊢
  rcases mul_eq_zero.mp hx with h | h
  · rcases mul_eq_zero.mp h with h | h
    · rw [show x = 10 by linarith]; norm_num
    · rw [show x = 2 by linarith]; norm_num
  · rw [show x = -2 by linarith]; norm_num

/-- `|x| = x - (x - 2)(x² - 6x + 2)/18` on the roots of `(x - 2)(x + 2)(x² - 6x + 2)`
(the roots of `x² - 6x + 2` are `3 ± √7 > 0`). -/
lemma hg_six_del (x : ℝ)
    (hx : ((X - C 2) * (X + C 2) * (X ^ 2 - C 6 * X + C 2) : ℝ[X]).eval x = 0) :
    |x| = (C (2/9) + C (2/9) * X + C (4/9) * X ^ 2 + C (-1/18) * X ^ 3 : ℝ[X]).eval x := by
  simp only [eval_mul, eval_sub, eval_add, eval_X, eval_C, eval_pow] at hx ⊢
  rcases mul_eq_zero.mp hx with h | h
  · rcases mul_eq_zero.mp h with h | h
    · rw [show x = 2 by linarith]; norm_num
    · rw [show x = -2 by linarith]; norm_num
  · have hx0 : 0 < x := by nlinarith [sq_nonneg x]
    rw [abs_of_pos hx0]
    linear_combination (1/18 : ℝ) * (x - 2) * h

/-- `|x| = x - (x - 2)(x² - 10x + 6)/30` on the roots of `(x - 2)(x + 2)(x² - 10x + 6)`
(the roots of `x² - 10x + 6` are `5 ± √19 > 0`). -/
lemma hg_ten_del (x : ℝ)
    (hx : ((X - C 2) * (X + C 2) * (X ^ 2 - C 10 * X + C 6) : ℝ[X]).eval x = 0) :
    |x| = (C (2/5) + C (2/15) * X + C (2/5) * X ^ 2 + C (-1/30) * X ^ 3 : ℝ[X]).eval x := by
  simp only [eval_mul, eval_sub, eval_add, eval_X, eval_C, eval_pow] at hx ⊢
  rcases mul_eq_zero.mp hx with h | h
  · rcases mul_eq_zero.mp h with h | h
    · rw [show x = 2 by linarith]; norm_num
    · rw [show x = -2 by linarith]; norm_num
  · have hx0 : 0 < x := by nlinarith [sq_nonneg x]
    rw [abs_of_pos hx0]
    linear_combination (1/30 : ℝ) * (x - 2) * h

end Spectral

end General

section Graphs

/-- `ℤ/4 × ℤ/4`, realised as `Fin 4 × Fin 4`. -/
abbrev V16 := Fin 4 × Fin 4

/-- The Cayley graph on `(ℤ/4)²` with connection set `C`: `x ~ y` iff `x ≠ y` and
`x - y ∈ C ∪ (-C)`. -/
def cay (C : Finset V16) : SimpleGraph V16 :=
  SimpleGraph.fromRel fun x y => x - y ∈ C

instance (C : Finset V16) : DecidableRel (cay C).Adj := fun x y =>
  inferInstanceAs (Decidable (x ≠ y ∧ (x - y ∈ C ∨ y - x ∈ C)))

/-- The `4 × 4` rook's graph `K₄ □ K₄`: distinct vertices are adjacent iff they agree in one
coordinate (see `rook_adj_iff`). -/
def rook : SimpleGraph V16 := cay {(1, 0), (2, 0), (3, 0), (0, 1), (0, 2), (0, 3)}

/-- The Shrikhande graph: the Cayley graph on `(ℤ/4)²` with connection set
`{±(1,0), ±(0,1), ±(1,1)}`. -/
def shrikhande : SimpleGraph V16 := cay {(1, 0), (3, 0), (0, 1), (0, 3), (1, 1), (3, 3)}

/-- The complement of the Clebsch graph, i.e. the (unique) strongly regular graph with parameters
`(16, 10, 6, 6)`, realised as a Cayley graph on `(ℤ/4)²` with connection set
`{(0,±1), (0,2), (±1,0), (2,0), (±1,±1)}`. -/
def clebschCompl : SimpleGraph V16 :=
  cay {(0, 1), (0, 2), (0, 3), (1, 0), (2, 0), (3, 0), (1, 1), (1, 3), (3, 1), (3, 3)}

instance : DecidableRel rook.Adj := inferInstanceAs (DecidableRel (cay _).Adj)
instance : DecidableRel shrikhande.Adj := inferInstanceAs (DecidableRel (cay _).Adj)
instance : DecidableRel clebschCompl.Adj := inferInstanceAs (DecidableRel (cay _).Adj)

lemma rook_adj_iff (x y : V16) : rook.Adj x y ↔ x ≠ y ∧ (x.1 = y.1 ∨ x.2 = y.2) := by
  revert x y
  decide +kernel

/-- Translations are automorphisms of Cayley graphs. -/
def translate (C : Finset V16) (v : V16) : cay C ≃g cay C where
  toEquiv := Equiv.subRight v
  map_rel_iff' := by
    intro x y
    simp [cay, SimpleGraph.fromRel_adj, sub_sub_sub_cancel_right]

lemma energy_delete_eq (C : Finset V16) (v : V16) [Fintype ({v}ᶜ : Set V16)]
    [Fintype ({0}ᶜ : Set V16)] :
    energy ((cay C).induce ({v}ᶜ : Set V16)) = energy ((cay C).induce ({0}ᶜ : Set V16)) := by
  have hb : Set.BijOn (translate C v) ({v}ᶜ : Set V16) ({0}ᶜ : Set V16) := by
    refine ⟨fun x hx => ?_, (translate C v).injective.injOn, fun y hy => ?_⟩
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx ⊢
      simpa [translate, sub_eq_zero] using hx
    · refine ⟨y + v, ?_, ?_⟩
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hy ⊢
        simpa using hy
      · simp [translate]
  exact energy_iso ((translate C v).induce hb)

/-- Local energy of a Cayley graph on `(ℤ/4)²` (vertex-transitivity). -/
lemma localEnergy_cay (C : Finset V16) :
    localEnergy (cay C) =
      16 * (energy (cay C) - energy ((cay C).induce ({0}ᶜ : Set V16))) := by
  classical
  unfold localEnergy localVertexEnergy
  simp only [energy_delete_eq C]
  simp [mul_sub]

/-- Connectivity from "every vertex is within distance 2 of `0`". -/
lemma connected_of_dist_two {G : SimpleGraph V16}
    (h : ∀ u : V16, u = 0 ∨ G.Adj u 0 ∨ ∃ w, G.Adj u w ∧ G.Adj w 0) : G.Connected := by
  have hr : ∀ u, G.Reachable u 0 := by
    intro u
    rcases h u with rfl | h1 | ⟨w, h1, h2⟩
    · rfl
    · exact h1.reachable
    · exact h1.reachable.trans h2.reachable
  exact ⟨fun u v => (hr u).trans (hr v).symm⟩

lemma rook_connected : rook.Connected :=
  connected_of_dist_two (by decide +kernel)

lemma shrikhande_connected : shrikhande.Connected :=
  connected_of_dist_two (by decide +kernel)

lemma clebschCompl_connected : clebschCompl.Connected :=
  connected_of_dist_two (by decide +kernel)

/-- The Shrikhande graph contains no `K₄`. -/
lemma shrikhande_K4_free : ∀ a b c d : V16, ¬ (shrikhande.Adj a b ∧ shrikhande.Adj a c ∧
    shrikhande.Adj a d ∧ shrikhande.Adj b c ∧ shrikhande.Adj b d ∧ shrikhande.Adj c d) := by
  decide +kernel

/-- The rook's graph and the Shrikhande graph are not isomorphic: a row of the rook's graph is a
`K₄`. -/
lemma rook_not_iso_shrikhande : IsEmpty (rook ≃g shrikhande) := by
  refine ⟨fun f => ?_⟩
  have h : ∀ x y : V16, rook.Adj x y → shrikhande.Adj (f x) (f y) := fun x y hxy =>
    f.map_adj_iff.mpr hxy
  exact shrikhande_K4_free (f (0, 0)) (f (0, 1)) (f (0, 2)) (f (0, 3))
    ⟨h _ _ (by decide +kernel), h _ _ (by decide +kernel), h _ _ (by decide +kernel),
      h _ _ (by decide +kernel), h _ _ (by decide +kernel), h _ _ (by decide +kernel)⟩

/-- Enumeration of the vertices, `(a, b) ↦ 4a + b`. -/
def enc : V16 ≃ Fin 16 := finProdFinEquiv

/-- The embedding `Fin 15 ↪ V16`, `i ↦ enc⁻¹ (i + 1)`, whose range is `{0}ᶜ`. -/
def emb15 : Fin 15 ↪ V16 := ⟨fun i => enc.symm i.succ, fun i j h => by simpa using h⟩

@[simp] lemma emb15_apply (i : Fin 15) : emb15 i = enc.symm i.succ := rfl

lemma range_emb15 : Set.range emb15 = ({0}ᶜ : Set V16) := by
  ext x
  simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
  revert x
  decide +kernel

/-- `G − 0` is isomorphic to the graph on `Fin 15` pulled back along `emb15`. -/
lemma energy_induce_eq_comap (C : Finset V16) [Fintype ({0}ᶜ : Set V16)] :
    energy ((cay C).induce ({0}ᶜ : Set V16)) = energy ((cay C).comap emb15) :=
  (energy_iso (isoComapInduce (cay C) emb15 _ range_emb15)).symm

end Graphs

/-! ### First certificate: `R` and `S` (and `R − 0`, `S − 0`) have similar adjacency matrices -/

section Certificate

/-- The certificate: `P * A_rook = A_shrikhande * P` and `P * Pᵀ = 4`. -/
def Pcert : Matrix (Fin 16) (Fin 16) ℤ :=
  !![2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1;
    0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0;
    0, 1, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1]

/-- Integer adjacency matrix of `G` in the enumeration `enc`. -/
def adj16 (G : SimpleGraph V16) [DecidableRel G.Adj] : Matrix (Fin 16) (Fin 16) ℤ :=
  Matrix.of fun i j => if G.Adj (enc.symm i) (enc.symm j) then 1 else 0

lemma cert16_intertwine : Pcert * adj16 rook = adj16 shrikhande * Pcert := by decide +kernel
lemma cert16_orth : Pcert * Pcertᵀ = (4 : ℤ) • (1 : Matrix (Fin 16) (Fin 16) ℤ) := by
  decide +kernel
lemma cert15_intertwine : Pcert.submatrix Fin.succ Fin.succ * (rook.comap emb15).adjMatrix ℤ =
    (shrikhande.comap emb15).adjMatrix ℤ * Pcert.submatrix Fin.succ Fin.succ := by
  decide +kernel
lemma cert15_orth : Pcert.submatrix Fin.succ Fin.succ * (Pcert.submatrix Fin.succ Fin.succ)ᵀ =
    (4 : ℤ) • (1 : Matrix (Fin 15) (Fin 15) ℤ) := by decide +kernel

lemma adj16_eq (G : SimpleGraph V16) [DecidableRel G.Adj] :
    (G.adjMatrix ℝ).charpoly = ((adj16 G).map (Int.castRingHom ℝ)).charpoly := by
  rw [← Matrix.charpoly_reindex enc]
  congr 1
  ext i j
  by_cases h : G.Adj (enc.symm i) (enc.symm j) <;> simp [adj16, h]

lemma energy_rook_eq : energy rook = energy shrikhande := by
  apply energy_eq_of_charpoly_eq
  rw [adj16_eq, adj16_eq]
  exact charpoly_eq_of_intertwiner _ _ _ 4 (by norm_num) cert16_intertwine cert16_orth

lemma energy_rook_del_eq : energy (rook.comap emb15) = energy (shrikhande.comap emb15) := by
  apply energy_eq_of_charpoly_eq
  rw [adjMatrix_real, adjMatrix_real]
  exact charpoly_eq_of_intertwiner _ _ _ 4 (by norm_num) cert15_intertwine cert15_orth

theorem localEnergy_rook_eq_shrikhande : localEnergy rook = localEnergy shrikhande := by
  rw [rook, shrikhande, localEnergy_cay, localEnergy_cay, energy_induce_eq_comap,
    energy_induce_eq_comap, ← rook, ← shrikhande, energy_rook_eq, energy_rook_del_eq]

end Certificate

/-! ### Second certificate: exact energies and local energies -/

section ExactValues

open Polynomial

theorem energy_rook_val : energy rook = 36 := by
  rw [energy_of_data rook _ (3/2) 0 (1/8) 0 ?_ hg_six 96 192 (by decide +kernel)
    (by decide +kernel)]
  · simp; norm_num
  · have h : (rook.adjMatrix ℤ - 6) * (rook.adjMatrix ℤ - 2) * (rook.adjMatrix ℤ + 2) = 0 := by
      decide +kernel
    have := congrArg (Int.castRingHom ℝ).mapMatrix h
    rw [adjMatrix_real]
    simpa [map_mul, map_sub, map_add, map_ofNat] using this

theorem energy_shrikhande_val : energy shrikhande = 36 := by
  rw [energy_of_data shrikhande _ (3/2) 0 (1/8) 0 ?_ hg_six 96 192 (by decide +kernel)
    (by decide +kernel)]
  · simp; norm_num
  · have h : (shrikhande.adjMatrix ℤ - 6) * (shrikhande.adjMatrix ℤ - 2) *
        (shrikhande.adjMatrix ℤ + 2) = 0 := by
      decide +kernel
    have := congrArg (Int.castRingHom ℝ).mapMatrix h
    rw [adjMatrix_real]
    simpa [map_mul, map_sub, map_add, map_ofNat] using this

theorem energy_clebschCompl_val : energy clebschCompl = 40 := by
  rw [energy_of_data clebschCompl _ (5/3) 0 (1/12) 0 ?_ hg_ten 160 960 (by decide +kernel)
    (by decide +kernel)]
  · simp; norm_num
  · have h : (clebschCompl.adjMatrix ℤ - 10) * (clebschCompl.adjMatrix ℤ - 2) *
        (clebschCompl.adjMatrix ℤ + 2) = 0 := by
      decide +kernel
    have := congrArg (Int.castRingHom ℝ).mapMatrix h
    rw [adjMatrix_real]
    simpa [map_mul, map_sub, map_add, map_ofNat] using this

theorem energy_rook_del_val : energy (rook.comap emb15) = 32 := by
  rw [energy_of_data (rook.comap emb15) _ (2/9) (2/9) (4/9) (-1/18) ?_ hg_six_del 84 156
    (by decide +kernel) (by decide +kernel)]
  · simp; norm_num
  · have h : ((rook.comap emb15).adjMatrix ℤ - 2) * ((rook.comap emb15).adjMatrix ℤ + 2) *
        ((rook.comap emb15).adjMatrix ℤ ^ 2 - 6 * (rook.comap emb15).adjMatrix ℤ + 2) = 0 := by
      decide +kernel
    have := congrArg (Int.castRingHom ℝ).mapMatrix h
    rw [adjMatrix_real]
    simpa [map_mul, map_sub, map_add, map_pow, map_ofNat] using this

theorem energy_shrikhande_del_val : energy (shrikhande.comap emb15) = 32 := by
  rw [energy_of_data (shrikhande.comap emb15) _ (2/9) (2/9) (4/9) (-1/18) ?_ hg_six_del 84 156
    (by decide +kernel) (by decide +kernel)]
  · simp; norm_num
  · have h : ((shrikhande.comap emb15).adjMatrix ℤ - 2) *
        ((shrikhande.comap emb15).adjMatrix ℤ + 2) *
        ((shrikhande.comap emb15).adjMatrix ℤ ^ 2 - 6 * (shrikhande.comap emb15).adjMatrix ℤ +
          2) = 0 := by
      decide +kernel
    have := congrArg (Int.castRingHom ℝ).mapMatrix h
    rw [adjMatrix_real]
    simpa [map_mul, map_sub, map_add, map_pow, map_ofNat] using this

theorem energy_clebschCompl_del_val : energy (clebschCompl.comap emb15) = 36 := by
  rw [energy_of_data (clebschCompl.comap emb15) _ (2/5) (2/15) (2/5) (-1/30) ?_ hg_ten_del 140
    780 (by decide +kernel) (by decide +kernel)]
  · simp; norm_num
  · have h : ((clebschCompl.comap emb15).adjMatrix ℤ - 2) *
        ((clebschCompl.comap emb15).adjMatrix ℤ + 2) *
        ((clebschCompl.comap emb15).adjMatrix ℤ ^ 2 -
          10 * (clebschCompl.comap emb15).adjMatrix ℤ + 6) = 0 := by
      decide +kernel
    have := congrArg (Int.castRingHom ℝ).mapMatrix h
    rw [adjMatrix_real]
    simpa [map_mul, map_sub, map_add, map_pow, map_ofNat] using this

theorem localEnergy_rook_val : localEnergy rook = 64 := by
  rw [rook, localEnergy_cay, energy_induce_eq_comap, ← rook, energy_rook_val, energy_rook_del_val]
  norm_num

theorem localEnergy_shrikhande_val : localEnergy shrikhande = 64 := by
  rw [shrikhande, localEnergy_cay, energy_induce_eq_comap, ← shrikhande, energy_shrikhande_val,
    energy_shrikhande_del_val]
  norm_num

theorem localEnergy_clebschCompl_val : localEnergy clebschCompl = 64 := by
  rw [clebschCompl, localEnergy_cay, energy_induce_eq_comap, ← clebschCompl,
    energy_clebschCompl_val, energy_clebschCompl_del_val]
  norm_num

end ExactValues

/-! ### None of the graphs is `K₁₆` or `C₁₆` (independently of the parity of 16) -/

section NotKC

/-- `C₁₆` (Mathlib's `cycleGraph 16`) is triangle-free. -/
lemma cycleGraph16_triangle_free : ∀ a b c : Fin 16, ¬ ((SimpleGraph.cycleGraph 16).Adj a b ∧
    (SimpleGraph.cycleGraph 16).Adj b c ∧ (SimpleGraph.cycleGraph 16).Adj a c) := by
  decide +kernel

lemma not_iso_top_of_nonadj {G : SimpleGraph V16} {x y : V16} (hxy : x ≠ y) (hn : ¬ G.Adj x y) :
    IsEmpty (G ≃g (⊤ : SimpleGraph (Fin 16))) :=
  ⟨fun f => hn (f.map_adj_iff.mp (by simpa using f.injective.ne hxy))⟩

lemma not_iso_cycle_of_triangle {G : SimpleGraph V16} {x y z : V16} (hxy : G.Adj x y)
    (hyz : G.Adj y z) (hxz : G.Adj x z) : IsEmpty (G ≃g SimpleGraph.cycleGraph 16) :=
  ⟨fun f => cycleGraph16_triangle_free (f x) (f y) (f z)
    ⟨f.map_adj_iff.mpr hxy, f.map_adj_iff.mpr hyz, f.map_adj_iff.mpr hxz⟩⟩

/-- Neither of the three graphs is isomorphic to `K₁₆` or to `C₁₆`. -/
theorem not_complete_not_cycle :
    IsEmpty (rook ≃g (⊤ : SimpleGraph (Fin 16))) ∧
      IsEmpty (rook ≃g SimpleGraph.cycleGraph 16) ∧
      IsEmpty (shrikhande ≃g (⊤ : SimpleGraph (Fin 16))) ∧
      IsEmpty (shrikhande ≃g SimpleGraph.cycleGraph 16) ∧
      IsEmpty (clebschCompl ≃g (⊤ : SimpleGraph (Fin 16))) ∧
      IsEmpty (clebschCompl ≃g SimpleGraph.cycleGraph 16) :=
  ⟨not_iso_top_of_nonadj (x := (0, 0)) (y := (1, 1)) (by decide) (by decide +kernel),
    not_iso_cycle_of_triangle (x := (0, 0)) (y := (0, 1)) (z := (0, 2))
      (by decide +kernel) (by decide +kernel) (by decide +kernel),
    not_iso_top_of_nonadj (x := (0, 0)) (y := (2, 2)) (by decide) (by decide +kernel),
    not_iso_cycle_of_triangle (x := (0, 0)) (y := (1, 0)) (z := (1, 1))
      (by decide +kernel) (by decide +kernel) (by decide +kernel),
    not_iso_top_of_nonadj (x := (0, 0)) (y := (2, 2)) (by decide) (by decide +kernel),
    not_iso_cycle_of_triangle (x := (0, 0)) (y := (0, 1)) (z := (0, 2))
      (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩

lemma card_V16 : Fintype.card V16 = 16 := by simp

lemma not_odd_card_V16 : ¬ Odd (Fintype.card V16) := by
  rw [card_V16]; decide

end NotKC

/-! ### Summary -/

/-- The rook's graph `K₄ □ K₄` and the Shrikhande graph are connected, non-isomorphic, of the same
(even) order 16, locally equienergetic with `e = 64`, equienergetic with `𝓔 = 36`, and neither of
them is isomorphic to `K₁₆` or `C₁₆`. -/
theorem rook_shrikhande_counterexample :
    rook.Connected ∧ shrikhande.Connected ∧ IsEmpty (rook ≃g shrikhande) ∧
      LocallyEquienergetic rook shrikhande ∧ ¬ Odd (Fintype.card V16) ∧
      localEnergy rook = 64 ∧ localEnergy shrikhande = 64 ∧
      energy rook = 36 ∧ energy shrikhande = 36 :=
  ⟨rook_connected, shrikhande_connected, rook_not_iso_shrikhande,
    ⟨rfl, localEnergy_rook_eq_shrikhande⟩, not_odd_card_V16, localEnergy_rook_val,
    localEnergy_shrikhande_val, energy_rook_val, energy_shrikhande_val⟩

/-- The rook's graph and the complement of the Clebsch graph are connected, of the same (even)
order 16, locally equienergetic (`e = 64`), but **not equienergetic** (`𝓔 = 36` vs `𝓔 = 40`), hence
not cospectral and not isomorphic. -/
theorem rook_clebschCompl_counterexample :
    rook.Connected ∧ clebschCompl.Connected ∧ energy rook ≠ energy clebschCompl ∧
      IsEmpty (rook ≃g clebschCompl) ∧ LocallyEquienergetic rook clebschCompl ∧
      ¬ Odd (Fintype.card V16) ∧ localEnergy clebschCompl = 64 ∧ energy clebschCompl = 40 := by
  have hE : energy rook ≠ energy clebschCompl := by
    rw [energy_rook_val, energy_clebschCompl_val]; norm_num
  exact ⟨rook_connected, clebschCompl_connected, hE, ⟨fun f => hE (energy_iso f)⟩,
    ⟨rfl, by rw [localEnergy_rook_val, localEnergy_clebschCompl_val]⟩, not_odd_card_V16,
    localEnergy_clebschCompl_val, energy_clebschCompl_val⟩

/-- Conjecture 1 implies its restriction to non-equienergetic pairs. -/
theorem conjecture1_imp_nonEquienergetic : Conjecture1 → Conjecture1NonEquienergetic := by
  intro h V₁ V₂ _ _ G₁ G₂ h₁ h₂ hE hle
  exact h V₁ V₂ G₁ G₂ h₁ h₂ ⟨fun f => hE (energy_iso f)⟩ hle

/-- Even the restriction of Conjecture 1 to non-equienergetic pairs is false. -/
theorem not_conjecture1NonEquienergetic : ¬ Conjecture1NonEquienergetic := by
  intro h
  obtain ⟨hR, hQ, hE, -, hle, hodd, -⟩ := rook_clebschCompl_counterexample
  exact hodd (h V16 V16 rook clebschCompl hR hQ hE hle).1

/-- **Main theorem.** Conjecture 1 of Dede–Popat is false. -/
theorem not_conjecture1 : ¬ Conjecture1 := by
  intro h
  obtain ⟨hR, hS, hiso, hle, hodd, -⟩ := rook_shrikhande_counterexample
  exact hodd (h V16 V16 rook shrikhande hR hS hiso hle).1

/-! ## An order-10 counterexample

This file refutes Conjecture 1 with a pair of connected graphs on 10 vertices; it also refutes
the paper's Corollary 2 (the claimed exhaustive classification for order `n ≤ 10`).

* `G` (graph6 `I?qa``kWo`) and `H` (graph6 `ICOeeOwFG`) have 16 edges each, the same degree
  sequence, the same characteristic polynomial and the same multiset of vertex-deleted
  characteristic polynomials.
* `G` has two disjoint Godsil–McKay switching sets `C₁ = {0,6,7,8}` and `C₂ = {3,4,5,9}`;
  switching on either gives a graph isomorphic to `H`.  This yields integer matrices `P₁`, `P₂`
  with `Pᵢ A_G = A_H Pᵢ` and `Pᵢ Pᵢᵀ = 4 I`.  For `v ∉ Cᵢ`, deleting column `v` and row `π v`
  of `Pᵢ` gives a `9 × 9` certificate `P A_{G-v} = A_{H-π v} P`, `P Pᵀ = 4 I`, where `π` is an
  explicit permutation of the vertices.  Hence `𝓔(G) = 𝓔(H)` and `𝓔(G - v) = 𝓔(H - π v)` for
  every `v`, so `e(G) = e(H)`.
* `H` contains two triangles sharing an edge (on `{8, 9, 3, 4}`), `G` does not; so `G ≇ H`.
* `n = 10` is even, so the pair is not `(K_n, C_n)` with `n` odd.

The certificates are produced (and re-verified in exact arithmetic) by
`order10/make_certificates.py`; here they are re-checked by the kernel (`decide +kernel`).
-/

section General10

/-- Local energies agree if the energies agree and the vertex-deleted energies agree along a
bijection of the vertex sets. -/
lemma localEnergy_eq_of_deck {V W : Type*} [Fintype V] [Fintype W] (G : SimpleGraph V)
    (H : SimpleGraph W) (e : V ≃ W) (h₀ : energy G = energy H)
    (h₁ : ∀ (v : V) [Fintype ({v}ᶜ : Set V)] [Fintype ({e v}ᶜ : Set W)],
      energy (G.induce ({v}ᶜ : Set V)) = energy (H.induce ({e v}ᶜ : Set W))) :
    localEnergy G = localEnergy H := by
  classical
  unfold localEnergy localVertexEnergy
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [h₀, h₁ v]

/-- `G - v` is isomorphic to the graph on `Fin n` pulled back along `Fin.succAbove v`. -/
lemma energy_induce_eq_comap_succAbove {n : ℕ} (G : SimpleGraph (Fin (n + 1))) (v : Fin (n + 1))
    [Fintype ({v}ᶜ : Set (Fin (n + 1)))] :
    energy (G.induce ({v}ᶜ : Set (Fin (n + 1)))) = energy (G.comap (Fin.succAboveEmb v)) :=
  (energy_iso (isoComapInduce G (Fin.succAboveEmb v) _ (Fin.range_succAbove v))).symm

/-- Connectivity from a parent function whose iterates reach the root `r`. -/
lemma connected_of_parent {V : Type*} [Nonempty V] {G : SimpleGraph V} (r : V) (par : V → V)
    (k : ℕ) (hpar : ∀ u, u = r ∨ G.Adj u (par u)) (hk : ∀ u, par^[k] u = r) : G.Connected := by
  have key : ∀ (m : ℕ) (u : V), par^[m] u = r → G.Reachable u r := by
    intro m
    induction m with
    | zero => intro u h; rw [Function.iterate_zero, id] at h; rw [h]
    | succ m ih =>
      intro u h
      rw [Function.iterate_succ_apply] at h
      rcases hpar u with rfl | hadj
      · rfl
      · exact hadj.reachable.trans (ih _ h)
  exact ⟨fun u v => (key k u (hk u)).trans (key k v (hk v)).symm⟩

end General10

section Order10

/-- The relation "`(i, j)` is in the edge list `E`" on `Fin 10`. -/
def edgeRel (E : List (ℕ × ℕ)) (i j : Fin 10) : Prop := (i.val, j.val) ∈ E

instance (E : List (ℕ × ℕ)) (i j : Fin 10) : Decidable (edgeRel E i j) :=
  inferInstanceAs (Decidable ((i.val, j.val) ∈ E))

/-- The simple graph on `Fin 10` with edge list `E`. -/
def graphOf (E : List (ℕ × ℕ)) : SimpleGraph (Fin 10) := SimpleGraph.fromRel (edgeRel E)

instance (E : List (ℕ × ℕ)) : DecidableRel (graphOf E).Adj := fun i j =>
  inferInstanceAs (Decidable (i ≠ j ∧ (edgeRel E i j ∨ edgeRel E j i)))

/-- `G` = graph6 `I?qa``kWo`. -/
def G10 : SimpleGraph (Fin 10) :=
  graphOf [(0, 4), (0, 5), (1, 4), (1, 6), (1, 8), (1, 9), (2, 5), (2, 7), (2, 8), (2, 9),
    (3, 6), (3, 7), (4, 8), (5, 8), (6, 9), (7, 9)]

/-- `H` = graph6 `ICOeeOwFG`. -/
def H10 : SimpleGraph (Fin 10) :=
  graphOf [(0, 3), (0, 6), (0, 7), (1, 4), (1, 6), (1, 7), (2, 5), (2, 8), (3, 6), (3, 8),
    (3, 9), (4, 7), (4, 8), (4, 9), (5, 9), (8, 9)]

instance : DecidableRel G10.Adj := inferInstanceAs (DecidableRel (graphOf _).Adj)
instance : DecidableRel H10.Adj := inferInstanceAs (DecidableRel (graphOf _).Adj)

lemma G10_connected : G10.Connected :=
  connected_of_parent 0 ![0, 4, 5, 6, 0, 0, 1, 2, 4, 1] 9 (by decide +kernel) (by decide +kernel)

lemma H10_connected : H10.Connected :=
  connected_of_parent 0 ![0, 6, 8, 0, 7, 9, 0, 0, 3, 3] 9 (by decide +kernel) (by decide +kernel)

/-- `G` contains no two triangles sharing an edge. -/
lemma G10_diamond_free : ∀ a b c d : Fin 10, ¬ (c ≠ d ∧ G10.Adj a b ∧ G10.Adj a c ∧
    G10.Adj b c ∧ G10.Adj a d ∧ G10.Adj b d) := by
  decide +kernel

/-- `G ≇ H`: the triangles `{8, 9, 3}` and `{8, 9, 4}` of `H` share the edge `{8, 9}`. -/
lemma G10_not_iso_H10 : IsEmpty (G10 ≃g H10) := by
  refine ⟨fun f => ?_⟩
  have h : ∀ x y : Fin 10, H10.Adj x y → G10.Adj (f.symm x) (f.symm y) := fun x y hxy =>
    f.symm.map_adj_iff.mpr hxy
  exact G10_diamond_free (f.symm 8) (f.symm 9) (f.symm 3) (f.symm 4)
    ⟨f.symm.injective.ne (by decide), h _ _ (by decide +kernel), h _ _ (by decide +kernel),
      h _ _ (by decide +kernel), h _ _ (by decide +kernel), h _ _ (by decide +kernel)⟩

/-- `P₁ = Π_{σ₁} (2 Q_{C₁})`: Godsil–McKay switching on `C₁ = {0,6,7,8}` composed with an
isomorphism onto `H`. -/
def P1 : Matrix (Fin 10) (Fin 10) ℤ :=
  !![0, 0, 0, 0, 2, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 2, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 1, 1, -1, 0;
    0, 2, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 2, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 2, 0, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 1, -1, 1, 0;
    1, 0, 0, 0, 0, 0, -1, 1, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 2;
    -1, 0, 0, 0, 0, 0, 1, 1, 1, 0]

/-- `P₂ = Π_{σ₂} (2 Q_{C₂})`: Godsil–McKay switching on `C₂ = {3,4,5,9}` composed with an
isomorphism onto `H`. -/
def P2 : Matrix (Fin 10) (Fin 10) ℤ :=
  !![0, 0, 0, 1, -1, 1, 0, 0, 0, 1;
    0, 0, 0, 1, 1, -1, 0, 0, 0, 1;
    2, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 2, 0, 0, 0, 0, 0, 0, 0;
    0, 2, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 1, 1, 0, 0, 0, -1;
    0, 0, 0, 0, 0, 0, 0, 2, 0, 0;
    0, 0, 0, 0, 0, 0, 2, 0, 0, 0;
    0, 0, 0, -1, 1, 1, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 2, 0]

/-- The deck bijection `π : V(G) → V(H)`: `𝓔(G - v) = 𝓔(H - π v)`. -/
def π10 : Fin 10 ≃ Fin 10 where
  toFun := ![2, 3, 4, 5, 0, 1, 7, 6, 9, 8]
  invFun := ![4, 5, 0, 1, 2, 3, 7, 6, 9, 8]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

/-- Which switching certificate is used at `v` (`P₂` for `v ∈ C₁`, `P₁` otherwise). -/
def certOf : Fin 10 → Matrix (Fin 10) (Fin 10) ℤ := ![P2, P1, P1, P1, P1, P1, P2, P2, P2, P1]

/-- The `9 × 9` certificate at `v`: delete row `π v` and column `v`. -/
def certDel (v : Fin 10) : Matrix (Fin 9) (Fin 9) ℤ :=
  (certOf v).submatrix (Fin.succAbove (π10 v)) (Fin.succAbove v)

lemma cert_full : P1 * G10.adjMatrix ℤ = H10.adjMatrix ℤ * P1 ∧
    P1 * P1ᵀ = (4 : ℤ) • (1 : Matrix (Fin 10) (Fin 10) ℤ) := by
  decide +kernel

lemma cert_del : ∀ v : Fin 10,
    certDel v * (G10.comap (Fin.succAboveEmb v)).adjMatrix ℤ =
        (H10.comap (Fin.succAboveEmb (π10 v))).adjMatrix ℤ * certDel v ∧
      certDel v * (certDel v)ᵀ = (4 : ℤ) • (1 : Matrix (Fin 9) (Fin 9) ℤ) := by
  decide +kernel

lemma energy_G10_eq_H10 : energy G10 = energy H10 := by
  apply energy_eq_of_charpoly_eq
  rw [adjMatrix_real, adjMatrix_real]
  exact charpoly_eq_of_intertwiner _ _ _ 4 (by norm_num) cert_full.1 cert_full.2

lemma energy_del_eq (v : Fin 10) :
    energy (G10.comap (Fin.succAboveEmb v)) = energy (H10.comap (Fin.succAboveEmb (π10 v))) := by
  apply energy_eq_of_charpoly_eq
  rw [adjMatrix_real, adjMatrix_real]
  exact charpoly_eq_of_intertwiner _ _ _ 4 (by norm_num) (cert_del v).1 (cert_del v).2

theorem localEnergy_G10_eq_H10 : localEnergy G10 = localEnergy H10 :=
  localEnergy_eq_of_deck G10 H10 π10 energy_G10_eq_H10 fun v _ _ => by
    rw [energy_induce_eq_comap_succAbove G10 v, energy_induce_eq_comap_succAbove H10 (π10 v)]
    exact energy_del_eq v

/-- **The order-10 counterexample.** `G` and `H` are connected, not isomorphic, and have equal
local energy. -/
theorem order10_counterexample :
    G10.Connected ∧ H10.Connected ∧ IsEmpty (G10 ≃g H10) ∧ localEnergy G10 = localEnergy H10 :=
  ⟨G10_connected, H10_connected, G10_not_iso_H10, localEnergy_G10_eq_H10⟩

end Order10

/-- Conjecture 1 is false, already for order 10 (contradicting also the paper's Corollary 2). -/
theorem not_conjecture1_order10 : ¬ Conjecture1 := by
  intro h
  obtain ⟨hG, hH, hiso, hle⟩ := order10_counterexample
  have hodd := (h (Fin 10) (Fin 10) G10 H10 hG hH hiso ⟨rfl, hle⟩).1
  rw [Fintype.card_fin] at hodd
  exact absurd hodd (by decide)

/-- The paper's Corollary 2 (its claimed exhaustive result for order `≤ 10`) is false. -/
theorem not_corollary2 : ¬ Corollary2 := by
  intro h
  obtain ⟨hG, hH, hiso, hle⟩ := order10_counterexample
  have hodd := (h (Fin 10) (Fin 10) G10 H10 (by simp) hG hH hiso ⟨rfl, hle⟩).1
  rw [Fintype.card_fin] at hodd
  exact absurd hodd (by decide)

end DedePopat
