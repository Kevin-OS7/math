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

theorem depthSum_as_map (T : BTree) :
    depthSum T = ((leafDepths T).map (fun (d : ℕ) => (d : ℤ))).sum := by
  simp [depthSum]
theorem depthSquareSum_as_map (T : BTree) :
    depthSquareSum T = ((leafDepths T).map (fun (d : ℕ) => (d : ℤ)^2)).sum := by
  simp [depthSquareSum]

-- This file develops a disproof; the frozen positive statement remains unchanged.

@[simp] theorem leafCount_leaf : leafCount .leaf = 1 := by simp [leafCount, leafDepths]
@[simp] theorem leafCount_fork (l r : BTree) :
    leafCount (.fork l r) = leafCount l + leafCount r := by
  simp [leafCount, leafDepths]

theorem leafCount_pos (T : BTree) : 0 < leafCount T := by
  induction T with
  | leaf => simp
  | fork l r hl hr => simp only [leafCount_fork]; omega

@[simp] theorem depthSum_leaf : depthSum .leaf = 0 := by simp [depthSum, leafDepths]
@[simp] theorem depthSquareSum_leaf : depthSquareSum .leaf = 0 := by
  simp [depthSquareSum, leafDepths]

theorem sum_shift (s : Multiset ℕ) :
    (s.map (fun (d : ℕ) => ((d + 1 : ℕ) : ℤ))).sum =
      (s.map (fun (d : ℕ) => (d : ℤ))).sum + s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih => simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, Nat.cast_add, Nat.cast_one] at *; omega

theorem square_shift (s : Multiset ℕ) :
    (s.map (fun (d : ℕ) => ((d + 1 : ℕ) : ℤ)^2)).sum =
      (s.map (fun (d : ℕ) => (d : ℤ)^2)).sum +
        2 * (s.map (fun (d : ℕ) => (d : ℤ))).sum + s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, Nat.cast_add, Nat.cast_one] at *
    nlinarith

@[simp] theorem depthSum_fork (l r : BTree) :
    depthSum (.fork l r) = depthSum l + depthSum r + leafCount l + leafCount r := by
  simp only [depthSum_as_map, leafDepths, Multiset.map_map]
  change ((leafDepths l + leafDepths r).map (fun (d : ℕ) => ((d+1:ℕ):ℤ))).sum = _
  rw [sum_shift]
  simp [leafCount, add_assoc]

@[simp] theorem depthSquareSum_fork (l r : BTree) :
    depthSquareSum (.fork l r) = depthSquareSum l + depthSquareSum r +
      2 * depthSum l + 2 * depthSum r + leafCount l + leafCount r := by
  simp only [depthSquareSum_as_map, leafDepths, Multiset.map_map]
  change ((leafDepths l + leafDepths r).map (fun (d : ℕ) => ((d+1:ℕ):ℤ)^2)).sum = _
  rw [square_shift]
  simp [leafCount, depthSum]
  ring

theorem sum_nonneg (T : BTree) : 0 ≤ depthSum T := by
  induction T with
  | leaf => simp
  | fork l r hl hr => simp only [depthSum_fork]; positivity

theorem sum_lower (T : BTree) : 2 * ((leafCount T : ℤ) - 1) ≤ depthSum T := by
  induction T with
  | leaf => simp
  | fork l r hl hr =>
    have h1 := leafCount_pos l
    have h2 := leafCount_pos r
    simp only [depthSum_fork, leafCount_fork, Nat.cast_add]
    omega

theorem square_ge_sum (T : BTree) : depthSum T ≤ depthSquareSum T := by
  simp only [depthSum_as_map, depthSquareSum_as_map]
  apply Multiset.sum_map_le_sum_map _ _
  intro d hd
  have : (d : ℤ) ≤ (d : ℤ)^2 := by nlinarith [sq_nonneg ((d : ℤ)-1)]
  exact this

def E (k : ℕ) (T : BTree) : ℤ :=
  ((leafDepths T).map (fun (d : ℕ) => (k : ℤ) - d)).sum
def R (k : ℕ) (T : BTree) : ℤ :=
  ((leafDepths T).map (fun (d : ℕ) => ((k : ℤ) - d)^2)).sum

theorem centered_identities (k : ℕ) (T : BTree) :
    E k T = (leafCount T : ℤ) * k - depthSum T ∧
    R k T = depthSquareSum T - 2 * k * depthSum T + (leafCount T : ℤ) * k^2 := by
  simp only [depthSum_as_map, depthSquareSum_as_map]
  unfold E R leafCount
  induction leafDepths T using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, Nat.cast_add, Nat.cast_one]
    constructor <;> nlinarith [ih.1, ih.2]

theorem centered_objective (k : ℕ) (T : BTree) :
    (leafCount T : ℤ) * R k T - E k T ^ 2 = depthObjective T := by
  rw [(centered_identities k T).1, (centered_identities k T).2]
  unfold depthObjective
  ring

theorem abs_E_le_R (k : ℕ) (T : BTree) : |E k T| ≤ R k T := by
  unfold E R
  apply le_trans Multiset.abs_sum_le_sum_abs
  rw [Multiset.map_map]
  apply Multiset.sum_map_le_sum_map _ _
  intro d hd
  change |(k : ℤ) - d| ≤ ((k : ℤ) - d)^2
  have h : ∀ z : ℤ, |z| ≤ z^2 := by
    intro z
    have h0 : 0 ≤ |z| := abs_nonneg z
    have h1 : |z| = 0 ∨ 1 ≤ |z| := by omega
    rcases h1 with h1 | h1
    · rw [h1]; exact sq_nonneg z
    · nlinarith [sq_abs z]
  exact h _

def shortGaps : ℕ → BTree → Multiset ℕ
  | 0, _ => 0
  | k+1, .leaf => {k+1}
  | k+1, .fork l r => shortGaps k l + shortGaps k r

def excess : ℕ → BTree → ℕ
  | 0, T => leafCount T - 1
  | _+1, .leaf => 0
  | k+1, .fork l r => excess k l + excess k r

def deepSum : ℕ → BTree → ℤ
  | 0, T => depthSum T
  | _+1, .leaf => 0
  | k+1, .fork l r => deepSum k l + deepSum k r

def deepSquare : ℕ → BTree → ℤ
  | 0, T => depthSquareSum T
  | _+1, .leaf => 0
  | k+1, .fork l r => deepSquare k l + deepSquare k r

def coinSaving (s : Multiset ℕ) : ℕ := (s.map (fun t => 2^t-1)).sum
def coinSquare (s : Multiset ℕ) : ℕ := (s.map (fun t => t^2)).sum

@[simp] theorem coinSaving_cons (a : ℕ) (s : Multiset ℕ) :
    coinSaving (a ::ₘ s) = (2^a-1) + coinSaving s := by simp [coinSaving]
@[simp] theorem coinSquare_cons (a : ℕ) (s : Multiset ℕ) :
    coinSquare (a ::ₘ s) = a^2 + coinSquare s := by simp [coinSquare]

 theorem cut_count (k : ℕ) (T : BTree) :
    2^k + excess k T = leafCount T + coinSaving (shortGaps k T) := by
  induction k generalizing T with
  | zero =>
    simp only [excess, shortGaps, coinSaving, Multiset.map_zero, Multiset.sum_zero,
      add_zero, pow_zero]
    have := leafCount_pos T
    omega
  | succ k ih =>
    cases T with
    | leaf =>
      simp only [shortGaps, excess, coinSaving, Multiset.map_singleton,
        Multiset.sum_singleton, leafCount_leaf, add_zero]
      have : 0 < 2^(k+1) := by positivity
      omega
    | fork l r =>
      simp only [shortGaps, excess, leafCount_fork, coinSaving, Multiset.map_add,
        Multiset.sum_add, pow_succ]
      have hl := ih l
      have hr := ih r
      unfold coinSaving at hl hr
      omega

 theorem cut_deep_bounds (k : ℕ) (T : BTree) :
    2 * (excess k T : ℤ) ≤ deepSum k T ∧ deepSum k T ≤ deepSquare k T := by
  induction k generalizing T with
  | zero =>
    simp only [excess, deepSum, deepSquare]
    rw [Nat.cast_sub (by have := leafCount_pos T; omega), Nat.cast_one]
    exact ⟨sum_lower T, square_ge_sum T⟩
  | succ k ih =>
    cases T with
    | leaf => simp [excess, deepSum, deepSquare]
    | fork l r =>
      simp only [excess, deepSum, deepSquare, Nat.cast_add]
      have hl := ih l
      have hr := ih r
      constructor <;> omega

 theorem centered_fork (k : ℕ) (l r : BTree) :
    E (k+1) (.fork l r) = E k l + E k r ∧
    R (k+1) (.fork l r) = R k l + R k r := by
  simp only [(centered_identities _ _).1, (centered_identities _ _).2,
    leafCount_fork, depthSum_fork, depthSquareSum_fork, Nat.cast_add, Nat.cast_one]
  constructor <;> ring

 theorem cut_moments (k : ℕ) (T : BTree) :
    E k T = ((shortGaps k T).sum : ℤ) - deepSum k T ∧
    R k T = (coinSquare (shortGaps k T) : ℤ) + deepSquare k T := by
  induction k generalizing T with
  | zero =>
    simp [shortGaps, deepSum, deepSquare, coinSquare,
      (centered_identities _ _).1, (centered_identities _ _).2]
  | succ k ih =>
    cases T with
    | leaf => simp [E, R, shortGaps, deepSum, deepSquare, leafDepths, coinSquare]
    | fork l r =>
      rw [(centered_fork k l r).1, (centered_fork k l r).2]
      have hl := ih l
      have hr := ih r
      simp only [shortGaps, deepSum, deepSquare, coinSquare, Multiset.sum_add,
        Multiset.map_add, Nat.cast_add] at *
      constructor <;> omega

 theorem shortGaps_pos (k : ℕ) (T : BTree) : ∀ t ∈ shortGaps k T, 0 < t := by
  induction k generalizing T with
  | zero => simp [shortGaps]
  | succ k ih =>
    cases T with
    | leaf => simp [shortGaps]
    | fork l r =>
      intro t ht
      simp only [shortGaps, Multiset.mem_add] at ht
      rcases ht with ht | ht
      · exact ih l t ht
      · exact ih r t ht

 theorem leaf_square_le_R (k : ℕ) (T : BTree) (d : ℕ) (hd : d ∈ leafDepths T) :
    ((k : ℤ) - d)^2 ≤ R k T := by
  apply Multiset.single_le_sum
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hz
    exact sq_nonneg _
  · exact Multiset.mem_map.mpr ⟨d, hd, rfl⟩

 def minDepth : BTree → ℕ
  | .leaf => 0
  | .fork l r => min (minDepth l) (minDepth r) + 1

 theorem minDepth_mem (T : BTree) : minDepth T ∈ leafDepths T := by
  induction T with
  | leaf => simp [minDepth, leafDepths]
  | fork l r hl hr =>
    simp only [minDepth, leafDepths]
    apply Multiset.mem_map.mpr
    by_cases h : minDepth l ≤ minDepth r
    · exact ⟨minDepth l, Multiset.mem_add.mpr (Or.inl hl), by simp [min_eq_left h]⟩
    · exact ⟨minDepth r, Multiset.mem_add.mpr (Or.inr hr), by simp [min_eq_right (by omega : minDepth r ≤ minDepth l)]⟩

 theorem pow_minDepth_le (T : BTree) : 2 ^ minDepth T ≤ leafCount T := by
  induction T with
  | leaf => simp [minDepth]
  | fork l r hl hr =>
    have h1 : 2 ^ min (minDepth l) (minDepth r) ≤ 2 ^ minDepth l :=
      Nat.pow_le_pow_right (by decide) (min_le_left _ _)
    have h2 : 2 ^ min (minDepth l) (minDepth r) ≤ 2 ^ minDepth r :=
      Nat.pow_le_pow_right (by decide) (min_le_right _ _)
    simp only [minDepth, leafCount_fork, pow_succ]
    omega

theorem low_objective_center (T : BTree) (hn : leafCount T = 67256579)
    (hD : depthObjective T ≤ 330431494786) :
    ∃ k : ℕ, 27 ≤ k ∧ k ≤ 96 ∧ R k T ≤ 4913 := by
  let z : ℤ := (2 * depthSum T + 67256579) / 134513158
  have hS := sum_nonneg T
  have hz : 0 ≤ z := by dsimp [z]; omega
  let k := z.toNat
  have hk : (k : ℤ) = z := Int.toNat_of_nonneg hz
  have hE := (centered_identities k T).1
  rw [hn, hk] at hE
  have hround : 2 * |E k T| ≤ 67256579 := by
    dsimp [z] at hE
    by_cases hp : 0 ≤ E k T
    · rw [abs_of_nonneg hp]; omega
    · rw [abs_of_nonpos (by omega : E k T ≤ 0)]; omega
  have habs := abs_E_le_R k T
  have hR0 : 0 ≤ R k T := le_trans (abs_nonneg _) habs
  have hid := centered_objective k T
  rw [hn] at hid
  norm_num at hid
  have hsq : (E k T)^2 ≤ (R k T)^2 := by
    nlinarith [sq_abs (E k T), mul_nonneg (sub_nonneg.mpr habs)
      (show 0 ≤ R k T + |E k T| by positivity)]
  have hsq2 : 2 * (E k T)^2 ≤ 67256579 * R k T := by
    nlinarith [sq_abs (E k T), mul_nonneg (abs_nonneg (E k T))
      (show 0 ≤ 67256579 - 2 * |E k T| by omega)]
  have hR2 : R k T ≤ 9826 := by omega
  have hRC : R k T ≤ 4913 := by
    by_contra h
    have hh : 0 ≤ R k T - 4914 := by omega
    have hh' : 0 ≤ 67256579 - R k T - 4914 := by omega
    nlinarith [mul_nonneg hh hh']
  refine ⟨k, ?_, ?_, hRC⟩
  · have hc := cut_count k T
    have hb := cut_deep_bounds k T
    have hm := (cut_moments k T).2
    have hq : (0 : ℤ) ≤ coinSquare (shortGaps k T) := by positivity
    have hx : excess k T ≤ 2456 := by omega
    by_contra hh
    have hk26 : k ≤ 26 := by omega
    have hp := Nat.pow_le_pow_right (n := 2) (by decide) hk26
    norm_num at hp
    omega
  · have hd : minDepth T ≤ 26 := by
      by_contra hh
      have h27 : 27 ≤ minDepth T := by omega
      have hp := Nat.pow_le_pow_right (n := 2) (by decide) h27
      have ht := pow_minDepth_le T
      rw [hn] at ht
      norm_num at hp
      omega
    have hs := leaf_square_le_R k T (minDepth T) (minDepth_mem T)
    by_contra hh
    have hdiff : (71 : ℤ) ≤ (k : ℤ) - minDepth T := by omega
    nlinarith

end DepthVariance

namespace DepthVariance
 theorem coin_min_normal (r : ℕ) (s : Multiset ℕ) (x : ℕ)
    (hpos : ∀ t ∈ s, 0 < t) (heq : coinSaving s = r + x)
    (hmin : ∀ u y, (∀ t ∈ u, 0 < t) → coinSaving u = r + y →
      coinSquare s + 2*x ≤ coinSquare u + 2*y) :
    (∀ t ∈ s, t = 1 ∨ 5 ≤ t) ∧
    (∀ t, 5 ≤ t → s.count t ≤ 1) ∧
    (x = 0 ∨ 1 ∉ s) := by
  constructor
  · intro t ht
    by_contra hh
    have hp := hpos t ht
    have h24 : 2 ≤ t ∧ t ≤ 4 := by omega
    obtain ⟨u, rfl⟩ := Multiset.exists_cons_of_mem ht
    have hu : ∀ a ∈ u, 0 < a := by
      intro a ha
      exact hpos a (Multiset.mem_cons_of_mem ha)
    have hrep : ∀ a ∈ Multiset.replicate (2^t-1) 1 + u, 0 < a := by
      intro a ha
      simp only [Multiset.mem_add] at ha
      rcases ha with ha | ha
      · have := (Multiset.mem_replicate.mp ha).2
        omega
      · exact hu a ha
    have hs : coinSaving (Multiset.replicate (2^t-1) 1 + u) = r+x := by
      simpa [coinSaving] using heq
    have hm := hmin (Multiset.replicate (2^t-1) 1 + u) x hrep hs
    simp [coinSquare] at hm
    rcases h24 with ⟨hlo, hhi⟩
    interval_cases t <;> norm_num at hm
  constructor
  · intro t ht
    by_contra hh
    have hmem : t ∈ s := Multiset.count_pos.mp (by omega)
    obtain ⟨u, rfl⟩ := Multiset.exists_cons_of_mem hmem
    have hmem2 : t ∈ u := by
      apply Multiset.count_pos.mp
      simp only [Multiset.count_cons_self] at hh
      omega
    obtain ⟨v, rfl⟩ := Multiset.exists_cons_of_mem hmem2
    have hv : ∀ a ∈ v, 0 < a := by
      intro a ha
      exact hpos a (Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem ha))
    have hnew : ∀ a ∈ (t+1) ::ₘ v, 0 < a := by
      intro a ha
      rcases Multiset.mem_cons.mp ha with rfl | ha
      · omega
      · exact hv a ha
    have hs : coinSaving ((t+1) ::ₘ v) = r+(x+1) := by
      simp only [coinSaving_cons] at heq ⊢
      rw [pow_succ]
      have hp : 0 < 2^t := by positivity
      omega
    have hm := hmin ((t+1) ::ₘ v) (x+1) hnew hs
    simp only [coinSquare_cons] at hm
    nlinarith
  · by_contra hh
    have hx : 0 < x := by omega
    have hmem : 1 ∈ s := by tauto
    obtain ⟨u, rfl⟩ := Multiset.exists_cons_of_mem hmem
    have hu : ∀ a ∈ u, 0 < a := by
      intro a ha
      exact hpos a (Multiset.mem_cons_of_mem ha)
    have hs : coinSaving u = r+(x-1) := by
      simp only [coinSaving_cons] at heq
      norm_num at heq
      omega
    have hm := hmin u (x-1) hu hs
    simp only [coinSquare_cons] at hm
    norm_num at hm
    omega

end DepthVariance

namespace DepthVarianceCertificate

def n : ℕ := 67256579
def C : ℕ := 4913

def bitGaps : ℕ → ℕ → ℕ → List ℕ
  | 0, _, _ => []
  | fuel + 1, b, t =>
    if b % 2 = 1 then t :: bitGaps fuel (b / 2) (t + 1)
    else bitGaps fuel (b / 2) (t + 1)

def gaps (b : ℕ) : List ℕ := bitGaps 96 b 5
def saving (b : ℕ) : ℕ := 32 * b - (gaps b).length
def squareCost (b : ℕ) : ℕ := ((gaps b).map (· ^ 2)).sum
def firstMoment (b : ℕ) : ℕ := (gaps b).sum

def cost (r b : ℕ) : ℕ :=
  squareCost b + if saving b ≤ r then r - saving b else 2 * (saving b - r)

def moment (r b : ℕ) : ℤ :=
  (firstMoment b : ℤ) + if saving b ≤ r then ((r - saving b : ℕ) : ℤ)
    else -2 * ((saving b - r : ℕ) : ℤ)

def entry (k i : ℕ) : Prop :=
  let r := 2 ^ k - n
  let b := (r - C) / 32 + i
  cost r b ≤ C → k = 27 ∧ cost r b = C ∧ moment r b ^ 2 = 279 ^ 2

instance (k i : ℕ) : Decidable (entry k i) := by unfold entry; infer_instance

theorem bitGaps_correct (fuel b t : ℕ) (hb : b < 2^fuel) :
    bitGaps fuel b t = b.bitIndices.map (· + t) := by
  induction fuel generalizing b t with
  | zero =>
    have : b = 0 := by simpa using hb
    subst b
    simp [bitGaps]
  | succ f ih =>
    have hh : b / 2 < 2^f := by
      apply (Nat.div_lt_iff_lt_mul (show 0 < 2 by decide)).2
      simpa [pow_succ] using hb
    have heq : b = 2 * (b/2) + b%2 := by omega
    rcases Nat.mod_two_eq_zero_or_one b with h | h
    · conv_rhs => rw [heq, h, Nat.add_zero, Nat.bitIndices_two_mul]
      simp only [bitGaps, h, Nat.zero_ne_one, ↓reduceIte, ih _ _ hh, List.map_map]
      congr 1
      funext a
      simp
      omega
    · conv_rhs => rw [heq, h, Nat.bitIndices_two_mul_add_one]
      simp only [bitGaps, h, ↓reduceIte, ih _ _ hh, List.map_map, List.map_cons,
        Nat.zero_add]
      congr 2
      funext a
      simp
      omega

 theorem gaps_correct (b : ℕ) (hb : b < 2^96) :
    gaps b = b.bitIndices.map (·+5) := bitGaps_correct 96 b 5 hb

end DepthVarianceCertificate

namespace DepthVariance

 theorem saving_add_card (s : Multiset ℕ) :
    coinSaving s + s.card = (s.map (fun t => 2^t)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [coinSaving]
  | @cons a s ih =>
    simp only [coinSaving_cons, Multiset.card_cons, Multiset.map_cons, Multiset.sum_cons]
    have hp : 0 < 2^a := by positivity
    omega

 theorem encode_large_gaps (u : Multiset ℕ) (hu : u.Nodup)
    (hge : ∀ t ∈ u, 5 ≤ t) :
    ∃ b : ℕ, ((b.bitIndices.map (·+5) : List ℕ) : Multiset ℕ) = u ∧
      32*b = coinSaving u + u.card := by
  let F : Finset ℕ := ⟨u, hu⟩
  let L := F.sort (· ≤ ·)
  have hL : L.SortedLT := F.sortedLT_sort
  have hLeq : (L : Multiset ℕ) = u := F.sort_eq _
  have hLge : ∀ t ∈ L, 5 ≤ t := by
    intro t ht
    apply hge t
    rw [← hLeq]
    exact ht
  have hsub : (L.map (·-5)).SortedLT := by
    apply List.Pairwise.sortedLT
    rw [List.pairwise_map]
    exact hL.pairwise.imp_of_mem (fun {a b} ha hb hab => by
      have h1 := hLge a ha
      have h2 := hLge b hb
      omega)
  let b := ((L.map (·-5)).map (fun i => 2^i)).sum
  have hb : b.bitIndices = L.map (·-5) := Nat.bitIndices_sum_map_two_pow hsub
  have hm : ((b.bitIndices.map (·+5) : List ℕ) : Multiset ℕ) = u := by
    rw [hb, List.map_map]
    have hi : L.map (fun x => (x-5)+5) = L := by
      calc
        L.map (fun x => (x-5)+5) = L.map id := by
          apply List.map_congr_left
          intro a ha
          exact Nat.sub_add_cancel (hLge a ha)
        _ = L := List.map_id L
    simpa [Function.comp_def, hi] using hLeq
  refine ⟨b, hm, ?_⟩
  rw [saving_add_card, ← hm]
  simp only [Multiset.map_coe, Multiset.sum_coe, List.map_map, Function.comp_def]
  simp_rw [pow_add]
  norm_num
  rw [List.sum_map_mul_right, Nat.sum_map_two_pow_bitIndices]
  omega

 theorem gap_card_bound (u : Multiset ℕ) (hge : ∀ t ∈ u, 5 ≤ t) :
    25*u.card ≤ coinSquare u := by
  induction u using Multiset.induction_on with
  | empty => simp [coinSquare]
  | @cons a s ih =>
    have ha : 5 ≤ a := hge a (by simp)
    have hs : ∀ t ∈ s, 5 ≤ t := fun t ht => hge t (Multiset.mem_cons_of_mem ht)
    have hh := ih hs
    simp only [coinSquare_cons, Multiset.card_cons]
    nlinarith

 theorem split_normal (s : Multiset ℕ)
    (hn : ∀ t ∈ s, t=1 ∨ 5 ≤ t) (hc : ∀ t, 5 ≤ t → s.count t ≤ 1) :
    ∃ a : ℕ, ∃ u : Multiset ℕ,
      s = Multiset.replicate a 1 + u ∧ u.Nodup ∧
      (∀ t ∈ u, 5 ≤ t) ∧ a = s.count 1 := by
  let u := s.filter (fun t => t ≠ 1)
  refine ⟨s.count 1, u, ?_, ?_, ?_, rfl⟩
  · have hh := Multiset.filter_add_not (fun t : ℕ => t=1) s
    rw [Multiset.filter_eq'] at hh
    exact hh.symm
  · apply Multiset.nodup_iff_count_le_one.mpr
    intro t
    by_cases ht : t=1
    · subst t
      simp [u]
    · by_cases hmem : t ∈ u
      · have hs : t ∈ s := (Multiset.mem_filter.mp hmem).1
        have h5 : 5 ≤ t := (hn t hs).resolve_left ht
        simpa [u, Multiset.count_filter, ht] using hc t h5
      · simp [Multiset.count_eq_zero.mpr hmem]
  · intro t ht
    have hs := Multiset.mem_filter.mp ht
    exact (hn t hs.1).resolve_left hs.2

end DepthVariance

namespace DepthVariance
open DepthVarianceCertificate

 theorem canonical_cost_certificate
    (hfinite : ∀ k, 27 ≤ k → k ≤ 96 → ∀ i, i < 240 → entry k i)
    (k a x : ℕ) (u : Multiset ℕ) (hk : 27 ≤ k) (hk' : k ≤ 96)
    (hu : u.Nodup) (hge : ∀ t ∈ u, 5 ≤ t)
    (hax : a=0 ∨ x=0)
    (heq : a + coinSaving u = 2^k-67256579+x)
    (hc : a + coinSquare u + 2*x ≤ 4913) :
    k=27 ∧ a+coinSquare u+2*x=4913 ∧
      ((a : ℤ) + u.sum - 2*x)^2=279^2 := by
  let r := 2^k-67256579
  obtain ⟨b, hb, hp⟩ := encode_large_gaps u hu hge
  have hj := gap_card_bound u hge
  have hj196 : u.card ≤ 196 := by omega
  have hx2456 : x ≤ 2456 := by omega
  have ha4913 : a ≤ 4913 := by omega
  have hrel : 32*b+a = r+x+u.card := by dsimp [r]; omega
  have hloPow : 2^27 ≤ 2^k := Nat.pow_le_pow_right (by decide) hk
  have hhiPow : 2^k ≤ 2^96 := Nat.pow_le_pow_right (by decide) hk'
  norm_num at hloPow hhiPow
  have hr : 4913 ≤ r := by dsimp [r]; omega
  have hb96 : b < 2^96 := by norm_num; dsimp [r] at hrel; omega
  have hlow : (r-4913)/32 ≤ b := by omega
  have hidx : b-(r-4913)/32 < 240 := by omega
  have hindex : (r-4913)/32 + (b-(r-4913)/32) = b := by omega
  have hg : ((gaps b : List ℕ) : Multiset ℕ) = u := by
    rw [gaps_correct b hb96]
    exact hb
  have hlen : (gaps b).length = u.card := by
    simpa using congrArg Multiset.card hg
  have hsum : firstMoment b = u.sum := by
    simpa [firstMoment] using congrArg Multiset.sum hg
  have hsq : squareCost b = coinSquare u := by
    unfold squareCost coinSquare
    rw [← hg]
    rfl
  have hsave : saving b = coinSaving u := by
    unfold saving
    rw [hlen]
    omega
  have hcost : cost r b = a+coinSquare u+2*x := by
    unfold cost
    rw [hsq, hsave]
    by_cases hh : coinSaving u ≤ r
    · have hzero : x=0 := by dsimp [r] at hh; omega
      simp only [hh, ↓reduceIte]
      dsimp [r]
      omega
    · have hzero : a=0 := by dsimp [r] at hh; omega
      simp only [hh, ↓reduceIte]
      dsimp [r]
      omega
  have hmom : moment r b = (a : ℤ)+u.sum-2*x := by
    unfold moment
    rw [hsum, hsave]
    by_cases hh : coinSaving u ≤ r
    · have hzero : x=0 := by dsimp [r] at hh; omega
      simp only [hh, ↓reduceIte]
      dsimp [r]
      omega
    · have hzero : a=0 := by dsimp [r] at hh; omega
      simp only [hh, ↓reduceIte]
      dsimp [r]
      omega
  have hf := hfinite k hk hk' (b-(r-4913)/32) hidx
  change cost r ((r-4913)/32+(b-(r-4913)/32)) ≤ 4913 →
    k=27 ∧ cost r ((r-4913)/32+(b-(r-4913)/32))=4913 ∧
      moment r ((r-4913)/32+(b-(r-4913)/32))^2=279^2 at hf
  rw [hindex, hcost, hmom] at hf
  exact hf hc

end DepthVariance

namespace DepthVariance
open DepthVarianceCertificate

 theorem normal_check
    (hfinite : ∀ k, 27 ≤ k → k ≤ 96 → ∀ i, i < 240 → entry k i)
    (k : ℕ) (s : Multiset ℕ) (x : ℕ) (hk : 27 ≤ k) (hk' : k ≤ 96)
    (hn : ∀ t ∈ s, t=1 ∨ 5 ≤ t) (hc : ∀ t, 5 ≤ t → s.count t ≤ 1)
    (hax : x=0 ∨ 1 ∉ s)
    (heq : coinSaving s = 2^k-67256579+x)
    (hcost : coinSquare s+2*x ≤ 4913) :
    k=27 ∧ coinSquare s+2*x=4913 ∧ ((s.sum : ℤ)-2*x)^2=279^2 := by
  obtain ⟨a,u,hs,hu,hge,ha⟩ := split_normal s hn hc
  have hax' : a=0 ∨ x=0 := by
    rcases hax with hx | hx
    · exact Or.inr hx
    · left
      rw [ha, Multiset.count_eq_zero.mpr hx]
  have heq' : a+coinSaving u = 2^k-67256579+x := by
    simpa [hs, coinSaving] using heq
  have hcost' : a+coinSquare u+2*x ≤ 4913 := by
    simpa [hs, coinSquare] using hcost
  have hh := canonical_cost_certificate hfinite k a x u hk hk' hu hge hax' heq' hcost'
  simpa [hs, coinSquare, Nat.cast_add] using hh

 theorem coin_certificate
    (hfinite : ∀ k, 27 ≤ k → k ≤ 96 → ∀ i, i < 240 → entry k i)
    (k : ℕ) (s : Multiset ℕ) (x : ℕ) (hk : 27 ≤ k) (hk' : k ≤ 96)
    (hpos : ∀ t ∈ s, 0 < t)
    (heq : coinSaving s = 2^k-67256579+x)
    (hcost : coinSquare s+2*x ≤ 4913) :
    k=27 ∧ coinSquare s+2*x=4913 ∧ ((s.sum : ℤ)-2*x)^2=279^2 := by
  classical
  let r := 2^k-67256579
  let P : ℕ → Prop := fun c => ∃ u : Multiset ℕ, ∃ y : ℕ,
    (∀ t ∈ u, 0 < t) ∧ coinSaving u = r+y ∧ coinSquare u+2*y=c
  have hex : ∃ c, P c := ⟨coinSquare s+2*x, s, x, hpos, heq, rfl⟩
  obtain ⟨u,y,hu,he,hec⟩ := Nat.find_spec hex
  have hmin : ∀ v z, (∀ t ∈ v, 0 < t) → coinSaving v=r+z →
      Nat.find hex ≤ coinSquare v+2*z := by
    intro v z hp heqv
    exact Nat.find_min' hex ⟨v,z,hp,heqv,rfl⟩
  have hm : ∀ v z, (∀ t ∈ v, 0 < t) → coinSaving v=r+z →
      coinSquare u+2*y ≤ coinSquare v+2*z := by
    intro v z hp heqv
    rw [hec]
    exact hmin v z hp heqv
  have hsmall : coinSquare u+2*y ≤ 4913 := le_trans (hm s x hpos heq) hcost
  have hnorm := coin_min_normal r u y hu he hm
  have hucheck := normal_check hfinite k u y hk hk' hnorm.1 hnorm.2.1 hnorm.2.2 he hsmall
  have horig : coinSquare s+2*x=4913 := by
    have := hm s x hpos heq
    omega
  have hmorig : ∀ v z, (∀ t ∈ v, 0 < t) → coinSaving v=r+z →
      coinSquare s+2*x ≤ coinSquare v+2*z := by
    intro v z hp heqv
    have := hm v z hp heqv
    omega
  have hnormorig := coin_min_normal r s x hpos heq hmorig
  exact normal_check hfinite k s x hk hk' hnormorig.1 hnormorig.2.1 hnormorig.2.2 heq hcost

 theorem global_lower_from_certificate
    (hfinite : ∀ k, 27 ≤ k → k ≤ 96 → ∀ i, i < 240 → entry k i)
    (T : BTree) (hn : leafCount T=67256579) :
    330431494786 ≤ depthObjective T := by
  by_contra hbad
  have hD : depthObjective T ≤ 330431494786 := by omega
  obtain ⟨k,hk,hk',hR⟩ := low_objective_center T hn hD
  have hcount := cut_count k T
  rw [hn] at hcount
  have hpow : 2^27 ≤ 2^k := Nat.pow_le_pow_right (by decide) hk
  norm_num at hpow
  have heq : coinSaving (shortGaps k T) = 2^k-67256579+excess k T := by omega
  have hdeep := cut_deep_bounds k T
  have hmoment := cut_moments k T
  have hcost : coinSquare (shortGaps k T)+2*excess k T ≤ 4913 := by omega
  have hh := coin_certificate hfinite k (shortGaps k T) (excess k T)
    hk hk' (shortGaps_pos k T) heq hcost
  have hReq : R k T=4913 := by omega
  have hSeq : deepSum k T = 2*(excess k T : ℤ) := by omega
  have hEsq : E k T ^ 2 = 279^2 := by
    rw [hmoment.1, hSeq]
    exact hh.2.2
  have hid := centered_objective k T
  rw [hn,hReq,hEsq] at hid
  norm_num at hid
  omega

end DepthVariance

namespace DepthVariance

 def perfect : ℕ → BTree
  | 0 => .leaf
  | h+1 => .fork (perfect h) (perfect h)

 theorem perfect_stats (h : ℕ) :
    leafCount (perfect h) = 2^h ∧
    depthSum (perfect h) = (2^h : ℕ)* (h : ℤ) ∧
    depthSquareSum (perfect h) = (2^h : ℕ)*(h : ℤ)^2 := by
  induction h with
  | zero => simp [perfect]
  | succ h ih =>
    simp only [perfect, leafCount_fork, depthSum_fork, depthSquareSum_fork,
      ih.1, ih.2.1, ih.2.2, pow_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
      Nat.cast_ofNat]
    constructor
    · omega
    constructor <;> ring

@[simp] theorem perfect_count (h : ℕ) : leafCount (perfect h) = 2^h := (perfect_stats h).1
@[simp] theorem perfect_sum (h : ℕ) : depthSum (perfect h) = (2^h : ℕ)*(h : ℤ) :=
  (perfect_stats h).2.1
@[simp] theorem perfect_square (h : ℕ) : depthSquareSum (perfect h) = (2^h : ℕ)*(h : ℤ)^2 :=
  (perfect_stats h).2.2

 def spread : ℕ → ℕ → BTree
  | 0, k => if k=0 then .leaf else .fork .leaf .leaf
  | h+1, k =>
    if k=0 then perfect (h+1)
    else if k=2^(h+1) then perfect (h+2)
    else .fork (spread h (min k (2^h))) (spread h (k-2^h))

 def graft (b : ℕ) (gaps : Finset ℕ) (base : BTree) : ℕ → BTree
  | 0 => base
  | s+1 => .fork (if b+s ∈ gaps then .leaf else perfect (b+s)) (graft b gaps base s)

 def treeA : BTree :=
  graft 5 {8,9,10,11,12,13,15,16,18,19,20,21,22,23,24,25} (spread 4 3) 22

 def treeB : BTree :=
  graft 9 {14,15,16,18,19,20,21,22,23,24,25} (spread 9 248) 18

set_option maxRecDepth 10000
set_option maxHeartbeats 0

 theorem treeA_stats :
    leafCount treeA=67256579 ∧ depthSum treeA=1815927354 ∧
    depthSquareSum treeA=49030035938 := by
  norm_num [treeA, graft, spread]

 theorem treeB_stats :
    leafCount treeB=67256579 ∧ depthSum treeB=1815927912 ∧
    depthSquareSum treeB=49030066070 := by
  norm_num [treeB, graft, spread]

 theorem treeA_objective : depthObjective treeA=330431494786 := by
  norm_num [depthObjective, treeA_stats.1, treeA_stats.2.1, treeA_stats.2.2]

 theorem treeB_objective : depthObjective treeB=330431494786 := by
  norm_num [depthObjective, treeB_stats.1, treeB_stats.2.1, treeB_stats.2.2]

 theorem trees_not_depth_equivalent : leafDepths treeA ≠ leafDepths treeB := by
  intro h
  have hs : depthSum treeA=depthSum treeB := by unfold depthSum; rw [h]
  rw [treeA_stats.2.1, treeB_stats.2.1] at hs
  norm_num at hs

 theorem counterexample_from_certificate
    (hfinite : ∀ k, 27 ≤ k → k ≤ 96 → ∀ i, i < 240 → DepthVarianceCertificate.entry k i) :
    MinimizesDepthVariance 67256579 treeA ∧
    MinimizesDepthVariance 67256579 treeB ∧ leafDepths treeA ≠ leafDepths treeB := by
  refine ⟨⟨treeA_stats.1, ?_⟩, ⟨treeB_stats.1, ?_⟩, trees_not_depth_equivalent⟩
  · intro U hU
    rw [treeA_objective]
    exact global_lower_from_certificate hfinite U hU
  · intro U hU
    rw [treeB_objective]
    exact global_lower_from_certificate hfinite U hU

end DepthVariance

namespace DepthVarianceCertificate

 def certifies (k r p j s q : ℕ) : Prop :=
  let a := p-j
  let c := q + if a ≤ r then r-a else 2*(a-r)
  let e : ℤ := (s : ℤ) + if a ≤ r then ((r-a : ℕ) : ℤ) else -2*((a-r : ℕ) : ℤ)
  c ≤ C → k=27 ∧ c=C ∧ e^2=279^2

 instance (k r p j s q : ℕ) : Decidable (certifies k r p j s q) := by
  unfold certifies
  infer_instance

 def scan (k r p : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | fuel, b, t, j, s, q =>
    if C < q then true else
    match fuel with
    | 0 => decide (certifies k r p j s q)
    | f+1 =>
      if b%2=1 then scan k r p f (b/2) (t+1) (j+1) (s+t) (q+t^2)
      else scan k r p f (b/2) (t+1) j s q

 theorem scan_sound (k r p fuel b t j s q : ℕ)
    (h : scan k r p fuel b t j s q = true) :
    certifies k r p (j+(bitGaps fuel b t).length)
      (s+(bitGaps fuel b t).sum)
      (q+((bitGaps fuel b t).map (·^2)).sum) := by
  induction fuel generalizing b t j s q with
  | zero =>
    simp only [bitGaps, List.length_nil, List.sum_nil, List.map_nil, Nat.add_zero]
    by_cases hq : C < q
    · unfold certifies
      intro hc
      omega
    · simpa [scan, hq] using h
  | succ f ih =>
    by_cases hq : C < q
    · unfold certifies
      intro hc
      omega
    · simp only [scan, hq, ↓reduceIte] at h
      by_cases hb : b%2=1
      · rw [if_pos hb] at h
        have hh := ih (b/2) (t+1) (j+1) (s+t) (q+t^2) h
        simpa [bitGaps, hb, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
      · rw [if_neg hb] at h
        simpa [bitGaps, hb] using ih (b/2) (t+1) j s q h

 def fastEntry (k i : ℕ) : Bool :=
  let r := 2^k-n
  let b := (r-C)/32+i
  scan k r (32*b) 96 b 5 0 0 0

 theorem fastEntry_sound (k i : ℕ) (h : fastEntry k i = true) : entry k i := by
  have hh := scan_sound k (2^k-n) (32*((2^k-n-C)/32+i)) 96
    ((2^k-n-C)/32+i) 5 0 0 0 h
  simp only [Nat.zero_add] at hh
  exact hh

end DepthVarianceCertificate

namespace DepthVarianceCertificate

 def checkCols : ℕ → ℕ → Bool
  | 0, _ => true
  | m+1, k => fastEntry k m && checkCols m k

 def checkRows : ℕ → Bool
  | 0 => true
  | m+1 => checkCols 240 (27+m) && checkRows m

 theorem checkCols_sound (m k : ℕ) (h : checkCols m k = true)
    (i : ℕ) (hi : i < m) : entry k i := by
  induction m with
  | zero => omega
  | succ m ih =>
    simp only [checkCols, Bool.and_eq_true] at h
    by_cases he : i=m
    · subst i
      exact fastEntry_sound k m h.1
    · exact ih h.2 (by omega)

 theorem checkRows_sound (m : ℕ) (h : checkRows m = true)
    (j : ℕ) (hj : j < m) (i : ℕ) (hi : i < 240) : entry (27+j) i := by
  induction m with
  | zero => omega
  | succ m ih =>
    simp only [checkRows, Bool.and_eq_true] at h
    by_cases he : j=m
    · subst j
      exact checkCols_sound 240 (27+m) h.1 i hi
    · exact ih h.2 (by omega)

 theorem finite_result_of_check (h : checkRows 70 = true) :
    ∀ k, 27 ≤ k → k ≤ 96 → ∀ i, i < 240 → entry k i := by
  intro k hk hk' i hi
  have hh := checkRows_sound 70 h (k-27) (by omega) i hi
  have he : 27+(k-27)=k := by omega
  rwa [he] at hh

end DepthVarianceCertificate

namespace DepthVarianceCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem finite_certificate : checkRows 70 = true := by
  decide +kernel

theorem finite_result :
    ∀ k, 27 ≤ k → k ≤ 96 → ∀ i, i < 240 → entry k i :=
  finite_result_of_check finite_certificate

end DepthVarianceCertificate

namespace DepthVariance

theorem explicit_counterexample :
    MinimizesDepthVariance 67256579 treeA ∧
    MinimizesDepthVariance 67256579 treeB ∧
    leafDepths treeA ≠ leafDepths treeB :=
  counterexample_from_certificate DepthVarianceCertificate.finite_result

/-- Negation of the frozen conjecture in Statement.lean. -/
theorem minimum_variance_depth_unique_false :
    ¬ (∀ (n : ℕ), 1 ≤ n → ∀ (T T' : BTree),
      MinimizesDepthVariance n T → MinimizesDepthVariance n T' →
      leafDepths T = leafDepths T') := by
  intro h
  obtain ⟨hA, hB, hne⟩ := explicit_counterexample
  exact hne (h 67256579 (by decide) treeA treeB hA hB)

end DepthVariance
