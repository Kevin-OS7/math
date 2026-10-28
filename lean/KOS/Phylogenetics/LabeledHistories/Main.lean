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

/-- The event-count conclusion actually obtained by the written proof. -/
def AllEventCounts : Prop :=
  ∀ (T : Shape) (z : ℕ), E T z ≤ E (canonical T.leaves) z

theorem allEventCounts_implies_part_ii (h : AllEventCounts) : Conjecture14ii := by
  intro T z _ _
  exact h T z

theorem canonical_leaves {n : ℕ} (hn : 0 < n) : (canonical n).leaves = n := by
  simp [Shape.leaves, canonical, Nat.card_Ico]
  omega

theorem leaves_positive (T : Shape) : 0 < T.leaves := by
  simp [Shape.leaves]

theorem canonical_nodes_card (T : Shape) :
    (canonical T.leaves).nodes.card = T.nodes.card := by
  have h := canonical_leaves (leaves_positive T)
  change (canonical T.leaves).nodes.card + 1 = T.nodes.card + 1 at h
  omega

/-- The uniqueness reduction used in the paper and in the written proof.
The ordinary-history uniqueness assertion is an explicit hypothesis here. -/
theorem all_counts_and_ordinary_unique_implies_part_i
    (hc : AllEventCounts)
    (hu : ∀ T : Shape, ¬ Isomorphic T (canonical T.leaves) →
      E T T.nodes.card < E (canonical T.leaves) T.nodes.card) : Conjecture14i := by
  intro T
  have hcard := canonical_nodes_card T
  have hle : N T ≤ N (canonical T.leaves) := by
    unfold N
    rw [hcard]
    exact Finset.sum_le_sum (fun z _ => hc T z)
  refine ⟨hle, ?_⟩
  intro heq
  by_contra hnot
  have hlt : N T < N (canonical T.leaves) := by
    unfold N
    rw [hcard]
    apply Finset.sum_lt_sum
    · intro z _
      exact hc T z
    · exact ⟨T.nodes.card, Finset.mem_range.mpr (Nat.lt_succ_self _), hu T hnot⟩
  omega


end DickeyRosenberg


/-!
Kernel-checked switching injection used in Lemma 1 of SOLUTION.md.
The edge relation is arbitrary. In the application it is child-to-parent.
-/

namespace DickeyRosenbergSwitching

variable {V : Type*}

def Admissible (r : V → V → Prop) (f : V → ℕ) : Prop :=
  ∀ u v, r u v → f u = 0 ∨ f u < f v

def Conflict (r : V → V → Prop) (f g : V → ℕ) (u v : V) : Prop :=
  r u v ∧ 0 < max (f u) (g u) ∧ min (f v) (g v) ≤ max (f u) (g u)

def Marked (r : V → V → Prop) (f g : V → ℕ) (Qonly : Set V) (v : V) : Prop :=
  ∃ w ∈ Qonly, Relation.EqvGen (Conflict r f g) v w

noncomputable def switched (r : V → V → Prop) (Qonly : Set V)
    (fg : (V → ℕ) × (V → ℕ)) : (V → ℕ) × (V → ℕ) := by
  classical
  exact (fun v => if Marked r fg.1 fg.2 Qonly v then fg.2 v else fg.1 v,
         fun v => if Marked r fg.1 fg.2 Qonly v then fg.1 v else fg.2 v)

theorem admissible_min {r : V → V → Prop} {f g : V → ℕ}
    (hf : Admissible r f) (hg : Admissible r g) :
    Admissible r (fun v => min (f v) (g v)) := by
  intro u v huv
  have h1 := hf u v huv
  have h2 := hg u v huv
  dsimp only
  omega

theorem admissible_max {r : V → V → Prop} {f g : V → ℕ}
    (hf : Admissible r f) (hg : Admissible r g) :
    Admissible r (fun v => max (f v) (g v)) := by
  intro u v huv
  have h1 := hf u v huv
  have h2 := hg u v huv
  dsimp only
  omega

theorem conflict_same_sign {r : V → V → Prop} {f g : V → ℕ}
    (hf : Admissible r f) (hg : Admissible r g) {u v : V}
    (hc : Conflict r f g u v) : (f u < g u ↔ f v < g v) := by
  obtain ⟨huv, hpos, hcross⟩ := hc
  have h1 := hf u v huv
  have h2 := hg u v huv
  omega

theorem component_same_sign {r : V → V → Prop} {f g : V → ℕ}
    (hf : Admissible r f) (hg : Admissible r g) {u v : V}
    (h : Relation.EqvGen (Conflict r f g) u v) :
    (f u < g u ↔ f v < g v) := by
  induction h with
  | rel x y h => exact conflict_same_sign hf hg h
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

theorem marked_low {r : V → V → Prop} {f g : V → ℕ} {Qonly : Set V}
    (hf : Admissible r f) (hg : Admissible r g)
    (hq : ∀ v ∈ Qonly, f v < g v) {v : V}
    (hv : Marked r f g Qonly v) : f v < g v := by
  obtain ⟨w, hw, hvw⟩ := hv
  exact (component_same_sign hf hg hvw).mpr (hq w hw)

theorem marked_of_mem {r : V → V → Prop} {f g : V → ℕ} {Qonly : Set V}
    {v : V} (hv : v ∈ Qonly) : Marked r f g Qonly v :=
  ⟨v, hv, Relation.EqvGen.refl v⟩

theorem marked_edge {r : V → V → Prop} {f g : V → ℕ} {Qonly : Set V}
    {u v : V} (hc : Conflict r f g u v) :
    (Marked r f g Qonly u ↔ Marked r f g Qonly v) := by
  constructor
  · rintro ⟨w, hw, h⟩
    exact ⟨w, hw, Relation.EqvGen.trans v u w
      (Relation.EqvGen.symm u v (Relation.EqvGen.rel u v hc)) h⟩
  · rintro ⟨w, hw, h⟩
    exact ⟨w, hw, Relation.EqvGen.trans u v w (Relation.EqvGen.rel u v hc) h⟩

theorem switched_admissible {r : V → V → Prop} {f g : V → ℕ} {Qonly : Set V}
    (hf : Admissible r f) (hg : Admissible r g)
    (hq : ∀ v ∈ Qonly, f v < g v) :
    Admissible r (switched r Qonly (f,g)).1 ∧
    Admissible r (switched r Qonly (f,g)).2 := by
  classical
  have low : ∀ {v}, Marked r f g Qonly v → f v < g v := marked_low hf hg hq
  constructor <;> intro u v huv
  all_goals
    have h1 := hf u v huv
    have h2 := hg u v huv
    by_cases hu : Marked r f g Qonly u
    · have hlowu := low hu
      by_cases hv : Marked r f g Qonly v
      · simp only [switched, hu, hv, if_true]
        assumption
      · have hnc : ¬ Conflict r f g u v := fun hc => hv ((marked_edge hc).mp hu)
        simp only [Conflict, huv, true_and] at hnc
        simp only [switched, hu, hv, if_true, if_false]
        omega
    · by_cases hv : Marked r f g Qonly v
      · have hlowv := low hv
        have hnc : ¬ Conflict r f g u v := fun hc => hu ((marked_edge hc).mpr hv)
        simp only [Conflict, huv, true_and] at hnc
        simp only [switched, hu, hv, if_true, if_false]
        omega
      · simp only [switched, hu, hv, if_false]
        assumption

theorem switched_min_max (r : V → V → Prop) (Qonly : Set V)
    (fg : (V → ℕ) × (V → ℕ)) (v : V) :
    min ((switched r Qonly fg).1 v) ((switched r Qonly fg).2 v) = min (fg.1 v) (fg.2 v) ∧
    max ((switched r Qonly fg).1 v) ((switched r Qonly fg).2 v) = max (fg.1 v) (fg.2 v) := by
  classical
  by_cases h : Marked r fg.1 fg.2 Qonly v <;>
    simp [switched, h, min_comm, max_comm]

theorem switched_conflict (r : V → V → Prop) (Qonly : Set V)
    (fg : (V → ℕ) × (V → ℕ)) :
    Conflict r (switched r Qonly fg).1 (switched r Qonly fg).2 =
      Conflict r fg.1 fg.2 := by
  funext u v
  simp only [Conflict, (switched_min_max r Qonly fg u).2,
    (switched_min_max r Qonly fg v).1]

theorem switched_marked (r : V → V → Prop) (Qonly : Set V)
    (fg : (V → ℕ) × (V → ℕ)) :
    Marked r (switched r Qonly fg).1 (switched r Qonly fg).2 Qonly =
      Marked r fg.1 fg.2 Qonly := by
  funext v
  simp only [Marked, switched_conflict]

theorem switched_involutive (r : V → V → Prop) (Qonly : Set V) :
    Function.Involutive (switched r Qonly) := by
  classical
  intro fg
  have hm := switched_marked r Qonly fg
  apply Prod.ext <;> funext v
  all_goals
    change (if Marked r (switched r Qonly fg).1 (switched r Qonly fg).2 Qonly v
      then _ else _) = _
    rw [hm]
    by_cases h : Marked r fg.1 fg.2 Qonly v <;> simp [switched, h]

theorem switched_injective (r : V → V → Prop) (Qonly : Set V) :
    Function.Injective (switched r Qonly) :=
  (switched_involutive r Qonly).injective

/-- A zero-extended strict map with a specified positive support and label bound. -/
def MapOn (r : V → V → Prop) (P : Set V) (m : ℕ) (f : V → ℕ) : Prop :=
  Admissible r f ∧ (∀ v, 0 < f v ↔ v ∈ P) ∧ ∀ v, f v ≤ m

theorem switched_maps {r : V → V → Prop} {P Q : Set V} {m j : ℕ}
    {f g : V → ℕ} (hjm : j ≤ m) (hf : MapOn r P m f) (hg : MapOn r Q j g) :
    MapOn r (P ∪ Q) m (switched r (Q \ P) (f,g)).1 ∧
    MapOn r (P ∩ Q) j (switched r (Q \ P) (f,g)).2 := by
  classical
  obtain ⟨hfa, hfs, hfb⟩ := hf
  obtain ⟨hga, hgs, hgb⟩ := hg
  have hq : ∀ v ∈ Q \ P, f v < g v := by
    intro v hv
    have hfzero : f v = 0 := by
      by_contra hn
      exact hv.2 ((hfs v).mp (Nat.pos_of_ne_zero hn))
    have hgpos : 0 < g v := (hgs v).mpr hv.1
    omega
  have had := switched_admissible hfa hga hq
  have hl : ∀ {v}, Marked r f g (Q \ P) v → f v < g v :=
    marked_low hfa hga hq
  have hmark : ∀ v, v ∈ Q → v ∉ P → Marked r f g (Q \ P) v := by
    intro v h1 h2
    exact marked_of_mem ⟨h1,h2⟩
  refine ⟨⟨had.1, ?_, ?_⟩, ⟨had.2, ?_, ?_⟩⟩
  · intro v
    have h1 := hfs v
    have h2 := hgs v
    have hm := hmark v
    by_cases hs : Marked r f g (Q \ P) v
    · have hlow := hl hs
      simp only [switched, hs, if_true, Set.mem_union]
      constructor
      · intro h
        exact Or.inr (h2.mp h)
      · rintro (h | h)
        · exact (h1.mpr h).trans hlow
        · exact h2.mpr h
    · simp only [switched, hs, if_false, Set.mem_union]
      constructor
      · intro h
        exact Or.inl (h1.mp h)
      · rintro (h | h)
        · exact h1.mpr h
        · by_cases hp : v ∈ P
          · exact h1.mpr hp
          · exact False.elim (hs (hm h hp))
  · intro v
    by_cases hs : Marked r f g (Q \ P) v
    · simpa only [switched, hs, if_true] using (hgb v).trans hjm
    · simpa only [switched, hs, if_false] using hfb v
  · intro v
    have h1 := hfs v
    have h2 := hgs v
    have hm := hmark v
    by_cases hs : Marked r f g (Q \ P) v
    · have hlow := hl hs
      simp only [switched, hs, if_true, Set.mem_inter_iff]
      constructor
      · intro h
        exact ⟨h1.mp h, h2.mp (h.trans hlow)⟩
      · intro h
        exact h1.mpr h.1
    · simp only [switched, hs, if_false, Set.mem_inter_iff]
      constructor
      · intro h
        have hqv := h2.mp h
        refine ⟨?_, hqv⟩
        by_contra hp
        exact hs (hm hqv hp)
      · intro h
        exact h2.mpr h.2
  · intro v
    by_cases hs : Marked r f g (Q \ P) v
    · simpa only [switched, hs, if_true] using (hl hs).le.trans (hgb v)
    · simpa only [switched, hs, if_false] using hgb v

/-- At every vertex, switching preserves the two labels as an unordered pair. -/
theorem switched_weight (r : V → V → Prop) (Qonly : Set V)
    (fg : (V → ℕ) × (V → ℕ)) (w : ℕ → ℕ) (v : V) :
    w ((switched r Qonly fg).1 v) + w ((switched r Qonly fg).2 v) =
      w (fg.1 v) + w (fg.2 v) := by
  classical
  by_cases h : Marked r fg.1 fg.2 Qonly v <;> simp [switched, h, Nat.add_comm]

theorem switched_total_weight [Fintype V] (r : V → V → Prop) (Qonly : Set V)
    (fg : (V → ℕ) × (V → ℕ)) (w : ℕ → ℕ) :
    (∑ v, w ((switched r Qonly fg).1 v)) + (∑ v, w ((switched r Qonly fg).2 v)) =
      (∑ v, w (fg.1 v)) + (∑ v, w (fg.2 v)) := by
  simp only [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun v _ => switched_weight r Qonly fg w v)

def PairMaps (r : V → V → Prop) (P Q : Set V) (m j : ℕ) :=
  {fg : (V → ℕ) × (V → ℕ) // MapOn r P m fg.1 ∧ MapOn r Q j fg.2}

/-- The complete union--intersection injection, with different label bounds. -/
noncomputable def unionIntersectionInjection (r : V → V → Prop)
    (P Q : Set V) {m j : ℕ} (hjm : j ≤ m) :
    PairMaps r P Q m j ↪ PairMaps r (P ∪ Q) (P ∩ Q) m j where
  toFun fg := ⟨switched r (Q \ P) fg.val,
    switched_maps hjm fg.property.1 fg.property.2⟩
  inj' := by
    intro x y h
    apply Subtype.ext
    exact switched_injective r (Q \ P) (congrArg Subtype.val h)

/-- This specializes to each label multiplicity with w(t) = if t = k then 1 else 0. -/
theorem unionIntersectionInjection_preserves_weight [Fintype V]
    (r : V → V → Prop) (P Q : Set V) {m j : ℕ} (hjm : j ≤ m)
    (fg : PairMaps r P Q m j) (w : ℕ → ℕ) :
    (∑ v, w ((unionIntersectionInjection r P Q hjm fg).val.1 v)) +
      (∑ v, w ((unionIntersectionInjection r P Q hjm fg).val.2 v)) =
    (∑ v, w (fg.val.1 v)) + (∑ v, w (fg.val.2 v)) :=
  switched_total_weight r (Q \ P) fg.val w

instance pairMaps_finite [Finite V] (r : V → V → Prop) (P Q : Set V) (m j : ℕ) :
    Finite (PairMaps r P Q m j) := by
  let e : PairMaps r P Q m j → (V → Fin (m+1)) × (V → Fin (j+1)) := fun fg =>
    (fun v => ⟨fg.val.1 v, Nat.lt_succ_of_le (fg.property.1.2.2 v)⟩,
     fun v => ⟨fg.val.2 v, Nat.lt_succ_of_le (fg.property.2.2.2 v)⟩)
  apply Finite.of_injective e
  intro x y h
  apply Subtype.ext
  apply Prod.ext <;> funext v
  · exact congrArg (fun p => (p.1 v).val) h
  · exact congrArg (fun p => (p.2 v).val) h

/-- Multiplicities of positive labels in a pair of zero-extended maps. -/
noncomputable def profile [Fintype V] (fg : (V → ℕ) × (V → ℕ)) : ℕ → ℕ := by
  classical
  exact fun k => (∑ v, if fg.1 v = k+1 then 1 else 0) +
    (∑ v, if fg.2 v = k+1 then 1 else 0)

theorem unionIntersectionInjection_profile [Fintype V]
    (r : V → V → Prop) (P Q : Set V) {m j : ℕ} (hjm : j ≤ m)
    (fg : PairMaps r P Q m j) :
    profile (unionIntersectionInjection r P Q hjm fg).val = profile fg.val := by
  classical
  funext k
  exact unionIntersectionInjection_preserves_weight r P Q hjm fg
    (fun t => if t = k+1 then 1 else 0)

noncomputable def profileInjection [Fintype V] (r : V → V → Prop)
    (P Q : Set V) {m j : ℕ} (hjm : j ≤ m) (c : ℕ → ℕ) :
    {fg : PairMaps r P Q m j // profile fg.val = c} ↪
      {fg : PairMaps r (P ∪ Q) (P ∩ Q) m j // profile fg.val = c} where
  toFun fg := ⟨unionIntersectionInjection r P Q hjm fg.val, by
    rw [unionIntersectionInjection_profile]
    exact fg.property⟩
  inj' := by
    intro x y h
    apply Subtype.ext
    exact (unionIntersectionInjection r P Q hjm).injective (congrArg Subtype.val h)

/-- Each separate label-histogram coefficient satisfies the required inequality. -/
theorem profile_card_le [Fintype V] (r : V → V → Prop)
    (P Q : Set V) {m j : ℕ} (hjm : j ≤ m) (c : ℕ → ℕ) :
    Nat.card {fg : PairMaps r P Q m j // profile fg.val = c} ≤
      Nat.card {fg : PairMaps r (P ∪ Q) (P ∩ Q) m j // profile fg.val = c} :=
  Nat.card_le_card_of_injective (profileInjection r P Q hjm c)
    (profileInjection r P Q hjm c).injective


end DickeyRosenbergSwitching


namespace DickeyRosenberg

/-- An auxiliary recursive presentation of a full binary tree. -/
inductive BTree where
  | leaf : BTree
  | fork : BTree → BTree → BTree
  deriving DecidableEq

namespace BTree

@[simp] def leaves : BTree → ℕ
  | leaf => 1
  | fork a b => a.leaves + b.leaves

theorem leaves_pos (t : BTree) : 0 < t.leaves := by
  induction t with
  | leaf => simp
  | fork a b ha hb => simp only [leaves]; omega

@[simp] def mirror : BTree → BTree
  | leaf => leaf
  | fork a b => fork b.mirror a.mirror

@[simp] theorem mirror_mirror (t : BTree) : t.mirror.mirror = t := by
  induction t <;> simp_all

@[simp] theorem leaves_mirror (t : BTree) : t.mirror.leaves = t.leaves := by
  induction t <;> simp_all [Nat.add_comm]

/-- Union and intersection of internal vertex sets in the common binary tree. -/
@[simp] def union : BTree → BTree → BTree
  | leaf, b => b
  | a, leaf => a
  | fork a b, fork c d => fork (a.union c) (b.union d)

@[simp] def inter : BTree → BTree → BTree
  | leaf, _ => leaf
  | _, leaf => leaf
  | fork a b, fork c d => fork (a.inter c) (b.inter d)

@[simp] theorem union_leaf (a : BTree) : a.union leaf = a := by cases a <;> rfl
@[simp] theorem inter_leaf (a : BTree) : a.inter leaf = leaf := by cases a <;> rfl

theorem leaves_union_add_inter (a b : BTree) :
    (a.union b).leaves + (a.inter b).leaves = a.leaves + b.leaves := by
  induction a generalizing b with
  | leaf => simp [Nat.add_comm]
  | fork a₁ a₂ h₁ h₂ =>
    cases b with
    | leaf => simp
    | fork b₁ b₂ =>
      simp only [union, inter, leaves]
      have := h₁ b₁
      have := h₂ b₂
      omega

/-- The perfect tree of height `k`, with the first `x` leaves expanded.
Only inputs `x ≤ 2^k` are used. -/
@[simp] def fill : ℕ → ℕ → BTree
  | 0, x => if x = 0 then leaf else fork leaf leaf
  | k + 1, x => fork (fill k (min x (2^k))) (fill k (x - 2^k))

theorem leaves_fill (k x : ℕ) (hx : x ≤ 2^k) :
    (fill k x).leaves = 2^k + x := by
  induction k generalizing x with
  | zero =>
    simp only [pow_zero] at hx ⊢
    by_cases h : x = 0
    · simp [h]
    · have : x = 1 := by omega
      simp [this]
  | succ k ih =>
    have hr : x - 2^k ≤ 2^k := by rw [pow_succ] at hx; omega
    simp only [fill, leaves, ih _ (min_le_right _ _), ih _ hr, pow_succ]
    omega

theorem union_fill_mirror_leaves (k x y : ℕ) (hx : x ≤ 2^k) (hy : y ≤ 2^k) :
    ((fill k x).union (fill k y).mirror).leaves = 2^k + min (2^k) (x+y) := by
  induction k generalizing x y with
  | zero =>
    simp only [pow_zero] at hx hy ⊢
    interval_cases x <;> interval_cases y <;> simp
  | succ k ih =>
    have hx' : x ≤ 2^k * 2 := by simpa [pow_succ] using hx
    have hy' : y ≤ 2^k * 2 := by simpa [pow_succ] using hy
    have h₁ := ih (min x (2^k)) (y - 2^k) (min_le_right _ _) (by omega)
    have h₂ := ih (x - 2^k) (min y (2^k)) (by omega) (min_le_right _ _)
    simp only [fill, mirror, union, leaves] at ⊢
    rw [h₁, h₂, pow_succ]
    omega

theorem inter_fill_mirror_leaves (k x y : ℕ) (hx : x ≤ 2^k) (hy : y ≤ 2^k) :
    ((fill k x).inter (fill k y).mirror).leaves = 2^k + (x+y-2^k) := by
  have h := leaves_union_add_inter (fill k x) (fill k y).mirror
  rw [union_fill_mirror_leaves k x y hx hy, leaves_mirror,
    leaves_fill k x hx, leaves_fill k y hy] at h
  omega

theorem fill_full (k : ℕ) : fill k (2^k) = fill (k+1) 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [fill, pow_succ, Nat.min_eq_right (by omega : 2^k ≤ 2^k * 2)]
    have h : 2^k * 2 - 2^k = 2^k := by omega
    rw [h, ih]
    simp

end BTree
end DickeyRosenberg

namespace DickeyRosenberg

namespace Path

def walk : ℕ → List Bool → ℕ
  | v, [] => v
  | v, b :: p => walk (2*v + b.toNat) p

def heap (p : List Bool) : ℕ := walk 1 p

@[simp] theorem walk_nil (v : ℕ) : walk v [] = v := rfl
@[simp] theorem heap_nil : heap [] = 1 := rfl

theorem walk_append (v : ℕ) (p q : List Bool) :
    walk v (p ++ q) = walk (walk v p) q := by
  induction p generalizing v with
  | nil => rfl
  | cons b p ih => exact ih _

@[simp] theorem heap_snoc (p : List Bool) (b : Bool) :
    heap (p ++ [b]) = 2 * heap p + b.toNat := by
  simp [heap, walk_append, walk]

theorem walk_affine (v : ℕ) (p : List Bool) :
    walk v p = v * 2^p.length + walk 0 p := by
  induction p generalizing v with
  | nil => simp [walk]
  | cons b p ih =>
    simp only [walk, List.length_cons, pow_succ]
    rw [ih (2*v+b.toNat), ih (2*0+b.toNat)]
    ring

theorem heap_cons (b : Bool) (p : List Bool) :
    heap (b :: p) = heap p + (1+b.toNat) * 2^p.length := by
  simp only [heap, walk]
  rw [walk_affine (2*1+b.toNat), walk_affine 1]
  ring

theorem heap_bounds (p : List Bool) : 2^p.length ≤ heap p ∧ heap p < 2^(p.length+1) := by
  induction p with
  | nil => simp
  | cons b p ih =>
    have hp : 0 < 2^p.length := by positivity
    rw [heap_cons, List.length_cons]
    simp only [pow_succ]
    cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;>
      simp only [pow_succ] at ih <;> omega

theorem heap_pos (p : List Bool) : 0 < heap p :=
  (by positivity : 0 < 2^p.length).trans_le (heap_bounds p).1

@[simp] theorem heap_eq_one (p : List Bool) : heap p = 1 ↔ p = [] := by
  cases p with
  | nil => simp
  | cons b p =>
    have h := heap_pos p
    have hp : 0 < 2^p.length := by positivity
    rw [heap_cons]
    cases b <;> simp only [Bool.toNat_false, Bool.toNat_true,
      List.cons_ne_nil, iff_false] <;> omega

theorem heap_injective : Function.Injective heap := by
  intro p
  induction p using List.reverseRecOn with
  | nil =>
    intro q h
    exact ((heap_eq_one q).mp h.symm).symm
  | append_singleton p b ih =>
    intro q h
    cases q using List.reverseRecOn with
    | nil =>
      have := (heap_eq_one (p ++ [b])).mp h
      simp at this
    | append_singleton q c =>
      simp only [heap_snoc] at h
      have hbc : b = c := by cases b <;> cases c <;> simp_all <;> omega
      subst c
      have hpq : heap p = heap q := by omega
      rw [ih hpq]

theorem heap_surjective_pos (n : ℕ) (hn : 0 < n) : ∃ p, heap p = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h1 : n = 1
    · exact ⟨[], h1.symm⟩
    · have h2 : 1 < n := by omega
      obtain ⟨p, hp⟩ := ih (n/2) (by omega) (by omega)
      by_cases he : n % 2 = 0
      · exact ⟨p ++ [false], by simp [hp]; omega⟩
      · exact ⟨p ++ [true], by simp [hp]; omega⟩

def Edge (u v : List Bool) : Prop := ∃ b, u = v ++ [b]

theorem edge_heap_iff (u v : List Bool) : Edge u v ↔ Parent (heap u) (heap v) := by
  constructor
  · rintro ⟨b, rfl⟩
    have hp := heap_pos v
    simp only [Parent, heap_snoc]
    cases b <;> simp <;> omega
  · intro h
    have hu : u ≠ [] := by intro he; subst u; simp [Parent] at h
    cases u using List.reverseRecOn with
    | nil => exact False.elim (hu rfl)
    | append_singleton p b =>
      have hp : heap p = heap v := by
        simp only [Parent, heap_snoc] at h
        cases b <;> simp_all <;> omega
      exact ⟨b, by rw [heap_injective hp]⟩

end Path

namespace BTree

@[simp] def nodes : BTree → Finset (List Bool)
  | leaf => ∅
  | fork a b => insert [] ((a.nodes.image (false :: ·)) ∪ (b.nodes.image (true :: ·)))

@[simp] theorem nil_mem_nodes (a b : BTree) : [] ∈ (fork a b).nodes := by simp

@[simp] theorem false_mem_nodes (a b : BTree) (p : List Bool) :
    false :: p ∈ (fork a b).nodes ↔ p ∈ a.nodes := by simp

@[simp] theorem true_mem_nodes (a b : BTree) (p : List Bool) :
    true :: p ∈ (fork a b).nodes ↔ p ∈ b.nodes := by simp

theorem nodes_card (t : BTree) : t.nodes.card + 1 = t.leaves := by
  induction t with
  | leaf => simp
  | fork a b ha hb =>
    have hd : Disjoint (a.nodes.image (false :: ·)) (b.nodes.image (true :: ·)) := by
      simp [Finset.disjoint_left]
    simp only [nodes]
    rw [Finset.card_insert_of_notMem (by simp), Finset.card_union_of_disjoint hd,
      Finset.card_image_of_injective _ (fun _ _ h => List.cons.inj h |>.2),
      Finset.card_image_of_injective _ (fun _ _ h => List.cons.inj h |>.2)]
    simp only [leaves]
    omega

theorem nodes_closed (t : BTree) {p : List Bool} {b : Bool}
    (h : p ++ [b] ∈ t.nodes) : p ∈ t.nodes := by
  induction t generalizing p with
  | leaf => simp at h
  | fork a c ha hc =>
    cases p with
    | nil => simp
    | cons d p =>
      cases d with
      | false => exact (false_mem_nodes a c p).mpr (ha (by simpa using h))
      | true => exact (true_mem_nodes a c p).mpr (hc (by simpa using h))

theorem nodes_union (a b : BTree) : (a.union b).nodes = a.nodes ∪ b.nodes := by
  induction a generalizing b with
  | leaf => simp
  | fork a₁ a₂ h₁ h₂ =>
    cases b with
    | leaf => simp
    | fork b₁ b₂ =>
      ext p
      cases p with
      | nil => simp
      | cons c p => cases c <;> simp [h₁, h₂]

theorem nodes_inter (a b : BTree) : (a.inter b).nodes = a.nodes ∩ b.nodes := by
  induction a generalizing b with
  | leaf => simp
  | fork a₁ a₂ h₁ h₂ =>
    cases b with
    | leaf => simp
    | fork b₁ b₂ =>
      ext p
      cases p with
      | nil => simp
      | cons c p => cases c <;> simp [h₁, h₂]

theorem nodes_injective : Function.Injective nodes := by
  intro a
  induction a with
  | leaf =>
    intro b h
    cases b with
    | leaf => rfl
    | fork b₁ b₂ => have := congrArg (fun s => [] ∈ s) h; simp at this
  | fork a₁ a₂ h₁ h₂ =>
    intro b h
    cases b with
    | leaf => have := congrArg (fun s => [] ∈ s) h; simp at this
    | fork b₁ b₂ =>
      congr 1
      · apply h₁
        ext p
        have := congrArg (fun s => false :: p ∈ s) h
        simpa using this
      · apply h₂
        ext p
        have := congrArg (fun s => true :: p ∈ s) h
        simpa using this

end BTree
end DickeyRosenberg

namespace DickeyRosenberg
namespace BTree

theorem mem_fill_by_level (k x : ℕ) (hx : x ≤ 2^k) (p : List Bool) :
    p ∈ (fill k x).nodes ↔
      p.length < k ∨ (p.length = k ∧ Path.heap p < 2^k+x) := by
  induction k generalizing x p with
  | zero =>
    have h : x = 0 ∨ x = 1 := by simp only [pow_zero] at hx; omega
    rcases h with rfl | rfl <;> cases p with
    | nil => simp
    | cons b p => cases b <;> simp
  | succ k ih =>
    have hx' : x ≤ 2^k * 2 := by simpa [pow_succ] using hx
    cases p with
    | nil => simp
    | cons b p =>
      have h₁ := ih (min x (2^k)) (min_le_right _ _) p
      have h₂ := ih (x - 2^k) (by omega) p
      simp only [fill]
      cases b <;> simp only [false_mem_nodes, true_mem_nodes, h₁, h₂,
        List.length_cons, Path.heap_cons, Bool.toNat_false, Bool.toNat_true, pow_succ]
      all_goals
        rcases lt_trichotomy p.length k with hl | hl | hl
        · omega
        · have hb := Path.heap_bounds p
          simp only [hl, pow_succ] at hb ⊢
          simp only [lt_self_iff_false, false_or, true_and, Nat.add_zero,
            Nat.one_mul, Nat.reduceAdd]
          omega
        · omega

theorem mem_fill (k x : ℕ) (hx : x ≤ 2^k) (p : List Bool) :
    p ∈ (fill k x).nodes ↔ Path.heap p < 2^k+x := by
  rw [mem_fill_by_level k x hx p]
  have hb := Path.heap_bounds p
  rcases lt_trichotomy p.length k with hl | hl | hl
  · have hpow : 2^(p.length+1) ≤ 2^k := Nat.pow_le_pow_right (by omega) hl
    omega
  · simp [hl]
  · have hpow : 2^(k+1) ≤ 2^p.length := Nat.pow_le_pow_right (by omega) hl
    rw [pow_succ] at hpow
    omega

/-- The breadth-first complete tree with `n` leaves, for positive `n`. -/
def complete (n : ℕ) : BTree := fill (Nat.log 2 n) (n - 2^(Nat.log 2 n))

theorem complete_mem {n : ℕ} (hn : 0 < n) (p : List Bool) :
    p ∈ (complete n).nodes ↔ Path.heap p < n := by
  have hlo := Nat.pow_log_le_self 2 (by omega : n ≠ 0)
  have hhi := Nat.lt_pow_succ_log_self (by omega : 1 < 2) n
  unfold complete
  rw [mem_fill _ _ (by rw [pow_succ] at hhi; omega)]
  omega

theorem leaves_complete {n : ℕ} (hn : 0 < n) : (complete n).leaves = n := by
  have hlo := Nat.pow_log_le_self 2 (by omega : n ≠ 0)
  have hhi := Nat.lt_pow_succ_log_self (by omega : 1 < 2) n
  unfold complete
  rw [leaves_fill _ _ (by rw [pow_succ] at hhi; omega)]
  omega

theorem complete_eq_fill (k x : ℕ) (hx : x ≤ 2^k) :
    complete (2^k+x) = fill k x := by
  apply nodes_injective
  ext p
  rw [complete_mem (by positivity), mem_fill k x hx]

@[simp] theorem complete_one : complete 1 = leaf := by
  have h := complete_eq_fill 0 0 (by norm_num)
  simpa using h

theorem complete_nested {a d : ℕ} (ha : 0 < a) (had : a ≤ d) :
    (complete a).nodes ⊆ (complete d).nodes := by
  intro p hp
  rw [complete_mem (ha.trans_le had)]
  exact ((complete_mem ha p).mp hp).trans_le had

theorem complete_dyadic_split_low (k n : ℕ) (hl : 2 * 2^k ≤ n)
    (hh : n ≤ 3 * 2^k) :
    complete n = fork (complete (n - 2^k)) (complete (2^k)) := by
  have hp : 0 < 2^k := by positivity
  have hn : n = 2^(k+1) + (n - 2 * 2^k) := by rw [pow_succ]; omega
  rw [hn, complete_eq_fill _ _ (by rw [pow_succ]; omega)]
  simp only [fill]
  have hmin : min (n - 2 * 2^k) (2^k) = n - 2 * 2^k := by omega
  have hsub : n - 2 * 2^k - 2^k = 0 := by omega
  rw [hmin, hsub]
  congr 1
  · have he : 2^(k+1) + (n - 2 * 2^k) - 2^k = 2^k + (n - 2 * 2^k) := by
      rw [pow_succ]; omega
    rw [he, complete_eq_fill _ _ (by omega)]
  · have := complete_eq_fill k 0 (by omega)
    simpa using this.symm

theorem complete_dyadic_split_high (k n : ℕ) (hl : 3 * 2^k ≤ n)
    (hh : n ≤ 4 * 2^k) :
    complete n = fork (complete (2 * 2^k)) (complete (n - 2 * 2^k)) := by
  have hp : 0 < 2^k := by positivity
  have hn : n = 2^(k+1) + (n - 2 * 2^k) := by rw [pow_succ]; omega
  rw [hn, complete_eq_fill _ _ (by rw [pow_succ]; omega)]
  simp only [fill]
  have hmin : min (n - 2 * 2^k) (2^k) = 2^k := by omega
  rw [hmin]
  congr 1
  · have he : 2 * 2^k = 2^k + 2^k := by omega
    rw [he, complete_eq_fill _ _ le_rfl]
  · have he : 2^(k+1) + (n - 2 * 2^k) - 2 * 2^k =
        2^k + (n - 2 * 2^k - 2^k) := by rw [pow_succ]; omega
    rw [he, complete_eq_fill _ _ (by omega)]

end BTree
end DickeyRosenberg

namespace DickeyRosenberg

@[ext] theorem Shape.ext {T S : Shape} (h : T.nodes = S.nodes) : T = S := by
  cases T
  cases S
  congr

namespace Path

def Closed (s : Finset (List Bool)) : Prop :=
  ∀ p b, p ++ [b] ∈ s → p ∈ s

theorem nil_mem_of_mem {s : Finset (List Bool)} (hs : Closed s)
    {p : List Bool} (hp : p ∈ s) : [] ∈ s := by
  induction p using List.reverseRecOn with
  | nil => exact hp
  | append_singleton p b ih => exact ih (hs p b hp)

noncomputable def branch (s : Finset (List Bool)) (b : Bool) : Finset (List Bool) :=
  s.preimage (List.cons b) (fun _ _ _ _ h => (List.cons.inj h).2)

@[simp] theorem mem_branch (s : Finset (List Bool)) (b : Bool) (p : List Bool) :
    p ∈ branch s b ↔ b :: p ∈ s := Finset.mem_preimage

theorem branch_closed {s : Finset (List Bool)} (hs : Closed s) (b : Bool) :
    Closed (branch s b) := by
  intro p c h
  rw [mem_branch] at h ⊢
  exact hs (b :: p) c h

theorem branch_card_lt {s : Finset (List Bool)} (hs : [] ∈ s) (b : Bool) :
    (branch s b).card < s.card := by
  have hsub : (branch s b).image (List.cons b) ⊂ s := by
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      exact (mem_branch s b q).mp hq
    · intro he
      have : [] ∈ (branch s b).image (List.cons b) := by rw [he]; exact hs
      simp at this
  have h := Finset.card_lt_card hsub
  rwa [Finset.card_image_of_injective _ (fun _ _ h => (List.cons.inj h).2)] at h

theorem realize (s : Finset (List Bool)) (hs : Closed s) :
    ∃ t : BTree, t.nodes = s := by
  by_cases he : s = ∅
  · exact ⟨.leaf, he.symm⟩
  · have hroot : [] ∈ s := by
      obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr he
      exact nil_mem_of_mem hs hp
    obtain ⟨a, ha⟩ := realize (branch s false) (branch_closed hs false)
    obtain ⟨b, hb⟩ := realize (branch s true) (branch_closed hs true)
    refine ⟨.fork a b, ?_⟩
    ext p
    cases p with
    | nil => simp [hroot]
    | cons c p => cases c <;> simp [ha, hb]
termination_by s.card
decreasing_by all_goals exact branch_card_lt hroot _

end Path

namespace BTree

def toShape (t : BTree) : Shape where
  nodes := t.nodes.image Path.heap
  positive := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
    exact Path.heap_pos p
  closed := by
    intro v hv h1
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
    cases p using List.reverseRecOn with
    | nil => simp at h1
    | append_singleton p b =>
      have hdiv : Path.heap (p ++ [b]) / 2 = Path.heap p := by
        rw [Path.heap_snoc]
        cases b <;> simp <;> omega
      rw [hdiv]
      exact Finset.mem_image.mpr ⟨p, nodes_closed t hp, rfl⟩

@[simp] theorem toShape_leaves (t : BTree) : t.toShape.leaves = t.leaves := by
  simp only [Shape.leaves, toShape,
    Finset.card_image_of_injective _ Path.heap_injective, nodes_card]

theorem toShape_complete {n : ℕ} (hn : 0 < n) : (complete n).toShape = canonical n := by
  apply Shape.ext
  ext v
  simp only [toShape, canonical, Finset.mem_image, Finset.mem_Ico]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨Path.heap_pos p, (complete_mem hn p).mp hp⟩
  · rintro ⟨hv, hvn⟩
    obtain ⟨p, rfl⟩ := Path.heap_surjective_pos v hv
    exact ⟨p, (complete_mem hn p).mpr hvn, rfl⟩

theorem toShape_surjective : Function.Surjective toShape := by
  intro T
  let s := T.nodes.preimage Path.heap Path.heap_injective.injOn
  have hs : Path.Closed s := by
    intro p b hp
    apply Finset.mem_preimage.mpr
    have hpb : Path.heap (p ++ [b]) ∈ T.nodes := Finset.mem_preimage.mp hp
    have hparent := (Path.edge_heap_iff (p ++ [b]) p).mp ⟨b, rfl⟩
    rw [← hparent.2]
    exact T.closed _ hpb hparent.1
  obtain ⟨t, ht⟩ := Path.realize s hs
  refine ⟨t, Shape.ext ?_⟩
  change t.nodes.image Path.heap = T.nodes
  rw [ht]
  ext v
  simp only [Finset.mem_image, s, Finset.mem_preimage]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp
  · intro hv
    obtain ⟨p, rfl⟩ := Path.heap_surjective_pos v (T.positive _ hv)
    exact ⟨p, hv, rfl⟩

end BTree
end DickeyRosenberg

namespace DickeyRosenberg

abbrev Poly := MvPolynomial ℕ ℕ

/-- Coefficientwise comparison of polynomials with natural coefficients. -/
instance polyPartialOrder : PartialOrder Poly where
  le p q := ∀ c, MvPolynomial.coeff c p ≤ MvPolynomial.coeff c q
  le_refl _ _ := le_rfl
  le_trans _ _ _ h₁ h₂ c := (h₁ c).trans (h₂ c)
  le_antisymm p q h₁ h₂ := MvPolynomial.ext p q (fun c => le_antisymm (h₁ c) (h₂ c))

theorem poly_mul_mono {p q r s : Poly} (hp : p ≤ q) (hr : r ≤ s) : p*r ≤ q*s := by
  intro c
  simp only [MvPolynomial.coeff_mul]
  exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul (hp i.1) (hr i.2))

theorem poly_sum_mono {ι : Type*} (s : Finset ι) {p q : ι → Poly}
    (h : ∀ i ∈ s, p i ≤ q i) : (∑ i ∈ s, p i) ≤ ∑ i ∈ s, q i := by
  intro c
  simp only [MvPolynomial.coeff_sum]
  exact Finset.sum_le_sum (fun i hi => h i hi c)

theorem poly_sum_injection {α β : Type*} [Fintype α] [Fintype β]
    (e : α ↪ β) (f : α → Poly) (g : β → Poly) (h : ∀ a, f a = g (e a)) :
    (∑ a, f a) ≤ ∑ b, g b := by
  classical
  intro c
  simp only [MvPolynomial.coeff_sum]
  calc
    (∑ a, MvPolynomial.coeff c (f a)) = ∑ a, MvPolynomial.coeff c (g (e a)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [h a]
    _ = ∑ b ∈ Finset.univ.image e, MvPolynomial.coeff c (g b) :=
      (Finset.sum_image (s := Finset.univ) (f := fun b => MvPolynomial.coeff c (g b))
        e.injective.injOn).symm
    _ ≤ ∑ b, MvPolynomial.coeff c (g b) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; omega)

noncomputable def labelWeight (n : ℕ) : Poly :=
  if n = 0 then 1 else MvPolynomial.X (n-1)

@[simp] theorem labelWeight_zero : labelWeight 0 = 1 := by simp [labelWeight]
@[simp] theorem labelWeight_succ (n : ℕ) : labelWeight (n+1) = MvPolynomial.X n := by
  simp [labelWeight]

namespace BTree

open DickeyRosenbergSwitching

abbrev Labeling (t : BTree) (m : ℕ) :=
  {f : List Bool → ℕ // MapOn Path.Edge (t.nodes : Set (List Bool)) m f}

instance labeling_finite (t : BTree) (m : ℕ) : Finite (Labeling t m) := by
  let e : Labeling t m → ({p // p ∈ t.nodes} → Fin (m+1)) := fun f p =>
    ⟨f.val p, Nat.lt_succ_of_le (f.property.2.2 p)⟩
  apply Finite.of_injective e
  intro f g h
  apply Subtype.ext
  funext p
  by_cases hp : p ∈ t.nodes
  · exact congrArg (fun k => (k ⟨p, hp⟩).val) h
  · have hf := f.property.2.1 p
    have hg := g.property.2.1 p
    change (0 < f.val p ↔ p ∈ t.nodes) at hf
    change (0 < g.val p ↔ p ∈ t.nodes) at hg
    have hf0 : f.val p = 0 := Nat.eq_zero_of_not_pos (fun h => hp (hf.mp h))
    have hg0 : g.val p = 0 := Nat.eq_zero_of_not_pos (fun h => hp (hg.mp h))
    omega

noncomputable instance labeling_fintype (t : BTree) (m : ℕ) : Fintype (Labeling t m) :=
  Fintype.ofFinite _

theorem labeling_zero_off {t : BTree} {m : ℕ} (f : Labeling t m)
    {p : List Bool} (hp : p ∉ t.nodes) : f.val p = 0 := by
  have hf := f.property.2.1 p
  change (0 < f.val p ↔ p ∈ t.nodes) at hf
  exact Nat.eq_zero_of_not_pos (fun h => hp (hf.mp h))

noncomputable def weight (t : BTree) (f : List Bool → ℕ) : Poly :=
  ∏ p ∈ t.nodes, labelWeight (f p)

noncomputable def K (t : BTree) (m : ℕ) : Poly := ∑ f : Labeling t m, weight t f.val

theorem weight_extend {t : BTree} {m : ℕ} (f : Labeling t m)
    (s : Finset (List Bool)) (hs : t.nodes ⊆ s) :
    weight t f.val = ∏ p ∈ s, labelWeight (f.val p) := by
  apply Finset.prod_subset hs
  intro p _ hp
  rw [labeling_zero_off f hp, labelWeight_zero]

theorem admissible_root_bound {f : List Bool → ℕ} (hf : Admissible Path.Edge f)
    (p : List Bool) : f p ≤ f [] := by
  induction p using List.reverseRecOn with
  | nil => exact le_rfl
  | append_singleton p b ih =>
    have h := hf (p ++ [b]) p ⟨b, rfl⟩
    omega

theorem admissible_prepend {f : List Bool → ℕ} (hf : Admissible Path.Edge f) (b : Bool) :
    Admissible Path.Edge (fun p => f (b :: p)) := by
  rintro p q ⟨c, rfl⟩
  exact hf ((b :: q) ++ [c]) (b :: q) ⟨c, rfl⟩

theorem labeling_branch_bound {a b : BTree} {m : ℕ} (f : Labeling (fork a b) m)
    (c : Bool) (p : List Bool) : f.val (c :: p) ≤ f.val [] - 1 := by
  have h₁ := admissible_root_bound (admissible_prepend f.property.1 c) p
  have h₂ := f.property.1 [c] [] ⟨c, rfl⟩
  omega

noncomputable def labelingRoot {a b : BTree} {m : ℕ} (f : Labeling (fork a b) m) : Fin m :=
  ⟨f.val [] - 1, by
    have hpos := (f.property.2.1 []).mpr (nil_mem_nodes a b)
    have hbound := f.property.2.2 []
    omega⟩

noncomputable def labelingLeft {a b : BTree} {m : ℕ} (f : Labeling (fork a b) m) :
    Labeling a (labelingRoot f).val :=
  ⟨(fun p => f.val (false :: p)), admissible_prepend f.property.1 false,
    (fun p => (f.property.2.1 (false :: p)).trans (false_mem_nodes a b p)),
    labeling_branch_bound f false⟩

noncomputable def labelingRight {a b : BTree} {m : ℕ} (f : Labeling (fork a b) m) :
    Labeling b (labelingRoot f).val :=
  ⟨(fun p => f.val (true :: p)), admissible_prepend f.property.1 true,
    (fun p => (f.property.2.1 (true :: p)).trans (true_mem_nodes a b p)),
    labeling_branch_bound f true⟩

def combineFun (j : ℕ) (f g : List Bool → ℕ) : List Bool → ℕ
  | [] => j+1
  | false :: p => f p
  | true :: p => g p

noncomputable def combine {a b : BTree} {m : ℕ} (j : Fin m)
    (f : Labeling a j.val) (g : Labeling b j.val) : Labeling (fork a b) m := by
  refine ⟨combineFun j.val f.val g.val, ?_, ?_, ?_⟩
  · rintro u v ⟨c, rfl⟩
    cases v with
    | nil =>
      cases c
      · have h := f.property.2.2 []; simp only [List.nil_append, combineFun]; omega
      · have h := g.property.2.2 []; simp only [List.nil_append, combineFun]; omega
    | cons d v =>
      cases d
      · exact f.property.1 (v ++ [c]) v ⟨c, rfl⟩
      · exact g.property.1 (v ++ [c]) v ⟨c, rfl⟩
  · intro p
    cases p with
    | nil => simp [combineFun]
    | cons c p =>
      cases c
      · exact (f.property.2.1 p).trans (false_mem_nodes a b p).symm
      · exact (g.property.2.1 p).trans (true_mem_nodes a b p).symm
  · intro p
    cases p with
    | nil => simp only [combineFun]; exact j.isLt
    | cons c p =>
      cases c
      · exact (f.property.2.2 p).trans j.isLt.le
      · exact (g.property.2.2 p).trans j.isLt.le

noncomputable def splitEquiv (a b : BTree) (m : ℕ) :
    Labeling (fork a b) m ≃ Σ j : Fin m, Labeling a j.val × Labeling b j.val where
  toFun f := ⟨labelingRoot f, labelingLeft f, labelingRight f⟩
  invFun f := combine f.1 f.2.1 f.2.2
  left_inv f := by
    apply Subtype.ext
    funext p
    cases p with
    | nil =>
      have hpos := (f.property.2.1 []).mpr (nil_mem_nodes a b)
      change f.val [] - 1 + 1 = f.val []
      omega
    | cons c p => cases c <;> rfl
  right_inv f := by
    obtain ⟨j, f, g⟩ := f
    rfl

theorem weight_combine {a b : BTree} {m : ℕ} (j : Fin m)
    (f : Labeling a j.val) (g : Labeling b j.val) :
    weight (fork a b) (combine j f g).val =
      MvPolynomial.X j.val * weight a f.val * weight b g.val := by
  classical
  have hd : Disjoint (a.nodes.image (false :: ·)) (b.nodes.image (true :: ·)) := by
    simp [Finset.disjoint_left]
  simp only [weight, nodes]
  rw [Finset.prod_insert (by simp), Finset.prod_union hd,
    Finset.prod_image (fun _ _ _ _ h => (List.cons.inj h).2),
    Finset.prod_image (fun _ _ _ _ h => (List.cons.inj h).2)]
  simp only [combine, combineFun, labelWeight_succ]
  ring

theorem K_fork (a b : BTree) (m : ℕ) :
    K (fork a b) m = ∑ j : Fin m, MvPolynomial.X j.val * K a j.val * K b j.val := by
  classical
  unfold K
  rw [Fintype.sum_equiv (splitEquiv a b m) _
    (fun f => weight (fork a b) (combine f.1 f.2.1 f.2.2).val)
    (by
      intro f
      change weight (fork a b) f.val =
        weight (fork a b) ((splitEquiv a b m).symm ((splitEquiv a b m) f)).val
      rw [Equiv.symm_apply_apply])]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  rw [Fintype.sum_prod_type]
  simp only [weight_combine, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem K_mirror (a : BTree) (m : ℕ) : K a.mirror m = K a m := by
  induction a generalizing m with
  | leaf => rfl
  | fork a b ha hb =>
    simp only [mirror, K_fork, ha, hb]
    apply Finset.sum_congr rfl
    intro j _
    ring

end BTree
end DickeyRosenberg

namespace DickeyRosenberg
namespace BTree

open DickeyRosenbergSwitching

noncomputable def switchLabels (a b : BTree) {m j : ℕ} (hjm : j ≤ m) :
    Labeling a m × Labeling b j ↪ Labeling (a.union b) m × Labeling (a.inter b) j where
  toFun fg := by
    let out := switched Path.Edge ((b.nodes : Set (List Bool)) \ (a.nodes : Set (List Bool)))
      (fg.1.val, fg.2.val)
    have h := switched_maps hjm fg.1.property fg.2.property
    exact (⟨out.1, by simpa only [nodes_union, Finset.coe_union] using h.1⟩,
      ⟨out.2, by simpa only [nodes_inter, Finset.coe_inter] using h.2⟩)
  inj' := by
    intro f g h
    have h' := congrArg (fun p => (p.1.val, p.2.val)) h
    have hf := switched_injective Path.Edge
      ((b.nodes : Set (List Bool)) \ (a.nodes : Set (List Bool))) h'
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst hf)
    · exact Subtype.ext (congrArg Prod.snd hf)

theorem switched_product (s : Finset (List Bool)) (Q : Set (List Bool))
    (fg : (List Bool → ℕ) × (List Bool → ℕ)) :
    (∏ p ∈ s, labelWeight ((switched Path.Edge Q fg).1 p)) *
      (∏ p ∈ s, labelWeight ((switched Path.Edge Q fg).2 p)) =
    (∏ p ∈ s, labelWeight (fg.1 p)) * (∏ p ∈ s, labelWeight (fg.2 p)) := by
  classical
  simp only [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _
  by_cases h : Marked Path.Edge fg.1 fg.2 Q p <;> simp [switched, h, mul_comm]

theorem switchLabels_weight (a b : BTree) {m j : ℕ} (hjm : j ≤ m)
    (fg : Labeling a m × Labeling b j) :
    weight (a.union b) (switchLabels a b hjm fg).1.val *
      weight (a.inter b) (switchLabels a b hjm fg).2.val =
    weight a fg.1.val * weight b fg.2.val := by
  let s := (a.union b).nodes
  have ha : a.nodes ⊆ s := by dsimp [s]; rw [nodes_union]; exact Finset.subset_union_left
  have hb : b.nodes ⊆ s := by dsimp [s]; rw [nodes_union]; exact Finset.subset_union_right
  have hi : (a.inter b).nodes ⊆ s := by
    rw [nodes_inter]
    exact Finset.inter_subset_left.trans ha
  rw [weight_extend (switchLabels a b hjm fg).1 s (by rfl),
    weight_extend (switchLabels a b hjm fg).2 s hi,
    weight_extend fg.1 s ha, weight_extend fg.2 s hb]
  exact switched_product s _ _

theorem K_union_inter (a b : BTree) {m j : ℕ} (hjm : j ≤ m) :
    K a m * K b j ≤ K (a.union b) m * K (a.inter b) j := by
  classical
  have h := poly_sum_injection (switchLabels a b hjm)
    (fun fg => weight a fg.1.val * weight b fg.2.val)
    (fun fg => weight (a.union b) fg.1.val * weight (a.inter b) fg.2.val)
    (fun fg => (switchLabels_weight a b hjm fg).symm)
  simpa only [K, Fintype.sum_prod_type, ← Finset.mul_sum, ← Finset.sum_mul] using h

noncomputable abbrev G (n m : ℕ) : Poly := K (complete n) m

theorem G_nested {a d j m : ℕ} (ha : 0 < a) (had : a ≤ d) (hjm : j ≤ m) :
    G a m * G d j ≤ G d m * G a j := by
  have hs := complete_nested ha had
  have hu : (complete a).union (complete d) = complete d := by
    apply nodes_injective
    rw [nodes_union, Finset.union_eq_right.mpr hs]
  have hi : (complete a).inter (complete d) = complete a := by
    apply nodes_injective
    rw [nodes_inter, Finset.inter_eq_left.mpr hs]
  simpa only [hu, hi] using K_union_inter (complete a) (complete d) hjm

/-- The strong induction hypothesis needed at leaf count `n`. -/
def Below (n : ℕ) : Prop :=
  ∀ t : BTree, t.leaves < n → ∀ m, K t m ≤ G t.leaves m

theorem dyadic_block {n k a d m j : ℕ} (ih : Below n)
    (ha : 2^k ≤ a) (ha' : a ≤ 2 * 2^k)
    (hd : 2^k ≤ d) (hd' : d ≤ 2 * 2^k)
    (had : a+d ≤ n) (hjm : j ≤ m) :
    G a m * G d j ≤ G (min (2 * 2^k) (a+d-2^k)) m *
      G (max (2^k) (a+d-2 * 2^k)) j := by
  have hq : 0 < 2^k := by positivity
  have hx : a - 2^k ≤ 2^k := by omega
  have hy : d - 2^k ≤ 2^k := by omega
  have hA : complete a = fill k (a-2^k) := by
    have h := complete_eq_fill k (a-2^k) hx
    simpa [Nat.add_sub_of_le ha] using h
  have hD : complete d = fill k (d-2^k) := by
    have h := complete_eq_fill k (d-2^k) hy
    simpa [Nat.add_sub_of_le hd] using h
  let P := complete a
  let Q := (complete d).mirror
  have hu : (P.union Q).leaves = min (2*2^k) (a+d-2^k) := by
    dsimp [P, Q]
    rw [hA, hD, union_fill_mirror_leaves k (a-2^k) (d-2^k) hx hy]
    omega
  have hi' : (P.inter Q).leaves = max (2^k) (a+d-2*2^k) := by
    dsimp [P, Q]
    rw [hA, hD, inter_fill_mirror_leaves k (a-2^k) (d-2^k) hx hy]
    omega
  have hsum : (P.union Q).leaves + (P.inter Q).leaves = a+d := by
    rw [leaves_union_add_inter]
    dsimp [P, Q]
    rw [leaves_mirror, leaves_complete (by omega), leaves_complete (by omega)]
  have hupos := leaves_pos (P.union Q)
  have hipos := leaves_pos (P.inter Q)
  calc
    G a m * G d j = K P m * K Q j := by simp only [P, Q, K_mirror]
    _ ≤ K (P.union Q) m * K (P.inter Q) j := K_union_inter P Q hjm
    _ ≤ G (P.union Q).leaves m * G (P.inter Q).leaves j :=
      poly_mul_mono (ih _ (by omega) m) (ih _ (by omega) j)
    _ = _ := by rw [hu, hi']

theorem rotation {n a b c d m : ℕ} (ih : Below n)
    (ha : 0 < a) (hc : 0 < c) (hd : 0 < d) (hb : b = c+d)
    (hs : G b m = K (fork (complete c) (complete d)) m)
    (had : a ≤ d) (hn : a+b ≤ n) :
    G a m * G b m ≤ G d m * G (a+c) m := by
  have hsmall : (fork (complete a) (complete c)).leaves < n := by
    simp only [leaves, leaves_complete ha, leaves_complete hc]
    omega
  calc
    G a m * G b m =
        ∑ j : Fin m, MvPolynomial.X j.val * G c j.val * (G a m * G d j.val) := by
      rw [hs, K_fork, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ ∑ j : Fin m, MvPolynomial.X j.val * G c j.val * (G d m * G a j.val) := by
      apply poly_sum_mono
      intro j _
      exact poly_mul_mono le_rfl (G_nested ha had j.isLt.le)
    _ = G d m * K (fork (complete a) (complete c)) m := by
      simp only [K_fork, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ G d m * G (a+c) m := by
      have h := ih _ hsmall m
      simp only [leaves, leaves_complete ha, leaves_complete hc] at h
      exact poly_mul_mono le_rfl h

end BTree
end DickeyRosenberg

namespace DickeyRosenberg
namespace BTree

theorem K_fork_comm (a b : BTree) (m : ℕ) : K (fork a b) m = K (fork b a) m := by
  rw [K_fork, K_fork]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem G_split_low (k n m : ℕ) (hl : 2 * 2^k ≤ n) (hh : n ≤ 3 * 2^k) :
    G n m = K (fork (complete (2^k)) (complete (n-2^k))) m := by
  change K (complete n) m = _
  rw [complete_dyadic_split_low k n hl hh, K_fork_comm]

theorem G_split_high (k n m : ℕ) (hl : 3 * 2^k ≤ n) (hh : n ≤ 4 * 2^k) :
    G n m = K (fork (complete (2*2^k)) (complete (n-2*2^k))) m := by
  change K (complete n) m = _
  rw [complete_dyadic_split_high k n hl hh]

noncomputable def splitTarget (k n m : ℕ) : Poly :=
  if n ≤ 3*2^k then G (2^k) m * G (n-2^k) m
  else G (2*2^k) m * G (n-2*2^k) m

theorem endpoints_eq_target {k a d m : ℕ} (ha : 2^k ≤ a) (hd : 2^k ≤ d) :
    G (min (2*2^k) (a+d-2^k)) m * G (max (2^k) (a+d-2*2^k)) m =
      splitTarget k (a+d) m := by
  unfold splitTarget
  split_ifs with h
  · have hl : min (2*2^k) (a+d-2^k) = a+d-2^k := by omega
    have hs : max (2^k) (a+d-2*2^k) = 2^k := by omega
    rw [hl, hs, mul_comm]
  · have hl : min (2*2^k) (a+d-2^k) = 2*2^k := by omega
    have hs : max (2^k) (a+d-2*2^k) = a+d-2*2^k := by omega
    rw [hl, hs]

theorem split_caseA {n k a b m : ℕ} (ih : Below n)
    (ha : 2^k ≤ a) (ha' : a ≤ 2*2^k) (hb : 2^k ≤ b) (hb' : b ≤ 2*2^k)
    (hn : a+b = n) : G a m * G b m ≤ splitTarget k n m := by
  have h := dyadic_block ih ha ha' hb hb' (by omega) (le_refl m)
  rw [endpoints_eq_target ha hb, hn] at h
  exact h

/-- The four dyadic cases of Lemma 5. -/
theorem split_bound_sorted {n k a b m : ℕ} (ih : Below n)
    (ha0 : 0 < a) (hab : a ≤ b) (hn : a+b = n)
    (hnlo : 2*2^k ≤ n) (hnhi : n < 4*2^k) :
    G a m * G b m ≤ splitTarget k n m := by
  have hp : 0 < 2^k := by positivity
  have hb0 : 0 < b := by omega
  by_cases ha : 2^k ≤ a
  · by_cases hb : b ≤ 2*2^k
    · exact split_caseA ih ha (by omega) (by omega) hb hn
    · -- Case D: one subtree is above the block, the other is inside it.
      have hbhi : b ≤ 3*2^k := by omega
      have hrec := G_split_low k b m (by omega) hbhi
      have hresult : G a m * G b m ≤ G (n-2*2^k) m * G (2*2^k) m := by
        calc
          G a m * G b m = ∑ j : Fin m,
              MvPolynomial.X j.val * G (2^k) j.val * (G a m * G (b-2^k) j.val) := by
            rw [hrec, K_fork, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
          _ ≤ ∑ j : Fin m,
              MvPolynomial.X j.val * G (2^k) j.val *
                (G (n-2*2^k) m * G (2^k) j.val) := by
            apply poly_sum_mono
            intro j _
            apply poly_mul_mono le_rfl
            have hd : 2^k ≤ b-2^k := by omega
            have hd' : b-2^k ≤ 2*2^k := by omega
            have h := dyadic_block ih ha (by omega) hd hd' (by omega) j.isLt.le
            have hl : min (2*2^k) (a+(b-2^k)-2^k) = n-2*2^k := by omega
            have hs : max (2^k) (a+(b-2^k)-2*2^k) = 2^k := by omega
            rwa [hl, hs] at h
          _ = G (n-2*2^k) m * K (fork (complete (2^k)) (complete (2^k))) m := by
            rw [K_fork, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
          _ = G (n-2*2^k) m * G (2*2^k) m := by
            have h := G_split_low k (2*2^k) m le_rfl (by omega)
            have he : 2*2^k - 2^k = 2^k := by omega
            rw [he] at h
            rw [h]
      unfold splitTarget
      rw [if_neg (by omega : ¬ n ≤ 3*2^k)]
      simpa only [mul_comm] using hresult
  · by_cases hb : 2*2^k < b
    · -- Case B: the two subtree sizes lie on opposite sides of the block.
      by_cases hbhi : b ≤ 3*2^k
      · have hrot := rotation ih ha0 hp (by omega : 0 < b-2^k)
          (by omega : b = 2^k + (b-2^k)) (G_split_low k b m (by omega) hbhi)
          (by omega : a ≤ b-2^k) (by omega : a+b ≤ n)
        exact hrot.trans (split_caseA ih (by omega) (by omega) (by omega) (by omega)
          (by omega : (b-2^k)+(a+2^k) = n))
      · have hrec : G b m = K (fork (complete (b-2*2^k)) (complete (2*2^k))) m := by
          rw [G_split_high k b m (by omega) (by omega), K_fork_comm]
        have hrot := rotation ih ha0 (by omega : 0 < b-2*2^k) (by omega : 0 < 2*2^k)
          (by omega : b = (b-2*2^k)+2*2^k) hrec (by omega : a ≤ 2*2^k)
          (by omega : a+b ≤ n)
        have he : a+(b-2*2^k) = n-2*2^k := by omega
        simpa only [he, splitTarget, if_neg (by omega : ¬ n ≤ 3*2^k)] using hrot
    · -- Case C: pass to the next smaller dyadic block.
      have hk : k ≠ 0 := by intro he; subst k; norm_num at ha; omega
      obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
      have hq : 0 < 2^l := by positivity
      simp only [pow_succ] at ha hnlo hnhi hb ⊢
      by_cases hbhi : 3*2^l ≤ b
      · have hrec : G b m = K (fork (complete (b-2*2^l)) (complete (2*2^l))) m := by
          rw [G_split_high l b m hbhi (by omega), K_fork_comm]
        have hrot := rotation ih ha0 (by omega : 0 < b-2*2^l) (by omega : 0 < 2*2^l)
          (by omega : b = (b-2*2^l)+2*2^l) hrec (by omega : a ≤ 2*2^l)
          (by omega : a+b ≤ n)
        have he : a+(b-2*2^l) = n-2*2^l := by omega
        unfold splitTarget
        rw [pow_succ, if_pos (by omega : n ≤ 3*(2^l*2))]
        simpa only [he, Nat.mul_comm] using hrot
      · have hrec := G_split_low l b m (by omega) (by omega)
        have hsmall : (fork (complete (2^l)) (complete (n-3*2^l))).leaves < n := by
          simp only [leaves, leaves_complete hq, leaves_complete (by omega : 0 < n-3*2^l)]
          omega
        have hresult : G a m * G b m ≤ G (2*2^l) m * G (n-2*2^l) m := by
          calc
            G a m * G b m = ∑ j : Fin m,
                MvPolynomial.X j.val * G (2^l) j.val * (G a m * G (b-2^l) j.val) := by
              rw [hrec, K_fork, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
            _ ≤ ∑ j : Fin m, MvPolynomial.X j.val * G (2^l) j.val *
                (G (2*2^l) m * G (n-3*2^l) j.val) := by
              apply poly_sum_mono
              intro j _
              apply poly_mul_mono le_rfl
              have h := dyadic_block ih (by omega : 2^l ≤ a) (by omega : a ≤ 2*2^l)
                (by omega : 2^l ≤ b-2^l) (by omega : b-2^l ≤ 2*2^l)
                (by omega : a+(b-2^l) ≤ n) j.isLt.le
              have hl : min (2*2^l) (a+(b-2^l)-2^l) = 2*2^l := by omega
              have hs : max (2^l) (a+(b-2^l)-2*2^l) = n-3*2^l := by omega
              rwa [hl, hs] at h
            _ = G (2*2^l) m * K (fork (complete (2^l)) (complete (n-3*2^l))) m := by
              rw [K_fork, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
            _ ≤ G (2*2^l) m * G (n-2*2^l) m := by
              have h := ih _ hsmall m
              have he : 2^l + (n-3*2^l) = n-2*2^l := by omega
              simp only [leaves, leaves_complete hq,
                leaves_complete (by omega : 0 < n-3*2^l), he] at h
              exact poly_mul_mono le_rfl h
        unfold splitTarget
        rw [pow_succ, if_pos (by omega : n ≤ 3*(2^l*2))]
        simpa only [Nat.mul_comm] using hresult

theorem split_bound {n k a b m : ℕ} (ih : Below n) (ha : 0 < a) (hb : 0 < b)
    (hn : a+b = n) (hnlo : 2*2^k ≤ n) (hnhi : n < 4*2^k) :
    G a m * G b m ≤ splitTarget k n m := by
  rcases le_total a b with hab | hba
  · exact split_bound_sorted ih ha hab hn hnlo hnhi
  · have h := split_bound_sorted ih hb hba (by omega : b+a = n) hnlo hnhi (m := m)
    simpa only [mul_comm] using h

theorem G_from_split {n k : ℕ} (hnlo : 2*2^k ≤ n) (hnhi : n < 4*2^k) (m : ℕ) :
    G n m = ∑ j : Fin m, MvPolynomial.X j.val * splitTarget k n j.val := by
  by_cases h : n ≤ 3*2^k
  · rw [G_split_low k n m hnlo h, K_fork]
    simp only [splitTarget, if_pos h, mul_assoc]
  · rw [G_split_high k n m (by omega) (by omega), K_fork]
    simp only [splitTarget, if_neg h, mul_assoc]

/-- The full coefficientwise dominance theorem, including every label bound. -/
theorem K_le_complete (t : BTree) (m : ℕ) : K t m ≤ G t.leaves m := by
  induction hn : t.leaves using Nat.strong_induction_on generalizing t m with
  | h n ih =>
    cases t with
    | leaf => simpa only [← hn, leaves, G, complete_one] using (le_refl (K leaf m))
    | fork a b =>
      have ha := leaves_pos a
      have hb := leaves_pos b
      have hab : a.leaves + b.leaves = n := hn
      have hn2 : 2 ≤ n := by omega
      have hind : Below n := by
        intro s hs k
        exact ih s.leaves hs s k rfl
      let k := Nat.log 2 (n/2)
      have hlo : 2*2^k ≤ n := by
        have h := Nat.pow_log_le_self 2 (by omega : n/2 ≠ 0)
        change 2^k ≤ n/2 at h
        omega
      have hhi : n < 4*2^k := by
        have h := Nat.lt_pow_succ_log_self (by omega : 1 < 2) (n/2)
        change n/2 < 2^(k+1) at h
        rw [pow_succ] at h
        omega
      rw [G_from_split hlo hhi m, K_fork]
      apply poly_sum_mono
      intro j _
      calc
        MvPolynomial.X j.val * K a j.val * K b j.val ≤
            MvPolynomial.X j.val * G a.leaves j.val * G b.leaves j.val :=
          poly_mul_mono (poly_mul_mono le_rfl (hind a (by omega) j.val))
            (hind b (by omega) j.val)
        _ ≤ MvPolynomial.X j.val * splitTarget k n j.val := by
          rw [mul_assoc]
          exact poly_mul_mono le_rfl (split_bound hind ha hb hab hlo hhi)

end BTree
end DickeyRosenberg

namespace DickeyRosenberg

/-- Sum the coefficients whose exponent satisfies `C`. -/
noncomputable def selectCoeffs (C : (ℕ →₀ ℕ) → Prop) : Poly →+ ℕ := by
  classical
  exact
    { toFun := fun p => (AddMonoidAlgebra.coeff p).sum (fun c n => if C c then n else 0)
      map_zero' := by simp
      map_add' := by
        intro p q
        rw [AddMonoidAlgebra.coeff_add]
        apply Finsupp.sum_add_index'
        · intro c; split_ifs <;> simp
        · intro c n k; split_ifs <;> simp }

theorem selectCoeffs_mono (C : (ℕ →₀ ℕ) → Prop) {p q : Poly} (h : p ≤ q) :
    selectCoeffs C p ≤ selectCoeffs C q := by
  classical
  change (AddMonoidAlgebra.coeff p).sum (fun c n => if C c then n else 0) ≤
    (AddMonoidAlgebra.coeff q).sum (fun c n => if C c then n else 0)
  apply Finsupp.sum_le_sum_index h
  · intro c _ a b hab
    split_ifs
    · exact hab
    · exact le_rfl
  · intro c _
    split_ifs <;> rfl

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem selectCoeffs_monomial (C : (ℕ →₀ ℕ) → Prop) [DecidablePred C]
    (c : ℕ →₀ ℕ) (n : ℕ) :
    selectCoeffs C (MvPolynomial.monomial c n) = if C c then n else 0 := by
  classical
  change (AddMonoidAlgebra.coeff (MvPolynomial.monomial c n)).sum
    (fun c n => @ite ℕ (C c) (Classical.propDecidable _) n 0) = _
  rw [MvPolynomial.sum_monomial_eq (by split_ifs <;> rfl)]
  split_ifs <;> rfl

abbrev Histories (V : Type*) (r : V → V → Prop) (z : ℕ) :=
  {f : V → Fin z // Function.Surjective f ∧ ∀ u v, r u v → f u < f v}

noncomputable def transportHistories {V W : Type*} {r : V → V → Prop} {s : W → W → Prop}
    (e : V ≃ W) (he : ∀ u v, r u v ↔ s (e u) (e v)) (z : ℕ) :
    Histories V r z ≃ Histories W s z where
  toFun f := ⟨f.val ∘ e.symm,
    f.property.1.comp e.symm.surjective, by
      intro u v h
      apply f.property.2
      exact (he (e.symm u) (e.symm v)).mpr (by simpa using h)⟩
  invFun f := ⟨f.val ∘ e, f.property.1.comp e.surjective, by
    intro u v h
    exact f.property.2 _ _ ((he u v).mp h)⟩
  left_inv f := by apply Subtype.ext; funext v; simp
  right_inv f := by apply Subtype.ext; funext v; simp

theorem E_isomorphic {T S : Shape} (h : Isomorphic T S) (z : ℕ) : E T z = E S z := by
  obtain ⟨e, he⟩ := h
  exact Nat.card_congr (transportHistories e he z)

namespace BTree

open DickeyRosenbergSwitching

noncomputable def profile (t : BTree) (f : List Bool → ℕ) : ℕ →₀ ℕ :=
  ∑ p ∈ t.nodes, Finsupp.single (f p - 1) 1

theorem weight_monomial {t : BTree} {m : ℕ} (f : Labeling t m) :
    weight t f.val = MvPolynomial.monomial (profile t f.val) 1 := by
  classical
  rw [profile, MvPolynomial.monomial_sum_one]
  apply Finset.prod_congr rfl
  intro p hp
  have hpos := (f.property.2.1 p).mpr hp
  simp only [labelWeight, if_neg (by omega : f.val p ≠ 0), MvPolynomial.X]

theorem profile_support (t : BTree) (f : List Bool → ℕ) :
    (profile t f).support = t.nodes.image (fun p => f p - 1) := by
  classical
  unfold profile
  induction t.nodes using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp [Finset.sum_insert ha, Finsupp.support_add_eq_union, ih]

def SurjLabeling {t : BTree} {m : ℕ} (f : Labeling t m) : Prop :=
  ∀ k : Fin m, ∃ p, f.val p = k.val+1

theorem profile_support_eq_range {t : BTree} {m : ℕ} (f : Labeling t m) :
    (profile t f.val).support = Finset.range m ↔ SurjLabeling f := by
  rw [profile_support]
  constructor
  · intro h k
    have hk : k.val ∈ t.nodes.image (fun p => f.val p - 1) := by
      rw [h]; exact Finset.mem_range.mpr k.isLt
    obtain ⟨p, hp, hpk⟩ := Finset.mem_image.mp hk
    have hpos := (f.property.2.1 p).mpr hp
    exact ⟨p, by omega⟩
  · intro h
    ext k
    constructor
    · rintro hk
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
      have hpos := (f.property.2.1 p).mpr hp
      have hle := f.property.2.2 p
      exact Finset.mem_range.mpr (by omega)
    · intro hk
      obtain ⟨p, hp⟩ := h ⟨k, Finset.mem_range.mp hk⟩
      change f.val p = k+1 at hp
      have hmem := (f.property.2.1 p).mp (by omega : 0 < f.val p)
      exact Finset.mem_image.mpr ⟨p, hmem, by omega⟩

abbrev PathHistories (t : BTree) (z : ℕ) :=
  Histories {p // p ∈ t.nodes} (fun u v => Path.Edge u.val v.val) z

noncomputable def extendHistory {t : BTree} {z : ℕ} (f : PathHistories t z) : Labeling t z := by
  classical
  let g := fun p => if hp : p ∈ t.nodes then (f.val ⟨p, hp⟩).val+1 else 0
  refine ⟨g, ?_, ?_, ?_⟩
  · intro u v huv
    by_cases hu : u ∈ t.nodes
    · have hv : v ∈ t.nodes := by
        obtain ⟨b, rfl⟩ := huv
        exact nodes_closed t hu
      have hlt := f.property.2 ⟨u, hu⟩ ⟨v, hv⟩ huv
      right
      simp only [g, dif_pos hu, dif_pos hv]
      exact Nat.add_lt_add_right hlt 1
    · left
      simp [g, hu]
  · intro p
    by_cases hp : p ∈ t.nodes <;> simp [g, hp]
  · intro p
    by_cases hp : p ∈ t.nodes
    · simp only [g, dif_pos hp]
      exact Nat.succ_le_of_lt (f.val ⟨p, hp⟩).isLt
    · simp [g, hp]

theorem extendHistory_surj {t : BTree} {z : ℕ} (f : PathHistories t z) :
    SurjLabeling (extendHistory f) := by
  classical
  intro k
  obtain ⟨p, hp⟩ := f.property.1 k
  refine ⟨p.val, ?_⟩
  simp only [extendHistory, dif_pos p.property]
  rw [hp]

noncomputable def restrictHistory {t : BTree} {z : ℕ}
    (f : {f : Labeling t z // SurjLabeling f}) : PathHistories t z := by
  let g : {p // p ∈ t.nodes} → Fin z := fun p =>
    ⟨f.val.val p.val - 1, by
      have hp := (f.val.property.2.1 p.val).mpr p.property
      have hb := f.val.property.2.2 p.val
      omega⟩
  refine ⟨g, ?_, ?_⟩
  · intro k
    obtain ⟨p, hp⟩ := f.property k
    have hm := (f.val.property.2.1 p).mp (by omega : 0 < f.val.val p)
    refine ⟨⟨p, hm⟩, Fin.ext ?_⟩
    simp only [g]
    omega
  · intro u v huv
    have hu := (f.val.property.2.1 u.val).mpr u.property
    have hv := (f.val.property.2.1 v.val).mpr v.property
    have h := f.val.property.1 u.val v.val huv
    change f.val.val u.val - 1 < f.val.val v.val - 1
    omega

noncomputable def historyLabelingEquiv (t : BTree) (z : ℕ) :
    PathHistories t z ≃ {f : Labeling t z // SurjLabeling f} where
  toFun f := ⟨extendHistory f, extendHistory_surj f⟩
  invFun := restrictHistory
  left_inv f := by
    classical
    apply Subtype.ext
    funext p
    apply Fin.ext
    simp [restrictHistory, extendHistory]
  right_inv f := by
    classical
    apply Subtype.ext
    apply Subtype.ext
    funext p
    by_cases hp : p ∈ t.nodes
    · have hpos := (f.val.property.2.1 p).mpr hp
      simp only [extendHistory, restrictHistory, dif_pos hp]
      omega
    · simp only [extendHistory, dif_neg hp]
      exact (labeling_zero_off f.val hp).symm

noncomputable def heapNodeEquiv (t : BTree) :
    {p // p ∈ t.nodes} ≃ {v // v ∈ t.toShape.nodes} :=
  Equiv.ofBijective (fun p => ⟨Path.heap p.val, Finset.mem_image.mpr ⟨p.val, p.property, rfl⟩⟩)
    ⟨by
      intro p q h
      exact Subtype.ext (Path.heap_injective (congrArg Subtype.val h)), by
      intro v
      obtain ⟨p, hp, he⟩ := Finset.mem_image.mp v.property
      exact ⟨⟨p, hp⟩, Subtype.ext he⟩⟩

noncomputable def heapHistoryEquiv (t : BTree) (z : ℕ) :
    PathHistories t z ≃ {f // IsHistory t.toShape z f} :=
  transportHistories (heapNodeEquiv t) (fun u v => Path.edge_heap_iff u.val v.val) z

theorem E_eq_select (t : BTree) (z : ℕ) :
    E t.toShape z = selectCoeffs (fun c => c.support = Finset.range z) (K t z) := by
  classical
  have he := (historyLabelingEquiv t z).symm.trans (heapHistoryEquiv t z)
  change Nat.card {f // IsHistory t.toShape z f} = _
  rw [← Nat.card_congr he, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  simp only [K, map_sum, weight_monomial, selectCoeffs_monomial]
  apply Finset.sum_congr rfl
  intro f _
  simp only [profile_support_eq_range]

end BTree

theorem allEventCounts : AllEventCounts := by
  intro T z
  obtain ⟨t, rfl⟩ := BTree.toShape_surjective T
  rw [← BTree.toShape_complete (leaves_positive t.toShape), BTree.E_eq_select,
    BTree.E_eq_select, BTree.toShape_leaves]
  exact selectCoeffs_mono _ (BTree.K_le_complete t z)

theorem conjecture14ii : Conjecture14ii := allEventCounts_implies_part_ii allEventCounts

theorem total_count_le (T : Shape) : N T ≤ N (canonical T.leaves) := by
  unfold N
  rw [canonical_nodes_card]
  exact Finset.sum_le_sum (fun z _ => allEventCounts T z)


end DickeyRosenberg

namespace DickeyRosenberg

noncomputable def mass : Poly →+* ℕ := MvPolynomial.eval₂Hom (RingHom.id ℕ) (fun _ => 1)

theorem mass_eq_select (p : Poly) : mass p = selectCoeffs (fun _ => True) p := by
  classical
  change MvPolynomial.eval₂ (RingHom.id ℕ) (fun _ => 1) p = _
  rw [MvPolynomial.eval₂_eq]
  simp [selectCoeffs, MvPolynomial.sum_def]

theorem mass_mono {p q : Poly} (h : p ≤ q) : mass p ≤ mass q := by
  rw [mass_eq_select, mass_eq_select]
  exact selectCoeffs_mono _ h

theorem E_zero_of_gt (T : Shape) {z : ℕ} (hz : T.nodes.card < z) : E T z = 0 := by
  have : IsEmpty {f // IsHistory T z f} := ⟨by
    intro f
    have h := Fintype.card_le_of_surjective f.val f.property.1
    simp only [Fintype.card_fin, Fintype.card_coe] at h
    omega⟩
  exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

theorem E_eq_of_N_eq (T : Shape) (hN : N T = N (canonical T.leaves)) (z : ℕ) :
    E T z = E (canonical T.leaves) z := by
  by_cases hz : z ≤ T.nodes.card
  · unfold N at hN
    rw [canonical_nodes_card] at hN
    exact (Finset.sum_eq_sum_iff_of_le (fun k _ => allEventCounts T k)).mp hN z
      (Finset.mem_range.mpr (by omega))
  · rw [E_zero_of_gt T (by omega), E_zero_of_gt (canonical T.leaves) (by
      rw [canonical_nodes_card]; omega)]

abbrev StrictMaps (V : Type*) (r : V → V → Prop) (m : ℕ) :=
  {f : V → Fin m // ∀ u v, r u v → f u < f v}

noncomputable def strictRange {V : Type*} [Fintype V] {r : V → V → Prop} {m : ℕ}
    (f : StrictMaps V r m) : Finset (Fin m) := Finset.univ.image f.val

noncomputable def rangeFiberEquiv (V : Type*) [Fintype V] (r : V → V → Prop)
    (m : ℕ) (s : Finset (Fin m)) :
    {f : StrictMaps V r m // strictRange f = s} ≃ Histories V r s.card := by
  classical
  let e := s.orderIsoOfFin rfl
  let compress (f : {f : StrictMaps V r m // strictRange f = s}) : Histories V r s.card := by
    have hmem : ∀ v, f.val.val v ∈ s := by
      intro v
      exact Eq.mp (congrArg (fun a => f.val.val v ∈ a) f.property)
        (Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩)
    refine ⟨(fun v => e.symm ⟨f.val.val v, hmem v⟩), ?_, ?_⟩
    · intro k
      have hk := Eq.mpr (congrArg (fun a => (e k).val ∈ a) f.property) (e k).property
      obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hk
      refine ⟨v, ?_⟩
      have heq : (⟨f.val.val v, hmem v⟩ : s) = e k := Subtype.ext hv
      exact (congrArg e.symm heq).trans (e.symm_apply_apply k)
    · intro u v h
      exact e.symm.strictMono (f.val.property u v h)
  let expand (f : Histories V r s.card) : {f : StrictMaps V r m // strictRange f = s} := by
    let g : StrictMaps V r m := ⟨(fun v => (e (f.val v)).val), by
      intro u v h
      exact e.strictMono (f.property.2 u v h)⟩
    refine ⟨g, ?_⟩
    ext k
    constructor
    · intro hk
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hk
      exact (e (f.val v)).property
    · intro hk
      obtain ⟨v, hv⟩ := f.property.1 (e.symm ⟨k, hk⟩)
      refine Finset.mem_image.mpr ⟨v, Finset.mem_univ _, ?_⟩
      change (e (f.val v)).val = k
      rw [hv, e.apply_symm_apply]
  exact
    { toFun := compress
      invFun := expand
      left_inv := by
        intro f
        apply Subtype.ext
        apply Subtype.ext
        funext v
        exact congrArg Subtype.val (e.apply_symm_apply _)
      right_inv := by
        intro f
        apply Subtype.ext
        funext v
        exact e.symm_apply_apply _ }

namespace BTree

open DickeyRosenbergSwitching

noncomputable def Count (t : BTree) (m : ℕ) : ℕ := Nat.card (Labeling t m)

theorem Count_eq_mass (t : BTree) (m : ℕ) : Count t m = mass (K t m) := by
  classical
  rw [mass_eq_select]
  simp [K, map_sum, weight_monomial, selectCoeffs_monomial, Count, Nat.card_eq_fintype_card]

theorem Count_le_complete (t : BTree) (m : ℕ) : Count t m ≤ Count (complete t.leaves) m := by
  rw [Count_eq_mass, Count_eq_mass]
  exact mass_mono (K_le_complete t m)

theorem Count_fork (a b : BTree) (m : ℕ) :
    Count (fork a b) m = ∑ j : Fin m, Count a j.val * Count b j.val := by
  rw [Count, Nat.card_congr (splitEquiv a b m), Nat.card_sigma]
  simp only [Nat.card_prod, Count]

noncomputable def extendStrict {t : BTree} {z : ℕ}
    (f : StrictMaps {p // p ∈ t.nodes} (fun u v => Path.Edge u.val v.val) z) : Labeling t z := by
  classical
  let g := fun p => if hp : p ∈ t.nodes then (f.val ⟨p, hp⟩).val+1 else 0
  refine ⟨g, ?_, ?_, ?_⟩
  · intro u v huv
    by_cases hu : u ∈ t.nodes
    · have hv : v ∈ t.nodes := by
        obtain ⟨b, rfl⟩ := huv
        exact nodes_closed t hu
      right
      simp only [g, dif_pos hu, dif_pos hv]
      exact Nat.add_lt_add_right (f.property ⟨u, hu⟩ ⟨v, hv⟩ huv) 1
    · left; simp [g, hu]
  · intro p
    by_cases hp : p ∈ t.nodes <;> simp [g, hp]
  · intro p
    by_cases hp : p ∈ t.nodes
    · simp only [g, dif_pos hp]
      exact Nat.succ_le_of_lt (f.val ⟨p, hp⟩).isLt
    · simp [g, hp]

noncomputable def restrictStrict {t : BTree} {z : ℕ} (f : Labeling t z) :
    StrictMaps {p // p ∈ t.nodes} (fun u v => Path.Edge u.val v.val) z := by
  let g : {p // p ∈ t.nodes} → Fin z := fun p =>
    ⟨f.val p.val - 1, by
      have hp := (f.property.2.1 p.val).mpr p.property
      have hb := f.property.2.2 p.val
      omega⟩
  refine ⟨g, ?_⟩
  intro u v huv
  have hu := (f.property.2.1 u.val).mpr u.property
  have hv := (f.property.2.1 v.val).mpr v.property
  have h := f.property.1 u.val v.val huv
  change f.val u.val - 1 < f.val v.val - 1
  omega

noncomputable def labelingStrictEquiv (t : BTree) (z : ℕ) :
    Labeling t z ≃ StrictMaps {p // p ∈ t.nodes} (fun u v => Path.Edge u.val v.val) z where
  toFun := restrictStrict
  invFun := extendStrict
  left_inv f := by
    classical
    apply Subtype.ext
    funext p
    by_cases hp : p ∈ t.nodes
    · have hpos := (f.property.2.1 p).mpr hp
      simp only [extendStrict, restrictStrict, dif_pos hp]
      omega
    · simp only [extendStrict, dif_neg hp]
      exact (labeling_zero_off f hp).symm
  right_inv f := by
    classical
    apply Subtype.ext
    funext p
    apply Fin.ext
    simp [restrictStrict, extendStrict]

theorem Count_eq_sum_E (t : BTree) (m : ℕ) :
    Count t m = ∑ s : Finset (Fin m), E t.toShape s.card := by
  classical
  rw [Count, Nat.card_congr (labelingStrictEquiv t m)]
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv
    (strictRange (V := {p // p ∈ t.nodes}) (r := fun u v => Path.Edge u.val v.val) (m := m))),
    Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro s _
  exact Nat.card_congr ((rangeFiberEquiv _ _ m s).trans (heapHistoryEquiv t s.card))

theorem Count_eq_of_N_eq (t : BTree) (hN : N t.toShape = N (canonical t.toShape.leaves))
    (m : ℕ) : Count t m = Count (complete t.leaves) m := by
  rw [Count_eq_sum_E, Count_eq_sum_E, toShape_complete (leaves_pos t)]
  apply Finset.sum_congr rfl
  intro s _
  simpa only [toShape_leaves] using E_eq_of_N_eq t.toShape hN s.card

end BTree
end DickeyRosenberg

namespace DickeyRosenberg
namespace BTree

open DickeyRosenbergSwitching

theorem node_length_lt (t : BTree) {p : List Bool} (hp : p ∈ t.nodes) : p.length < t.leaves := by
  induction t generalizing p with
  | leaf => simp at hp
  | fork a b ha hb =>
    have hapos := leaves_pos a
    have hbpos := leaves_pos b
    cases p with
    | nil => simp only [List.length_nil, leaves]; omega
    | cons c p =>
      cases c
      · have h := ha ((false_mem_nodes a b p).mp hp)
        simp only [List.length_cons, leaves]; omega
      · have h := hb ((true_mem_nodes a b p).mp hp)
        simp only [List.length_cons, leaves]; omega

noncomputable def baseLabeling (t : BTree) : Labeling t t.leaves := by
  classical
  let f := fun p => if p ∈ t.nodes then t.leaves - p.length else 0
  refine ⟨f, ?_, ?_, ?_⟩
  · rintro u v ⟨b, rfl⟩
    by_cases hu : v ++ [b] ∈ t.nodes
    · have hv := nodes_closed t hu
      have hlen := node_length_lt t hu
      simp only [List.length_append, List.length_singleton] at hlen
      right
      simp only [f, if_pos hu, if_pos hv, List.length_append, List.length_singleton]
      omega
    · left; simp [f, hu]
  · intro p
    change (0 < f p ↔ p ∈ t.nodes)
    by_cases hp : p ∈ t.nodes
    · have hlen := node_length_lt t hp
      simp only [f, if_pos hp, hp, iff_true]; omega
    · simp [f, hp]
  · intro p
    simp only [f]
    split_ifs <;> omega

noncomputable def relabelBound {t : BTree} {m k : ℕ} (f : Labeling t m) (h : m ≤ k) :
    Labeling t k := ⟨f.val, f.property.1, f.property.2.1, fun p => (f.property.2.2 p).trans h⟩

noncomputable def shiftLabeling {t : BTree} {m : ℕ} (f : Labeling t m) (k : ℕ) :
    Labeling t (m+k) := by
  classical
  let g := fun p => if p ∈ t.nodes then f.val p + k else 0
  refine ⟨g, ?_, ?_, ?_⟩
  · intro u v huv
    by_cases hu : u ∈ t.nodes
    · have hv : v ∈ t.nodes := by obtain ⟨b, rfl⟩ := huv; exact nodes_closed t hu
      have hpos := (f.property.2.1 u).mpr hu
      have hlt := f.property.1 u v huv
      right
      simp only [g, if_pos hu, if_pos hv]
      omega
    · left; simp [g, hu]
  · intro p
    change (0 < g p ↔ p ∈ t.nodes)
    by_cases hp : p ∈ t.nodes
    · have hpos := (f.property.2.1 p).mpr hp
      simp only [g, if_pos hp, hp, iff_true]; omega
    · simp [g, hp]
  · intro p
    have hb := f.property.2.2 p
    simp only [g]
    split_ifs <;> omega

theorem shiftLabeling_high {t : BTree} {m : ℕ} (f : Labeling t m) (k : ℕ)
    {p : List Bool} (hp : p ∈ t.nodes) : k < (shiftLabeling f k).val p := by
  have hpos := (f.property.2.1 p).mpr hp
  simp only [shiftLabeling, if_pos hp]
  omega

theorem Count_pos (t : BTree) {m : ℕ} (hm : t.leaves ≤ m) : 0 < Count t m := by
  rw [Count, Nat.card_eq_fintype_card]
  exact Fintype.card_pos_iff.mpr ⟨relabelBound (baseLabeling t) hm⟩

theorem component_root {t : BTree} {f g : List Bool → ℕ} {k : ℕ}
    (hf : ∀ p ∈ t.nodes, k < f p) (hg : ∀ p, g p ≤ k)
    {p : List Bool} (hp : p ∈ t.nodes) :
    Relation.EqvGen (Conflict Path.Edge f g) p [] := by
  induction p using List.reverseRecOn with
  | nil => exact Relation.EqvGen.refl _
  | append_singleton p b ih =>
    have hc : Conflict Path.Edge f g (p ++ [b]) p := by
      have h := hf _ hp
      have h' := hg p
      exact ⟨⟨b, rfl⟩, by omega, by omega⟩
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ hc) (ih (nodes_closed t hp))

/-- Labelings with all union labels above all intersection labels expose a missing image. -/
theorem switchLabels_not_surjective {a b : BTree} {m j k : ℕ} (hjm : j ≤ m)
    (F : Labeling (a.union b) m) (H : Labeling (a.inter b) j)
    (hF : ∀ p ∈ (a.union b).nodes, k < F.val p) (hH : ∀ p, H.val p ≤ k)
    (hq : ∃ q ∈ b.nodes, q ∉ a.nodes)
    (hbad : (∃ p ∈ a.nodes, p ∉ b.nodes) ∨ j ≤ k) :
    (F, H) ∉ Set.range (switchLabels a b hjm) := by
  classical
  obtain ⟨q, hqB, hqA⟩ := hq
  have hqU : q ∈ (a.union b).nodes := by rw [nodes_union]; exact Finset.mem_union_right _ hqB
  have hmark : ∀ p ∈ (a.union b).nodes,
      Marked Path.Edge F.val H.val ((b.nodes : Set (List Bool)) \ (a.nodes : Set (List Bool))) p := by
    intro p hp
    refine ⟨q, ⟨hqB, hqA⟩, ?_⟩
    exact Relation.EqvGen.trans _ _ _ (component_root hF hH hp)
      (Relation.EqvGen.symm _ _ (component_root hF hH hqU))
  rintro ⟨fg, hfg⟩
  have hraw := congrArg (fun p => (p.1.val, p.2.val)) hfg
  change switched Path.Edge ((b.nodes : Set (List Bool)) \ (a.nodes : Set (List Bool)))
    (fg.1.val, fg.2.val) = (F.val, H.val) at hraw
  have hback : (fg.1.val, fg.2.val) =
      switched Path.Edge ((b.nodes : Set (List Bool)) \ (a.nodes : Set (List Bool)))
        (F.val, H.val) := by
    rw [← hraw]
    exact (switched_involutive _ _ _).symm
  rcases hbad with ⟨p, hpA, hpB⟩ | hjk
  · have hpU : p ∈ (a.union b).nodes := by rw [nodes_union]; exact Finset.mem_union_left _ hpA
    have hv := congrArg (fun fg => fg.1 p) hback
    simp only [switched, hmark p hpU, if_true] at hv
    have hz : H.val p = 0 := labeling_zero_off H (by
      rw [nodes_inter]; simp only [Finset.mem_inter]; tauto)
    have hpos := (fg.1.property.2.1 p).mpr hpA
    omega
  · have hv := congrArg (fun fg => fg.2 q) hback
    simp only [switched, hmark q hqU, if_true] at hv
    have hbound := fg.2.property.2.2 q
    have hhigh := hF q hqU
    omega

theorem Count_union_strict_diff (a b : BTree) {m j : ℕ}
    (hq : ∃ q ∈ b.nodes, q ∉ a.nodes)
    (hj : (a.inter b).leaves ≤ j) (hm : (a.union b).leaves+j ≤ m) :
    Count a m * Count b j < Count (a.union b) m * Count (a.inter b) j := by
  have hjm : j ≤ m := by omega
  let F := relabelBound (shiftLabeling (baseLabeling (a.union b)) j) hm
  let H := relabelBound (baseLabeling (a.inter b)) hj
  have hnot := switchLabels_not_surjective hjm F H
    (fun p hp => shiftLabeling_high (baseLabeling (a.union b)) j hp)
    H.property.2.2 hq (Or.inr (le_refl j))
  have h := Fintype.card_lt_of_injective_of_notMem (switchLabels a b hjm)
    (switchLabels a b hjm).injective hnot
  simpa only [Fintype.card_prod, Count, Nat.card_eq_fintype_card] using h

theorem Count_union_strict_equal (a b : BTree)
    (hp : ∃ p ∈ a.nodes, p ∉ b.nodes) (hq : ∃ q ∈ b.nodes, q ∉ a.nodes) :
    ∃ m, Count a m * Count b m < Count (a.union b) m * Count (a.inter b) m := by
  let k := (a.inter b).leaves
  let m := (a.union b).leaves+k
  let F := shiftLabeling (baseLabeling (a.union b)) k
  let H : Labeling (a.inter b) m := relabelBound (baseLabeling (a.inter b)) (by dsimp [m,k]; omega)
  have hnot := switchLabels_not_surjective (le_refl m) F H
    (fun p hp => shiftLabeling_high (baseLabeling (a.union b)) k hp)
    (baseLabeling (a.inter b)).property.2.2 hq (Or.inl hp)
  refine ⟨m, ?_⟩
  have h := Fintype.card_lt_of_injective_of_notMem (switchLabels a b (le_refl m))
    (switchLabels a b (le_refl m)).injective hnot
  simpa only [Fintype.card_prod, Count, Nat.card_eq_fintype_card] using h

theorem right_only_of_inter_lt (a b : BTree) (h : (a.inter b).leaves < b.leaves) :
    ∃ q ∈ b.nodes, q ∉ a.nodes := by
  have hc : (a.inter b).nodes.card < b.nodes.card := by
    have hi := nodes_card (a.inter b)
    have hb := nodes_card b
    omega
  obtain ⟨q, hqB, hqI⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  refine ⟨q, hqB, ?_⟩
  intro hqA
  apply hqI
  rw [nodes_inter]
  exact Finset.mem_inter.mpr ⟨hqA, hqB⟩

theorem left_only_of_inter_lt (a b : BTree) (h : (a.inter b).leaves < a.leaves) :
    ∃ p ∈ a.nodes, p ∉ b.nodes := by
  have he : b.inter a = a.inter b := by apply nodes_injective; simp [nodes_inter, Finset.inter_comm]
  exact right_only_of_inter_lt b a (by rwa [he])

theorem Count_mirror (t : BTree) (m : ℕ) : Count t.mirror m = Count t m := by
  rw [Count_eq_mass, K_mirror, ← Count_eq_mass]

end BTree
end DickeyRosenberg

namespace DickeyRosenberg
namespace BTree

noncomputable abbrev C (n m : ℕ) : ℕ := Count (complete n) m

theorem below_all (n : ℕ) : Below n := fun t _ m => K_le_complete t m

theorem dyadic_union_leaves {k a d : ℕ}
    (ha : 2^k ≤ a) (ha' : a ≤ 2*2^k) (hd : 2^k ≤ d) (hd' : d ≤ 2*2^k) :
    ((complete a).union (complete d).mirror).leaves = min (2*2^k) (a+d-2^k) := by
  have hA : complete a = fill k (a-2^k) := by
    simpa [Nat.add_sub_of_le ha] using complete_eq_fill k (a-2^k) (by omega)
  have hD : complete d = fill k (d-2^k) := by
    simpa [Nat.add_sub_of_le hd] using complete_eq_fill k (d-2^k) (by omega)
  rw [hA, hD, union_fill_mirror_leaves k (a-2^k) (d-2^k) (by omega) (by omega)]
  omega

theorem dyadic_inter_leaves {k a d : ℕ}
    (ha : 2^k ≤ a) (ha' : a ≤ 2*2^k) (hd : 2^k ≤ d) (hd' : d ≤ 2*2^k) :
    ((complete a).inter (complete d).mirror).leaves = max (2^k) (a+d-2*2^k) := by
  have hp : 0 < 2^k := by positivity
  have h := leaves_union_add_inter (complete a) (complete d).mirror
  rw [dyadic_union_leaves ha ha' hd hd', leaves_mirror,
    leaves_complete (by omega), leaves_complete (by omega)] at h
  omega

theorem Count_dyadic_le {k a d m j : ℕ}
    (ha : 2^k ≤ a) (ha' : a ≤ 2*2^k) (hd : 2^k ≤ d) (hd' : d ≤ 2*2^k)
    (hjm : j ≤ m) :
    C a m * C d j ≤ C (min (2*2^k) (a+d-2^k)) m * C (max (2^k) (a+d-2*2^k)) j := by
  have h := mass_mono (dyadic_block (below_all (a+d)) ha ha' hd hd' le_rfl hjm)
  simpa only [map_mul, ← Count_eq_mass] using h

theorem Count_dyadic_strict_equal {k a d : ℕ}
    (ha : 2^k < a) (ha' : a < 2*2^k) (hd : 2^k < d) (hd' : d < 2*2^k) :
    ∃ m, C a m * C d m <
      C (min (2*2^k) (a+d-2^k)) m * C (max (2^k) (a+d-2*2^k)) m := by
  have hq : 0 < 2^k := by positivity
  let P := complete a
  let Q := (complete d).mirror
  have hu := dyadic_union_leaves ha.le ha'.le hd.le hd'.le
  have hi := dyadic_inter_leaves ha.le ha'.le hd.le hd'.le
  change (P.union Q).leaves = _ at hu
  change (P.inter Q).leaves = _ at hi
  have hP : P.leaves = a := leaves_complete (by omega)
  have hQ : Q.leaves = d := by dsimp [Q]; rw [leaves_mirror, leaves_complete (by omega)]
  have hleft := left_only_of_inter_lt P Q (by rw [hi, hP]; omega)
  have hright := right_only_of_inter_lt P Q (by rw [hi, hQ]; omega)
  obtain ⟨m, hm⟩ := Count_union_strict_equal P Q hleft hright
  refine ⟨m, ?_⟩
  have hdom := Nat.mul_le_mul (Count_le_complete (P.union Q) m) (Count_le_complete (P.inter Q) m)
  rw [hu, hi] at hdom
  have h := hm.trans_le hdom
  simpa only [P, Q, Count_mirror] using h

theorem Count_dyadic_strict_diff {k a d m j : ℕ}
    (ha : 2^k ≤ a) (ha' : a < 2*2^k) (hd : 2^k < d) (hd' : d ≤ 2*2^k)
    (hj : max (2^k) (a+d-2*2^k) ≤ j)
    (hm : min (2*2^k) (a+d-2^k)+j ≤ m) :
    C a m * C d j < C (min (2*2^k) (a+d-2^k)) m * C (max (2^k) (a+d-2*2^k)) j := by
  have hq : 0 < 2^k := by positivity
  let P := complete a
  let Q := (complete d).mirror
  have hu := dyadic_union_leaves ha ha'.le hd.le hd'
  have hi := dyadic_inter_leaves ha ha'.le hd.le hd'
  change (P.union Q).leaves = _ at hu
  change (P.inter Q).leaves = _ at hi
  have hQ : Q.leaves = d := by dsimp [Q]; rw [leaves_mirror, leaves_complete (by omega)]
  have hright := right_only_of_inter_lt P Q (by rw [hi, hQ]; omega)
  have hstrict := Count_union_strict_diff P Q (m := m) (j := j) hright
    (by rwa [hi]) (by rwa [hu])
  have hdom := Nat.mul_le_mul (Count_le_complete (P.union Q) m) (Count_le_complete (P.inter Q) j)
  rw [hu, hi] at hdom
  have h := hstrict.trans_le hdom
  simpa only [P, Q, Count_mirror] using h

theorem Count_nested_strict {a d j m : ℕ} (ha : 0 < a) (had : a < d)
    (hj : a ≤ j) (hm : d+j ≤ m) : C a m * C d j < C d m * C a j := by
  have hs := complete_nested ha had.le
  have hu : (complete a).union (complete d) = complete d := by
    apply nodes_injective
    rw [nodes_union, Finset.union_eq_right.mpr hs]
  have hi : (complete a).inter (complete d) = complete a := by
    apply nodes_injective
    rw [nodes_inter, Finset.inter_eq_left.mpr hs]
  have hright := right_only_of_inter_lt (complete a) (complete d) (by
    rw [hi, leaves_complete ha, leaves_complete (by omega)]; exact had)
  have h := Count_union_strict_diff (complete a) (complete d) (m := m) (j := j) hright
    (by simpa only [hi, leaves_complete ha] using hj)
    (by simpa only [hu, leaves_complete (by omega : 0 < d)] using hm)
  simpa only [hu, hi] using h

theorem Count_convolution_strict {A B C₀ D S : BTree} {m j₀ : ℕ}
    (hle : ∀ j : Fin m, Count A m * Count D j.val ≤ Count B m * Count S j.val)
    (hj : j₀ < m) (hc : 0 < Count C₀ j₀)
    (hlt : Count A m * Count D j₀ < Count B m * Count S j₀) :
    Count A m * Count (fork C₀ D) m < Count B m * Count (fork C₀ S) m := by
  calc
    Count A m * Count (fork C₀ D) m =
        ∑ j : Fin m, Count C₀ j.val * (Count A m * Count D j.val) := by
      rw [Count_fork, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ < ∑ j : Fin m, Count C₀ j.val * (Count B m * Count S j.val) := by
      apply Finset.sum_lt_sum
      · intro j _
        exact Nat.mul_le_mul_left _ (hle j)
      · exact ⟨⟨j₀, hj⟩, Finset.mem_univ _, Nat.mul_lt_mul_of_pos_left hlt hc⟩
    _ = Count B m * Count (fork C₀ S) m := by
      rw [Count_fork, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem canonical_transfer_strict {a b c d L S : ℕ} (hc : 0 < c) (hS : 0 < S)
    (hrec : ∀ m, G b m = K (fork (complete c) (complete d)) m)
    (hle : ∀ m j, j ≤ m → C a m * C d j ≤ C L m * C S j)
    (hw : ∃ m j, j < m ∧ c ≤ j ∧ C a m * C d j < C L m * C S j) :
    ∃ m, C a m * C b m < C L m * C (c+S) m := by
  obtain ⟨m, j, hj, hcj, hlt⟩ := hw
  have hpos : 0 < C c j := Count_pos (complete c) (by rwa [leaves_complete hc])
  have h := Count_convolution_strict (fun k => hle m k.val k.isLt.le) hj hpos hlt
  have hb : C b m = Count (fork (complete c) (complete d)) m := by
    simpa only [Count_eq_mass] using congrArg mass (hrec m)
  rw [← hb] at h
  refine ⟨m, h.trans_le ?_⟩
  have hdom := Count_le_complete (fork (complete c) (complete S)) m
  simp only [leaves, leaves_complete hc, leaves_complete hS] at hdom
  exact Nat.mul_le_mul_left _ hdom

theorem Count_rotation_strict {a b c d : ℕ}
    (ha : 0 < a) (hc : 0 < c) (had : a < d)
    (hrec : ∀ m, G b m = K (fork (complete c) (complete d)) m) :
    ∃ m, C a m * C b m < C d m * C (a+c) m := by
  have h := canonical_transfer_strict hc ha hrec
    (fun m j hj => by
      have h := mass_mono (G_nested ha had.le hj)
      simpa only [map_mul, ← Count_eq_mass] using h)
    (by
      let j := max a c
      refine ⟨d+j+1, j, by omega, by dsimp [j]; omega, ?_⟩
      exact Count_nested_strict ha had (by dsimp [j]; omega) (by omega))
  simpa only [Nat.add_comm] using h

theorem Count_block_transfer_strict {k a b c d : ℕ}
    (ha : 2^k ≤ a) (ha' : a < 2*2^k) (hd : 2^k < d) (hd' : d ≤ 2*2^k)
    (hc : 0 < c) (hrec : ∀ m, G b m = K (fork (complete c) (complete d)) m) :
    ∃ m, C a m * C b m <
      C (min (2*2^k) (a+d-2^k)) m * C (c + max (2^k) (a+d-2*2^k)) m := by
  have hq : 0 < 2^k := by positivity
  apply canonical_transfer_strict hc (by omega) hrec
  · intro m j hj
    exact Count_dyadic_le ha ha'.le hd.le hd' hj
  · let S := max (2^k) (a+d-2*2^k)
    let L := min (2*2^k) (a+d-2^k)
    let j := max c S
    have hL : 0 < L := by dsimp [L]; omega
    refine ⟨L+j+1, j, by omega, by dsimp [j]; omega, ?_⟩
    exact Count_dyadic_strict_diff ha ha' hd hd' (by dsimp [j,S]; omega) (by omega)

end BTree
end DickeyRosenberg

namespace DickeyRosenberg
namespace BTree

def GoodSplit (n a b : ℕ) : Prop :=
  complete n = fork (complete a) (complete b) ∨ complete n = fork (complete b) (complete a)

theorem strict_split_sorted {n k a b : ℕ}
    (ha0 : 0 < a) (hab : a ≤ b) (hn : a+b = n)
    (hnlo : 2*2^k ≤ n) (hnhi : n < 4*2^k) :
    GoodSplit n a b ∨ ∃ m, C a m * C b m < mass (splitTarget k n m) := by
  have hp : 0 < 2^k := by positivity
  by_cases ha : 2^k ≤ a
  · by_cases hb : b ≤ 2*2^k
    · by_cases hae : a = 2^k
      · left; right
        have hbe : b = n-2^k := by omega
        rw [hae, hbe]
        exact complete_dyadic_split_low k n hnlo (by omega)
      · by_cases hbe : b = 2*2^k
        · left; right
          have hae : a = n-2*2^k := by omega
          rw [hae, hbe]
          exact complete_dyadic_split_high k n (by omega) (by omega)
        · right
          obtain ⟨m, h⟩ := Count_dyadic_strict_equal
            (by omega : 2^k < a) (by omega : a < 2*2^k)
            (by omega : 2^k < b) (by omega : b < 2*2^k)
          have he := congrArg mass (endpoints_eq_target (m := m) ha (by omega : 2^k ≤ b))
          simp only [map_mul, ← Count_eq_mass, hn] at he
          rw [hn] at h
          exact ⟨m, h.trans_eq he⟩
    · right
      obtain ⟨m, h⟩ := Count_block_transfer_strict ha (by omega : a < 2*2^k)
        (by omega : 2^k < b-2^k) (by omega : b-2^k ≤ 2*2^k) hp
        (fun m => G_split_low k b m (by omega) (by omega))
      have hl : min (2*2^k) (a+(b-2^k)-2^k) = n-2*2^k := by omega
      have hs : 2^k + max (2^k) (a+(b-2^k)-2*2^k) = 2*2^k := by omega
      rw [hl, hs] at h
      refine ⟨m, ?_⟩
      unfold splitTarget
      rw [if_neg (by omega : ¬ n ≤ 3*2^k)]
      simpa only [map_mul, ← Count_eq_mass, Nat.mul_comm] using h
  · by_cases hb : 2*2^k < b
    · right
      by_cases hbhi : b ≤ 3*2^k
      · obtain ⟨m, h⟩ := Count_rotation_strict ha0 hp (by omega : a < b-2^k)
          (fun m => G_split_low k b m (by omega) hbhi)
        have hbound := mass_mono (split_caseA (m := m) (below_all n)
          (by omega : 2^k ≤ b-2^k) (by omega : b-2^k ≤ 2*2^k)
          (by omega : 2^k ≤ a+2^k) (by omega : a+2^k ≤ 2*2^k)
          (by omega : (b-2^k)+(a+2^k) = n))
        simp only [map_mul, ← Count_eq_mass] at hbound
        exact ⟨m, h.trans_le hbound⟩
      · have hrec : ∀ m, G b m = K (fork (complete (b-2*2^k)) (complete (2*2^k))) m := by
          intro m
          rw [G_split_high k b m (by omega) (by omega), K_fork_comm]
        obtain ⟨m, h⟩ := Count_rotation_strict ha0 (by omega : 0 < b-2*2^k)
          (by omega : a < 2*2^k) hrec
        have he : a+(b-2*2^k) = n-2*2^k := by omega
        refine ⟨m, ?_⟩
        unfold splitTarget
        rw [if_neg (by omega : ¬ n ≤ 3*2^k)]
        simpa only [he, map_mul, ← Count_eq_mass] using h
    · right
      have hk : k ≠ 0 := by intro he; subst k; norm_num at ha; omega
      obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
      have hq : 0 < 2^l := by positivity
      simp only [pow_succ] at ha hnlo hnhi hb
      by_cases hbhi : 3*2^l ≤ b
      · have hrec : ∀ m, G b m = K (fork (complete (b-2*2^l)) (complete (2*2^l))) m := by
          intro m
          rw [G_split_high l b m hbhi (by omega), K_fork_comm]
        obtain ⟨m, h⟩ := Count_rotation_strict ha0 (by omega : 0 < b-2*2^l)
          (by omega : a < 2*2^l) hrec
        have he : a+(b-2*2^l) = n-2*2^l := by omega
        refine ⟨m, ?_⟩
        unfold splitTarget
        rw [pow_succ, if_pos (by omega : n ≤ 3*(2^l*2))]
        simpa only [he, map_mul, ← Count_eq_mass, Nat.mul_comm] using h
      · obtain ⟨m, h⟩ := Count_block_transfer_strict (by omega : 2^l ≤ a)
          (by omega : a < 2*2^l) (by omega : 2^l < b-2^l)
          (by omega : b-2^l ≤ 2*2^l) hq (fun m => G_split_low l b m (by omega) (by omega))
        have hl : min (2*2^l) (a+(b-2^l)-2^l) = 2*2^l := by omega
        have hs : 2^l + max (2^l) (a+(b-2^l)-2*2^l) = n-2*2^l := by omega
        rw [hl, hs] at h
        refine ⟨m, ?_⟩
        unfold splitTarget
        rw [pow_succ, if_pos (by omega : n ≤ 3*(2^l*2))]
        simpa only [map_mul, ← Count_eq_mass, Nat.mul_comm] using h

theorem strict_split {n k a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hn : a+b = n)
    (hnlo : 2*2^k ≤ n) (hnhi : n < 4*2^k) :
    GoodSplit n a b ∨ ∃ m, C a m * C b m < mass (splitTarget k n m) := by
  rcases le_total a b with hab | hba
  · exact strict_split_sorted ha hab hn hnlo hnhi
  · rcases strict_split_sorted hb hba (by omega : b+a = n) hnlo hnhi with hg | ⟨m, hm⟩
    · exact Or.inl hg.symm
    · exact Or.inr ⟨m, by simpa only [Nat.mul_comm] using hm⟩

end BTree
end DickeyRosenberg

namespace DickeyRosenberg
namespace BTree

/-- A rooted automorphism of binary addresses carrying one tree onto another. -/
structure TreeIso (a b : BTree) where
  equiv : List Bool ≃ List Bool
  root : equiv [] = []
  edge : ∀ u v, Path.Edge u v ↔ Path.Edge (equiv u) (equiv v)
  mem : ∀ p, p ∈ a.nodes ↔ equiv p ∈ b.nodes

namespace TreeIso

def refl (a : BTree) : TreeIso a a := ⟨Equiv.refl _, rfl, fun _ _ => Iff.rfl, fun _ => Iff.rfl⟩

def symm {a b : BTree} (i : TreeIso a b) : TreeIso b a where
  equiv := i.equiv.symm
  root := i.equiv.symm_apply_eq.mpr i.root.symm
  edge u v := by simpa using (i.edge (i.equiv.symm u) (i.equiv.symm v)).symm
  mem p := by simpa using (i.mem (i.equiv.symm p)).symm

def trans {a b c : BTree} (i : TreeIso a b) (j : TreeIso b c) : TreeIso a c where
  equiv := i.equiv.trans j.equiv
  root := by simp [i.root, j.root]
  edge u v := (i.edge u v).trans (j.edge _ _)
  mem p := (i.mem p).trans (j.mem _)

def forkFun (f g : List Bool → List Bool) : List Bool → List Bool
  | [] => []
  | false :: p => false :: f p
  | true :: p => true :: g p

def forkEquiv (f g : List Bool ≃ List Bool) : List Bool ≃ List Bool where
  toFun := forkFun f g
  invFun := forkFun f.symm g.symm
  left_inv p := by cases p with
    | nil => rfl
    | cons b p => cases b <;> simp [forkFun]
  right_inv p := by cases p with
    | nil => rfl
    | cons b p => cases b <;> simp [forkFun]

theorem forkFun_edge {f g : List Bool → List Bool}
    (fr : f [] = []) (gr : g [] = [])
    (fe : ∀ u v, Path.Edge u v → Path.Edge (f u) (f v))
    (ge : ∀ u v, Path.Edge u v → Path.Edge (g u) (g v))
    {u v : List Bool} (h : Path.Edge u v) : Path.Edge (forkFun f g u) (forkFun f g v) := by
  obtain ⟨c, rfl⟩ := h
  cases v with
  | nil =>
    cases c
    · exact ⟨false, by simp [forkFun, fr]⟩
    · exact ⟨true, by simp [forkFun, gr]⟩
  | cons b p =>
    cases b
    · obtain ⟨d, hd⟩ := fe (p ++ [c]) p ⟨c, rfl⟩
      refine ⟨d, ?_⟩
      change false :: f (p ++ [c]) = (false :: f p) ++ [d]
      rw [hd]
      rfl
    · obtain ⟨d, hd⟩ := ge (p ++ [c]) p ⟨c, rfl⟩
      refine ⟨d, ?_⟩
      change true :: g (p ++ [c]) = (true :: g p) ++ [d]
      rw [hd]
      rfl

def fork {a b c d : BTree} (i : TreeIso a c) (j : TreeIso b d) :
    TreeIso (BTree.fork a b) (BTree.fork c d) where
  equiv := forkEquiv i.equiv j.equiv
  root := rfl
  edge u v := by
    constructor
    · exact forkFun_edge i.root j.root (fun u v => (i.edge u v).mp) (fun u v => (j.edge u v).mp)
    · intro h
      have he : Path.Edge
          ((forkEquiv i.equiv j.equiv).symm ((forkEquiv i.equiv j.equiv) u))
          ((forkEquiv i.equiv j.equiv).symm ((forkEquiv i.equiv j.equiv) v)) :=
        forkFun_edge i.symm.root j.symm.root
          (fun u v => (i.symm.edge u v).mp) (fun u v => (j.symm.edge u v).mp) h
      simpa using he
  mem p := by
    cases p with
    | nil => simp [forkEquiv, forkFun]
    | cons b p => cases b <;> simp [forkEquiv, forkFun, ← i.mem, ← j.mem]

def swapFun : List Bool → List Bool
  | [] => []
  | b :: p => (!b) :: p

theorem swapFun_involutive : Function.Involutive swapFun := by
  intro p
  cases p with
  | nil => rfl
  | cons b p => cases b <;> rfl

theorem swapFun_edge {u v : List Bool} (h : Path.Edge u v) :
    Path.Edge (swapFun u) (swapFun v) := by
  obtain ⟨c, rfl⟩ := h
  cases v with
  | nil => exact ⟨!c, rfl⟩
  | cons b p => exact ⟨c, rfl⟩

def swap (a b : BTree) : TreeIso (BTree.fork a b) (BTree.fork b a) where
  equiv := ⟨swapFun, swapFun, swapFun_involutive, swapFun_involutive⟩
  root := rfl
  edge u v := by
    constructor
    · exact swapFun_edge
    · intro h
      change Path.Edge (swapFun u) (swapFun v) at h
      have h' := swapFun_edge h
      simpa only [swapFun_involutive u, swapFun_involutive v] using h'
  mem p := by
    change (p ∈ (BTree.fork a b).nodes ↔ swapFun p ∈ (BTree.fork b a).nodes)
    cases p with
    | nil => simp [swapFun]
    | cons b p => cases b <;> simp [swapFun]

theorem toShape_isomorphic {a b : BTree} (i : TreeIso a b) : Isomorphic a.toShape b.toShape := by
  let en := i.equiv.subtypeEquiv i.mem
  let e := (heapNodeEquiv a).symm.trans (en.trans (heapNodeEquiv b))
  refine ⟨e, ?_⟩
  intro u v
  obtain ⟨p, rfl⟩ := (heapNodeEquiv a).surjective u
  obtain ⟨q, rfl⟩ := (heapNodeEquiv a).surjective v
  simp only [e, Equiv.trans_apply, Equiv.symm_apply_apply]
  change Parent (Path.heap p.val) (Path.heap q.val) ↔
    Parent (Path.heap (i.equiv p.val)) (Path.heap (i.equiv q.val))
  rw [← Path.edge_heap_iff, ← Path.edge_heap_iff]
  exact i.edge p.val q.val

end TreeIso
end BTree
end DickeyRosenberg

namespace DickeyRosenberg
namespace BTree

@[simp] theorem mass_X (n : ℕ) : mass (MvPolynomial.X n) = 1 := by simp [mass]

/-- Equality for all sufficiently large upper label bounds. -/
def EventuallyMax (t : BTree) : Prop :=
  ∃ M, ∀ m, M ≤ m → Count t m = C t.leaves m

theorem canonical_product_le_target {n k a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hn : a+b = n) (hnlo : 2*2^k ≤ n) (hnhi : n < 4*2^k) (j : ℕ) :
    C a j * C b j ≤ mass (splitTarget k n j) := by
  have h := mass_mono (split_bound (below_all n) ha hb hn hnlo hnhi (m := j))
  simpa only [map_mul, ← Count_eq_mass] using h

theorem eventual_root_tight {a b : BTree} {n k : ℕ} (hmax : EventuallyMax (fork a b))
    (hn : a.leaves+b.leaves = n) (hnlo : 2*2^k ≤ n) (hnhi : n < 4*2^k) (j : ℕ) :
    Count a j * Count b j = C a.leaves j * C b.leaves j ∧
      C a.leaves j * C b.leaves j = mass (splitTarget k n j) := by
  obtain ⟨M, hM⟩ := hmax
  let m := max M (j+1)
  have hjm : j < m := by dsimp [m]; omega
  have hsum := hM m (le_max_left _ _)
  simp only [leaves, hn] at hsum
  have hcanon := congrArg mass (G_from_split hnlo hnhi m)
  simp only [map_sum, map_mul, mass_X, one_mul, ← Count_eq_mass] at hcanon
  rw [Count_fork] at hsum
  have hsum' : (∑ i : Fin m, Count a i.val * Count b i.val) =
      ∑ i : Fin m, mass (splitTarget k n i.val) := hsum.trans hcanon
  have hprod (i : ℕ) : Count a i * Count b i ≤ C a.leaves i * C b.leaves i :=
    Nat.mul_le_mul (Count_le_complete a i) (Count_le_complete b i)
  have htarget (i : ℕ) : C a.leaves i * C b.leaves i ≤ mass (splitTarget k n i) :=
    canonical_product_le_target (leaves_pos a) (leaves_pos b) hn hnlo hnhi i
  have he := (Finset.sum_eq_sum_iff_of_le
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => (hprod i.val).trans (htarget i.val))).mp hsum'
    ⟨j, hjm⟩ (Finset.mem_univ _)
  change Count a j * Count b j = mass (splitTarget k n j) at he
  have hp := hprod j
  have ht := htarget j
  constructor <;> omega

theorem factors_eq_of_tight {x y X Y : ℕ} (hx : x ≤ X) (hy : y ≤ Y)
    (hX : 0 < X) (hY : 0 < Y) (h : x*y = X*Y) : x = X ∧ y = Y := by
  constructor
  · apply le_antisymm hx
    by_contra hnot
    have hlt : x < X := by omega
    have hstrict := (Nat.mul_le_mul_left x hy).trans_lt (Nat.mul_lt_mul_of_pos_right hlt hY)
    omega
  · apply le_antisymm hy
    by_contra hnot
    have hlt : y < Y := by omega
    have hstrict := (Nat.mul_le_mul_right y hx).trans_lt (Nat.mul_lt_mul_of_pos_left hlt hX)
    omega

theorem eventual_children {a b : BTree} {n k : ℕ} (hmax : EventuallyMax (fork a b))
    (hn : a.leaves+b.leaves = n) (hnlo : 2*2^k ≤ n) (hnhi : n < 4*2^k) :
    EventuallyMax a ∧ EventuallyMax b := by
  have hboth : ∀ j, max a.leaves b.leaves ≤ j →
      Count a j = C a.leaves j ∧ Count b j = C b.leaves j := by
    intro j hj
    apply factors_eq_of_tight (Count_le_complete a j) (Count_le_complete b j)
    · exact Count_pos (complete a.leaves) (by rw [leaves_complete (leaves_pos a)]; omega)
    · exact Count_pos (complete b.leaves) (by rw [leaves_complete (leaves_pos b)]; omega)
    · exact (eventual_root_tight hmax hn hnlo hnhi j).1
  exact ⟨⟨max a.leaves b.leaves, fun j hj => (hboth j hj).1⟩,
    ⟨max a.leaves b.leaves, fun j hj => (hboth j hj).2⟩⟩

theorem eventuallyMax_iso (t : BTree) (hmax : EventuallyMax t) :
    Nonempty (TreeIso t (complete t.leaves)) := by
  revert hmax
  induction hn : t.leaves using Nat.strong_induction_on generalizing t with
  | h n ih =>
    intro hmax
    cases t with
    | leaf =>
      have he : n = 1 := hn.symm
      subst n
      change Nonempty (TreeIso leaf (complete 1))
      rw [complete_one]
      exact ⟨TreeIso.refl leaf⟩
    | fork a b =>
      have ha := leaves_pos a
      have hb := leaves_pos b
      have hab : a.leaves+b.leaves = n := hn
      have hn2 : 2 ≤ n := by omega
      let k := Nat.log 2 (n/2)
      have hlo : 2*2^k ≤ n := by
        have h := Nat.pow_log_le_self 2 (by omega : n/2 ≠ 0)
        change 2^k ≤ n/2 at h
        omega
      have hhi : n < 4*2^k := by
        have h := Nat.lt_pow_succ_log_self (by omega : 1 < 2) (n/2)
        change n/2 < 2^(k+1) at h
        rw [pow_succ] at h
        omega
      have hg : GoodSplit n a.leaves b.leaves := by
        rcases strict_split ha hb hab hlo hhi with hg | ⟨m, hm⟩
        · exact hg
        · have he := (eventual_root_tight hmax hab hlo hhi m).2
          omega
      have hchildren := eventual_children hmax hab hlo hhi
      obtain ⟨ia⟩ := ih a.leaves (by omega) a rfl hchildren.1
      obtain ⟨ib⟩ := ih b.leaves (by omega) b rfl hchildren.2
      rcases hg with hg | hg
      · rw [hg]
        exact ⟨ia.fork ib⟩
      · rw [hg]
        exact ⟨(ia.fork ib).trans (TreeIso.swap _ _)⟩

end BTree

/-- Dickey--Rosenberg Conjecture 14(i), including uniqueness up to isomorphism. -/
theorem conjecture14i : Conjecture14i := by
  intro T
  refine ⟨total_count_le T, ?_⟩
  intro hN
  obtain ⟨t, rfl⟩ := BTree.toShape_surjective T
  have hmax : BTree.EventuallyMax t :=
    ⟨0, fun m _ => BTree.Count_eq_of_N_eq t hN m⟩
  obtain ⟨i⟩ := BTree.eventuallyMax_iso t hmax
  have hi := i.toShape_isomorphic
  rw [BTree.toShape_complete (BTree.leaves_pos t)] at hi
  simpa only [BTree.toShape_leaves] using hi

end DickeyRosenberg



/-!
Bridge to the recursive tree in Dickey--Rosenberg, Theorem 7.
Source: https://arxiv.org/html/2511.16799v1

The paper's split at n = 3 is (1,2): the real logarithm of 2/3 has
floor -1. Thus this case is handled explicitly before using the natural
logarithm. For n >= 4, flooring (n-1)/3 before taking its base-two
logarithm does not change the floor of the logarithm.
-/

namespace DickeyRosenberg

/-- Prefix a left (`false`) or right (`true`) edge to a heap address.
This inserts a bit after the leading binary 1, rather than appending a bit. -/
def heapEmbed (b : Bool) (v : ℕ) : ℕ :=
  v + (1 + b.toNat) * 2 ^ (Nat.log 2 v)

theorem heapEmbed_heap (b : Bool) (p : List Bool) :
    heapEmbed b (Path.heap p) = Path.heap (b :: p) := by
  have hl : Nat.log 2 (Path.heap p) = p.length :=
    Nat.log_eq_of_pow_le_of_lt_pow (Path.heap_bounds p).1 (Path.heap_bounds p).2
  simp only [heapEmbed, hl, Path.heap_cons]

theorem BTree.fork_heap_nodes (a b : BTree) :
    (BTree.fork a b).toShape.nodes =
      insert 1 ((a.toShape.nodes.image (heapEmbed false)) ∪
        (b.toShape.nodes.image (heapEmbed true))) := by
  simp only [BTree.toShape, BTree.nodes, Finset.image_insert, Finset.image_union,
    Finset.image_image, Path.heap_nil, Function.comp_def, heapEmbed_heap]

/-- Join two full binary shapes beneath a new root, by embedding their
internal vertices into the left and right subtrees in heap numbering. -/
def join (T S : Shape) : Shape where
  nodes := insert 1 ((T.nodes.image (heapEmbed false)) ∪
    (S.nodes.image (heapEmbed true)))
  positive := by
    obtain ⟨a, rfl⟩ := BTree.toShape_surjective T
    obtain ⟨b, rfl⟩ := BTree.toShape_surjective S
    rw [← BTree.fork_heap_nodes]
    exact (BTree.fork a b).toShape.positive
  closed := by
    obtain ⟨a, rfl⟩ := BTree.toShape_surjective T
    obtain ⟨b, rfl⟩ := BTree.toShape_surjective S
    rw [← BTree.fork_heap_nodes]
    exact (BTree.fork a b).toShape.closed

@[simp] theorem join_toShape (a b : BTree) :
    join a.toShape b.toShape = (BTree.fork a b).toShape :=
  Shape.ext (BTree.fork_heap_nodes a b).symm

@[simp] theorem join_leaves (T S : Shape) :
    (join T S).leaves = T.leaves + S.leaves := by
  obtain ⟨a, rfl⟩ := BTree.toShape_surjective T
  obtain ⟨b, rfl⟩ := BTree.toShape_surjective S
  simp

/-- The power-of-two part in Theorem 7, with the paper's small cases.
At n = 2 and n = 3 it equals 1; from n = 4 it is the displayed formula. -/
def paperSplit (n : ℕ) : ℕ :=
  if n ≤ 3 then 1 else 2 ^ (Nat.log 2 ((n - 1) / 3) + 1)

theorem paperSplit_bounds {n : ℕ} (hn : 2 ≤ n) :
    1 ≤ paperSplit n ∧ paperSplit n < n := by
  unfold paperSplit
  split_ifs with h
  · omega
  · have hlo := Nat.pow_log_le_self 2 (by omega : (n - 1) / 3 ≠ 0)
    have hp : 0 < 2 ^ Nat.log 2 ((n - 1) / 3) := by positivity
    rw [pow_succ]
    constructor <;> omega

/-- The paper's recursively specified maximizing tree. The otherwise unused
input 0 is assigned the single leaf, as is input 1. -/
def ustar (n : ℕ) : Shape :=
  if _h : n ≤ 1 then BTree.leaf.toShape
  else join (ustar (paperSplit n)) (ustar (n - paperSplit n))
termination_by n
decreasing_by
  all_goals have hs := paperSplit_bounds (by omega : 2 ≤ n)
  all_goals omega

@[simp] theorem ustar_one : ustar 1 = BTree.leaf.toShape := by
  rw [ustar, dif_pos (by omega)]

theorem ustar_step {n : ℕ} (hn : 2 ≤ n) :
    ustar n = join (ustar (paperSplit n)) (ustar (n - paperSplit n)) := by
  rw [ustar, dif_neg (by omega)]

@[simp] theorem ustar_two :
    ustar 2 = join BTree.leaf.toShape BTree.leaf.toShape := by
  rw [ustar_step (by omega)]
  norm_num [paperSplit]

theorem ustar_three : ustar 3 = join (ustar 1) (ustar 2) := by
  rw [ustar_step (by omega)]
  norm_num [paperSplit]

theorem ustar_recursion {n : ℕ} (hn : 4 ≤ n) :
    ustar n = join (ustar (2 ^ (Nat.log 2 ((n-1)/3) + 1)))
      (ustar (n - 2 ^ (Nat.log 2 ((n-1)/3) + 1))) := by
  rw [ustar_step (by omega), paperSplit, if_neg (by omega)]

theorem ustar_leaves (n : ℕ) (hn : 1 ≤ n) : (ustar n).leaves = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h : n = 1
    · subst n; simp
    · have hn2 : 2 ≤ n := by omega
      have hs := paperSplit_bounds hn2
      rw [ustar_step hn2, join_leaves, ih _ hs.2 hs.1,
        ih _ (by omega) (by omega)]
      omega

/-- The formula in Theorem 7 selects the canonical root split, up to order.
For n >= 4, put q = 2^(Nat.log 2 ((n-1)/3)); then 3q < n <= 6q and t = 2q.
The two halves of this interval use the existing two dyadic split lemmas. -/
theorem paperSplit_good {n : ℕ} (hn : 2 ≤ n) :
    BTree.GoodSplit n (paperSplit n) (n - paperSplit n) := by
  by_cases hsmall : n ≤ 3
  · right
    simpa [paperSplit, hsmall] using
      BTree.complete_dyadic_split_low 0 n (by omega) (by omega)
  · let k := Nat.log 2 ((n - 1) / 3)
    have hlo := Nat.pow_log_le_self 2 (by omega : (n - 1) / 3 ≠ 0)
    have hhi := Nat.lt_pow_succ_log_self (by omega : 1 < 2) ((n - 1) / 3)
    change 2 ^ k ≤ (n - 1) / 3 at hlo
    change (n - 1) / 3 < 2 ^ (k + 1) at hhi
    rw [pow_succ] at hhi
    have hsplit : paperSplit n = 2 * 2^k := by
      simp [paperSplit, hsmall, k, pow_succ, Nat.mul_comm]
    rw [hsplit]
    by_cases hmid : n ≤ 4 * 2^k
    · left
      exact BTree.complete_dyadic_split_high k n (by omega) hmid
    · right
      have h := BTree.complete_dyadic_split_low (k+1) n
        (by rw [pow_succ]; omega) (by rw [pow_succ]; omega)
      simpa only [pow_succ, Nat.mul_comm] using h

/-- A stronger witness: the paper's recursive shape is represented by a
binary tree with a rooted address isomorphism to the complete tree. -/
theorem ustar_tree_witness (n : ℕ) (hn : 1 ≤ n) :
    ∃ t : BTree, t.toShape = ustar n ∧
      Nonempty (BTree.TreeIso t (BTree.complete n)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h : n = 1
    · subst n
      exact ⟨BTree.leaf, ustar_one.symm, by
        rw [BTree.complete_one]
        exact ⟨BTree.TreeIso.refl _⟩⟩
    · have hn2 : 2 ≤ n := by omega
      have hs := paperSplit_bounds hn2
      obtain ⟨a, ha, ⟨ia⟩⟩ := ih _ hs.2 hs.1
      obtain ⟨b, hb, ⟨ib⟩⟩ := ih (n - paperSplit n) (by omega) (by omega)
      refine ⟨BTree.fork a b, ?_, ?_⟩
      · rw [ustar_step hn2, ← ha, ← hb, join_toShape]
      · rcases paperSplit_good hn2 with hg | hg
        · rw [hg]
          exact ⟨ia.fork ib⟩
        · rw [hg]
          exact ⟨(ia.fork ib).trans (BTree.TreeIso.swap _ _)⟩

theorem ustar_iso_canonical (n : ℕ) (hn : 1 ≤ n) :
    Isomorphic (ustar n) (canonical n) := by
  obtain ⟨t, ht, ⟨i⟩⟩ := ustar_tree_witness n hn
  have h := i.toShape_isomorphic
  rwa [ht, BTree.toShape_complete (by omega : 0 < n)] at h

namespace Isomorphic

@[refl] theorem refl (T : Shape) : Isomorphic T T :=
  ⟨Equiv.refl _, fun _ _ => Iff.rfl⟩

@[symm] theorem symm {T S : Shape} (h : Isomorphic T S) : Isomorphic S T := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, ?_⟩
  intro u v
  simpa using (he (e.symm u) (e.symm v)).symm

@[trans] theorem trans {T S R : Shape} (h : Isomorphic T S)
    (h' : Isomorphic S R) : Isomorphic T R := by
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  exact ⟨e.trans e', fun u v => (he u v).trans (he' (e u) (e v))⟩

theorem nodes_card {T S : Shape} (h : Isomorphic T S) :
    T.nodes.card = S.nodes.card := by
  obtain ⟨e, _⟩ := h
  simpa using Fintype.card_congr e

theorem leaves_eq {T S : Shape} (h : Isomorphic T S) : T.leaves = S.leaves := by
  simp only [Shape.leaves, h.nodes_card]

end Isomorphic

theorem N_isomorphic {T S : Shape} (h : Isomorphic T S) : N T = N S := by
  unfold N
  rw [h.nodes_card]
  exact Finset.sum_congr rfl (fun z _ => E_isomorphic h z)

/-- Conjecture 14(i), now with exactly the recursive tree of Theorem 7. -/
theorem conjecture14i_paper : ∀ T : Shape,
    N T ≤ N (ustar T.leaves) ∧
      (N T = N (ustar T.leaves) → Isomorphic T (ustar T.leaves)) := by
  intro T
  have hi := ustar_iso_canonical T.leaves (leaves_positive T)
  have hN := N_isomorphic hi
  obtain ⟨hle, huniq⟩ := conjecture14i T
  refine ⟨by omega, ?_⟩
  intro heq
  exact (huniq (heq.trans hN)).trans hi.symm

/-- Conjecture 14(ii), now with exactly the recursive tree of Theorem 7. -/
theorem conjecture14ii_paper : ∀ (T : Shape) (z : ℕ),
    Nat.clog 2 T.leaves ≤ z → z ≤ T.leaves - 1 →
      E T z ≤ E (ustar T.leaves) z := by
  intro T z hlo hhi
  rw [E_isomorphic (ustar_iso_canonical T.leaves (leaves_positive T))]
  exact conjecture14ii T z hlo hhi

end DickeyRosenberg
