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


namespace DR

/-- A code for an unordered pair, with zero reserved for a leaf. -/
def join (a b : ℕ) : ℕ := Nat.pair (min a b) (max a b) + 1

@[simp] theorem join_comm (a b : ℕ) : join a b = join b a := by
  simp [join, min_comm, max_comm]

@[simp] theorem join_ne_zero (a b : ℕ) : join a b ≠ 0 := by
  simp [join]

theorem join_eq_iff {a b c d : ℕ} :
    join a b = join c d ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  simp only [join, Nat.add_right_cancel_iff, Nat.pair_eq_pair]
  constructor
  · intro h
    rcases le_total a b with hab | hab <;> rcases le_total c d with hcd | hcd
    · simp [min_eq_left hab, max_eq_right hab, min_eq_left hcd, max_eq_right hcd] at h
      exact Or.inl h
    · simp [min_eq_left hab, max_eq_right hab, min_eq_right hcd, max_eq_left hcd] at h
      exact Or.inr h
    · simp [min_eq_right hab, max_eq_left hab, min_eq_left hcd, max_eq_right hcd] at h
      exact Or.inr ⟨h.2, h.1⟩
    · simp [min_eq_right hab, max_eq_left hab, min_eq_right hcd, max_eq_left hcd] at h
      exact Or.inl ⟨h.2, h.1⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp [min_comm, max_comm]

end DR

namespace BTree
open DR

/-- A computable complete invariant of unordered tree shapes. -/
def code : BTree → ℕ
  | leaf => 0
  | node a b => join a.code b.code

@[simp] theorem code_eq_zero (T : BTree) : T.code = 0 ↔ T = leaf := by
  cases T <;> simp [code]

theorem iso_iff_code_eq (T U : BTree) : Iso T U ↔ T.code = U.code := by
  induction T generalizing U with
  | leaf => cases U <;> simp [code, @eq_comm _ 0, Iso.leaf, show ∀ a b, ¬ Iso leaf (node a b) from
      fun a b h => by cases h]
  | node a b ha hb =>
    cases U with
    | leaf => simp [code, show ¬ Iso (node a b) leaf from fun h => by cases h]
    | node c d =>
      rw [code, code, join_eq_iff, ← ha, ← hb, ← ha, ← hb]
      constructor
      · intro h; cases h with
        | node h₁ h₂ => exact Or.inl ⟨h₁, h₂⟩
        | swap h₁ h₂ => exact Or.inr ⟨h₁, h₂⟩
      · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
        · exact Iso.node h₁ h₂
        · exact Iso.swap h₁ h₂

theorem eqvGen_iff_code_eq (T U : BTree) :
    Relation.EqvGen Iso T U ↔ T.code = U.code := by
  constructor
  · intro h
    induction h with
    | rel a b h => exact (iso_iff_code_eq a b).mp h
    | refl a => rfl
    | symm a b _ h => exact h.symm
    | trans a b c _ _ h₁ h₂ => exact h₁.trans h₂
  · intro h
    exact Relation.EqvGen.rel _ _ ((iso_iff_code_eq T U).mpr h)

theorem eqvGen_iff_iso (T U : BTree) : Relation.EqvGen Iso T U ↔ Iso T U := by
  rw [eqvGen_iff_code_eq, iso_iff_code_eq]

def shapeCode : Quotient shapeSetoid → ℕ :=
  Quotient.lift code (fun a b h => (eqvGen_iff_code_eq a b).mp h)

theorem shapeCode_injective : Function.Injective shapeCode := by
  intro x y
  induction x using Quotient.inductionOn with | _ a =>
    induction y using Quotient.inductionOn with | _ b =>
      intro h
      exact Quotient.sound ((eqvGen_iff_code_eq a b).mpr h)

/-- The finite set of pruning shapes, including the trivial pruning. -/
def shapes (T : BTree) : Finset ℕ := T.prunings.image code

@[simp] theorem leaf_mem_prunings (T : BTree) : leaf ∈ T.prunings := by
  cases T <;> simp [prunings]

@[simp] theorem zero_mem_shapes (T : BTree) : 0 ∈ T.shapes := by
  exact Finset.mem_image.mpr ⟨leaf, leaf_mem_prunings T, rfl⟩

@[simp] theorem shapes_leaf : shapes leaf = {0} := by simp [shapes, prunings, code]

theorem rootConfigs_eq_card_erase (T : BTree) :
    T.rootConfigs = (T.shapes.erase 0).card := by
  classical
  let f : {s : Quotient shapeSetoid //
      ∃ P ∈ T.prunings, P ≠ leaf ∧ Quotient.mk _ P = s} →
      {c : ℕ // c ∈ T.shapes.erase 0} := fun s =>
    ⟨shapeCode s.1, by
      obtain ⟨P, hP, hn, he⟩ := s.2
      rw [← he]
      apply Finset.mem_erase.mpr
      exact ⟨(code_eq_zero P).not.mpr hn, Finset.mem_image.mpr ⟨P, hP, rfl⟩⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      apply Subtype.ext
      apply shapeCode_injective
      exact congrArg Subtype.val h
    · rintro ⟨c, hc⟩
      obtain ⟨hne, hc⟩ := Finset.mem_erase.mp hc
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hc
      refine ⟨⟨Quotient.mk _ P, P, hP, ?_, rfl⟩, ?_⟩
      · exact (code_eq_zero P).not.mp hne
      · rfl
  exact (Nat.card_congr (Equiv.ofBijective f hf)).trans (Nat.card_eq_finsetCard _)

theorem rootConfigs_eq (T : BTree) : T.rootConfigs = T.shapes.card - 1 := by
  rw [rootConfigs_eq_card_erase, Finset.card_erase_of_mem (zero_mem_shapes T)]

theorem shapes_card (T : BTree) : T.shapes.card = T.rootConfigs + 1 := by
  have h := Finset.card_pos.mpr ⟨0, zero_mem_shapes T⟩
  rw [rootConfigs_eq]
  omega

@[simp] theorem rootConfigs_leaf : rootConfigs leaf = 0 := by
  simp [rootConfigs_eq]

end BTree

namespace DR

/-- The redundant ordered pairs: the reverse pair is present and has smaller first entry. -/
def bad (A B : Finset ℕ) : Finset (ℕ × ℕ) :=
  (A ×ˢ B).filter fun p => p.2 < p.1 ∧ p.2 ∈ A ∧ p.1 ∈ B

def good (A B : Finset ℕ) : Finset (ℕ × ℕ) := (A ×ˢ B) \ bad A B

theorem bad_subset (A B : Finset ℕ) : bad A B ⊆ A ×ˢ B := Finset.filter_subset _ _

theorem image_good (A B : Finset ℕ) :
    ((good A B).image fun p => join p.1 p.2) =
      ((A ×ˢ B).image fun p => join p.1 p.2) := by
  apply Finset.Subset.antisymm
  · exact Finset.image_subset_image Finset.sdiff_subset
  · intro z hz
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hz
    by_cases hbad : (a, b) ∈ bad A B
    · obtain ⟨_, hlt, hb, ha⟩ := Finset.mem_filter.mp hbad
      apply Finset.mem_image.mpr
      refine ⟨(b, a), Finset.mem_sdiff.mpr ⟨Finset.mem_product.mpr ⟨hb, ha⟩, ?_⟩,
        join_comm b a⟩
      intro h
      have := (Finset.mem_filter.mp h).2.1
      omega
    · exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_sdiff.mpr ⟨hab, hbad⟩, rfl⟩

theorem join_injOn_good (A B : Finset ℕ) :
    Set.InjOn (fun p : ℕ × ℕ => join p.1 p.2) (good A B) := by
  rintro ⟨a, b⟩ hx ⟨c, d⟩ hy he
  rcases join_eq_iff.mp he with he | he
  · exact Prod.ext he.1 he.2
  · obtain ⟨he₁, he₂⟩ := he
    dsimp at he₁ he₂
    subst c
    subst d
    obtain ⟨hx, hnx⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨hy, hny⟩ := Finset.mem_sdiff.mp hy
    obtain ⟨haA, hbB⟩ := Finset.mem_product.mp hx
    obtain ⟨hbA, haB⟩ := Finset.mem_product.mp hy
    have h₁ : a ≤ b := by
      by_contra h
      exact hnx (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨haA, hbB⟩,
        by omega, hbA, haB⟩)
    have h₂ : b ≤ a := by
      by_contra h
      exact hny (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hbA, haB⟩,
        by omega, haA, hbB⟩)
    have : a = b := by omega
    subst b
    rfl

theorem card_join_image (A B : Finset ℕ) :
    ((A ×ˢ B).image fun p => join p.1 p.2).card =
      A.card * B.card - (bad A B).card := by
  rw [← image_good, Finset.card_image_of_injOn (join_injOn_good A B), good,
    Finset.card_sdiff_of_subset (bad_subset A B), Finset.card_product]

end DR

namespace BTree
open DR

theorem shapes_node (l r : BTree) :
    (node l r).shapes = insert 0 ((l.shapes ×ˢ r.shapes).image fun p => join p.1 p.2) := by
  ext z
  simp only [shapes, prunings, Finset.mem_image, Finset.mem_insert,
    Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨P, hP, rfl⟩
    rcases hP with rfl | ⟨a, b, ⟨ha, hb⟩, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨a.code, b.code, ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩, rfl⟩
  · rintro (rfl | ⟨a, b, ⟨⟨P, hP, rfl⟩, ⟨Q, hQ, rfl⟩⟩, rfl⟩)
    · exact ⟨leaf, Or.inl rfl, rfl⟩
    · exact ⟨node P Q, Or.inr ⟨P, Q, ⟨hP, hQ⟩, rfl⟩, rfl⟩

theorem rootConfigs_node (l r : BTree) :
    (node l r).rootConfigs = l.shapes.card * r.shapes.card - (bad l.shapes r.shapes).card := by
  rw [rootConfigs_eq, shapes_node, Finset.card_insert_of_notMem, Nat.add_sub_cancel,
    card_join_image]
  simp only [Finset.mem_image, Prod.exists]
  rintro ⟨a, b, _, h⟩
  exact join_ne_zero a b h

theorem leaves_pos (T : BTree) : 1 ≤ T.leaves := by
  induction T with
  | leaf => simp [leaves]
  | node a b ha hb => simp only [leaves]; omega

theorem one_mem_shapes (T : BTree) (hT : 2 ≤ T.leaves) : 1 ∈ T.shapes := by
  cases T with
  | leaf => simp [leaves] at hT
  | node a b =>
    rw [shapes_node]
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨(0, 0), Finset.mem_product.mpr
      ⟨zero_mem_shapes a, zero_mem_shapes b⟩, by decide⟩

theorem two_mem_shapes (T : BTree) (hT : 3 ≤ T.leaves) : 2 ∈ T.shapes := by
  cases T with
  | leaf => simp [leaves] at hT
  | node a b =>
    rw [shapes_node]
    apply Finset.mem_insert_of_mem
    have ha := leaves_pos a
    have hb := leaves_pos b
    simp only [leaves] at hT
    by_cases h : 2 ≤ a.leaves
    · exact Finset.mem_image.mpr ⟨(1, 0), Finset.mem_product.mpr
        ⟨one_mem_shapes a h, zero_mem_shapes b⟩, by decide⟩
    · exact Finset.mem_image.mpr ⟨(0, 1), Finset.mem_product.mpr
        ⟨zero_mem_shapes a, one_mem_shapes b (by omega)⟩, by decide⟩

end BTree

namespace DR

/-- The forced number of duplicate pairs from the common small pruning shapes. -/
def loss (a b : ℕ) : ℕ :=
  if a = 1 ∨ b = 1 then 0 else if a = 2 ∨ b = 2 then 1 else 3

theorem loss_comm (a b : ℕ) : loss a b = loss b a := by simp [loss, or_comm]

theorem bad_two (B : Finset ℕ) (h0 : 0 ∈ B) (h1 : 1 ∈ B) :
    bad {0, 1} B = {(1, 0)} := by
  ext ⟨x, y⟩
  simp only [bad, Finset.mem_filter, Finset.mem_product, Finset.mem_insert,
    Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨hx, _⟩, hlt, hy, _⟩
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> omega
  · rintro ⟨rfl, rfl⟩
    simp [h0, h1]

theorem bad_three (B : Finset ℕ) (h0 : 0 ∈ B) (h1 : 1 ∈ B) (h2 : 2 ∈ B) :
    bad {0, 1, 2} B = {(1, 0), (2, 0), (2, 1)} := by
  ext ⟨x, y⟩
  simp only [bad, Finset.mem_filter, Finset.mem_product, Finset.mem_insert,
    Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨hx, _⟩, hlt, hy, _⟩
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp [h0, h1, h2]

end DR

namespace BTree
open DR

theorem loss_le_bad (l r : BTree) :
    loss l.leaves r.leaves ≤ (bad l.shapes r.shapes).card := by
  have hl := leaves_pos l
  have hr := leaves_pos r
  unfold loss
  split_ifs with h1 h2
  · omega
  · have hl2 : 2 ≤ l.leaves := by omega
    have hr2 : 2 ≤ r.leaves := by omega
    have hs : ({(1, 0)} : Finset (ℕ × ℕ)) ⊆ bad l.shapes r.shapes := by
      intro p hp
      have : p = (1, 0) := Finset.mem_singleton.mp hp
      subst p
      simp [bad, one_mem_shapes l hl2, one_mem_shapes r hr2]
    simpa using Finset.card_le_card hs
  · have hl3 : 3 ≤ l.leaves := by omega
    have hr3 : 3 ≤ r.leaves := by omega
    have hs : ({(1, 0), (2, 0), (2, 1)} : Finset (ℕ × ℕ)) ⊆
        bad l.shapes r.shapes := by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl <;>
        simp [bad, one_mem_shapes l (by omega), one_mem_shapes r (by omega),
          two_mem_shapes l hl3, two_mem_shapes r hr3]
    have hc := Finset.card_le_card hs
    norm_num at hc
    exact hc

def cherry : BTree := node leaf leaf

def triple : BTree := node leaf cherry

@[simp] theorem cherry_leaves : cherry.leaves = 2 := rfl
@[simp] theorem triple_leaves : triple.leaves = 3 := rfl

@[simp] theorem shapes_cherry : cherry.shapes = {0, 1} := by decide
@[simp] theorem shapes_triple : triple.shapes = {0, 1, 2} := by decide

theorem rootConfigs_cherry_node (T : BTree) (h : 2 ≤ T.leaves) :
    (node cherry T).rootConfigs = 2 * T.rootConfigs + 1 := by
  rw [rootConfigs_node, shapes_cherry,
    bad_two T.shapes (zero_mem_shapes T) (one_mem_shapes T h), shapes_card]
  norm_num
  omega

theorem rootConfigs_triple_node (T : BTree) (h : 3 ≤ T.leaves) :
    (node triple T).rootConfigs = 3 * T.rootConfigs := by
  rw [rootConfigs_node, shapes_triple,
    bad_three T.shapes (zero_mem_shapes T) (one_mem_shapes T (by omega))
      (two_mem_shapes T h), shapes_card]
  norm_num
  omega

end BTree

namespace DR

/-- The leaf case must be corrected separately in the conjectured formula. -/
def F (n : ℕ) : ℕ := if n = 1 then 0 else drMax n

theorem F_eq_drMax {n : ℕ} (hn : 2 ≤ n) : F n = drMax n := by
  simp [F, show n ≠ 1 by omega]

theorem drMax_closed {n : ℕ} (hn : 9 ≤ n) :
    drMax n = 3 ^ (n / 3 - 3) * (2 * (n % 3) ^ 2 + 8 * (n % 3) + 23) := by
  have hq : n / 3 = (n / 3 - 3) + 3 := by omega
  unfold drMax
  conv_lhs => rw [hq, pow_add]
  norm_num
  rw [show 3 ^ (n / 3 - 3) * 27 * (2 * (n % 3) ^ 2 + 8 * (n % 3) + 23) =
    (3 ^ (n / 3 - 3) * (2 * (n % 3) ^ 2 + 8 * (n % 3) + 23)) * 27 by ring]
  exact Nat.mul_div_cancel _ (by decide)

theorem F_add_three {n : ℕ} (hn : 9 ≤ n) : F (n + 3) = 3 * F n := by
  rw [F_eq_drMax (by omega), F_eq_drMax (by omega),
    drMax_closed (by omega), drMax_closed hn]
  have hq : (n + 3) / 3 - 3 = (n / 3 - 3) + 1 := by omega
  have hr : (n + 3) % 3 = n % 3 := by omega
  rw [hq, hr, pow_succ]
  ring

theorem F_ge_two {n : ℕ} (hn : 3 ≤ n) : 2 ≤ F n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h : 12 ≤ n
    · have hrec := F_add_three (n := n - 3) (by omega)
      have hi := ih (n - 3) (by omega) (by omega)
      have he : n - 3 + 3 = n := by omega
      rw [he] at hrec
      omega
    · have hfin : ∀ k ∈ Finset.Icc 3 11, 2 ≤ F k := by decide
      exact hfin n (by simp; omega)

theorem loss_le_F {a b : ℕ} (ha : 1 ≤ a) : loss a b ≤ F a + 1 := by
  unfold loss
  split_ifs with h1 h2
  · omega
  · omega
  · have := F_ge_two (n := a) (by omega)
    omega

theorem loss_add_three_right (a b : ℕ) (hb : 3 ≤ b) : loss a (b + 3) = loss a b := by
  simp [loss, show b ≠ 1 by omega, show b ≠ 2 by omega,
    show b + 3 ≠ 1 by omega, show b + 3 ≠ 2 by omega]

theorem arithmetic_small : ∀ a ∈ Finset.Icc 1 11, ∀ b ∈ Finset.Icc 1 11,
    (F a + 1) * (F b + 1) ≤ F (a + b) + loss a b := by decide

/-- Scaling one argument by three reduces the arithmetic lemma to finitely many cases. -/
theorem arithmetic (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (F a + 1) * (F b + 1) ≤ F (a + b) + loss a b := by
  suffices h : ∀ n a b : ℕ, a + b = n → 1 ≤ a → 1 ≤ b →
      (F a + 1) * (F b + 1) ≤ F (a + b) + loss a b from h (a + b) a b rfl ha hb
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a b hab ha hb
    by_cases hB : 12 ≤ b
    · have hi := ih (a + (b - 3)) (by omega) a (b - 3) rfl ha (by omega)
      have hbrec := F_add_three (n := b - 3) (by omega)
      have hsrec := F_add_three (n := a + (b - 3)) (by omega)
      have hloss := loss_add_three_right a (b - 3) (by omega)
      have hlow := loss_le_F (b := b - 3) ha
      have he : b - 3 + 3 = b := by omega
      have hes : a + (b - 3) + 3 = a + b := by omega
      rw [he] at hbrec hloss
      rw [hes] at hsrec
      rw [hbrec, hsrec, hloss]
      nlinarith
    · by_cases hA : 12 ≤ a
      · have hi := ih ((a - 3) + b) (by omega) (a - 3) b rfl (by omega) hb
        have harec := F_add_three (n := a - 3) (by omega)
        have hsrec := F_add_three (n := (a - 3) + b) (by omega)
        have hloss := loss_add_three_right b (a - 3) (by omega)
        have hlow := loss_le_F (b := a - 3) hb
        have he : a - 3 + 3 = a := by omega
        have hes : (a - 3) + b + 3 = a + b := by omega
        rw [he, loss_comm b a, loss_comm b (a - 3)] at hloss
        rw [he] at harec
        rw [hes] at hsrec
        rw [loss_comm b (a - 3)] at hlow
        rw [harec, hsrec, hloss]
        nlinarith
      · exact arithmetic_small a (by simp; omega) b (by simp; omega)

end DR

namespace BTree
open DR

/-- The universal upper bound on the number of root configurations. -/
theorem rootConfigs_le (T : BTree) : T.rootConfigs ≤ F T.leaves := by
  induction T with
  | leaf => simp [leaves, F]
  | node l r hl hr =>
    have hprod : l.shapes.card * r.shapes.card ≤
        (F l.leaves + 1) * (F r.leaves + 1) := by
      rw [shapes_card, shapes_card]
      exact Nat.mul_le_mul (by omega) (by omega)
    have hbound := arithmetic l.leaves r.leaves (leaves_pos l) (leaves_pos r)
    have hloss := loss_le_bad l r
    rw [rootConfigs_node, leaves]
    omega

/-- The eleven initial extremal trees. -/
def seed (n : ℕ) : BTree :=
  let u4 := node leaf triple
  let u5 := node cherry triple
  let u6 := node cherry u4
  let u7 := node cherry u5
  let u8 := node cherry u6
  let u9 := node cherry u7
  match n with
  | 2 => cherry
  | 3 => triple
  | 4 => u4
  | 5 => u5
  | 6 => u6
  | 7 => u7
  | 8 => u8
  | 9 => u9
  | 10 => node triple u7
  | 11 => node cherry u9
  | _ => leaf

theorem seed_correct : ∀ n ∈ Finset.Icc 1 11,
    (seed n).leaves = n ∧ (seed n).shapes.card - 1 = F n := by decide

/-- An explicit maximizing family, extended by grafting a three-leaf tree. -/
def extremal (n : ℕ) : BTree :=
  if n < 12 then seed n else node triple (extremal (n - 3))
termination_by n

theorem extremal_correct (n : ℕ) (hn : 1 ≤ n) :
    (extremal n).leaves = n ∧ (extremal n).rootConfigs = F n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h : n < 12
    · rw [extremal, if_pos h, rootConfigs_eq]
      exact seed_correct n (by simp; omega)
    · have hi := ih (n - 3) (by omega) (by omega)
      rw [extremal, if_neg h]
      constructor
      · simp only [leaves, triple_leaves, hi.1]
        omega
      · rw [rootConfigs_triple_node _ (by rw [hi.1]; omega), hi.2,
          ← F_add_three (by omega)]
        congr 1
        omega

end BTree

namespace BTree
open DR

theorem Iso.leaves_eq {T U : BTree} (h : Iso T U) : T.leaves = U.leaves := by
  induction h with
  | leaf => rfl
  | node _ _ h₁ h₂ => simp only [leaves, h₁, h₂]
  | swap _ _ h₁ h₂ => simp only [leaves, h₁, h₂, Nat.add_comm]

@[simp] theorem self_mem_prunings (T : BTree) : T ∈ T.prunings := by
  induction T with
  | leaf => simp [prunings]
  | node l r hl hr =>
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨(l, r), Finset.mem_product.mpr ⟨hl, hr⟩, rfl⟩

/-- There is a pruning with every leaf count between one and that of the original tree. -/
theorem pruning_with_leaves (T : BTree) (k : ℕ) (hk : 1 ≤ k) (hkT : k ≤ T.leaves) :
    ∃ P ∈ T.prunings, P.leaves = k := by
  induction T generalizing k with
  | leaf =>
    have he : k = 1 := by simp only [leaves] at hkT; omega
    subst k
    exact ⟨leaf, leaf_mem_prunings leaf, rfl⟩
  | node l r hl hr =>
    by_cases he : k = 1
    · subst k
      exact ⟨leaf, leaf_mem_prunings _, rfl⟩
    · by_cases hkl : k - 1 ≤ l.leaves
      · obtain ⟨P, hP, hPk⟩ := hl (k - 1) (by omega) hkl
        refine ⟨node P leaf, ?_, ?_⟩
        · apply Finset.mem_insert_of_mem
          exact Finset.mem_image.mpr ⟨(P, leaf),
            Finset.mem_product.mpr ⟨hP, leaf_mem_prunings r⟩, rfl⟩
        · simp only [leaves, hPk]
          omega
      · have hp := leaves_pos l
        simp only [leaves] at hkT
        obtain ⟨Q, hQ, hQk⟩ := hr (k - l.leaves) (by omega) (by omega)
        refine ⟨node l Q, ?_, ?_⟩
        · apply Finset.mem_insert_of_mem
          exact Finset.mem_image.mpr ⟨(l, Q),
            Finset.mem_product.mpr ⟨self_mem_prunings l, hQ⟩, rfl⟩
        · simp only [leaves, hQk]
          omega

/-- Every tree with `n` leaves has at least `n - 1` root configurations. -/
theorem rootConfigs_min (T : BTree) : T.leaves - 1 ≤ T.rootConfigs := by
  classical
  have hp : ∀ k : (Finset.Icc 1 T.leaves),
      ∃ P ∈ T.prunings, P.leaves = (k : ℕ) := by
    intro k
    exact pruning_with_leaves T k (Finset.mem_Icc.mp k.2).1 (Finset.mem_Icc.mp k.2).2
  choose P hP hPk using hp
  let f : (Finset.Icc 1 T.leaves) → T.shapes := fun k =>
    ⟨(P k).code, Finset.mem_image.mpr ⟨P k, hP k, rfl⟩⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    have he : (P x).code = (P y).code := congrArg Subtype.val h
    have hl := ((iso_iff_code_eq _ _).mpr he).leaves_eq
    simpa only [hPk] using hl
  have hc : T.leaves ≤ T.shapes.card := by
    simpa using Finset.card_le_card_of_injective hf
  rw [rootConfigs_eq]
  omega

theorem rootConfigs_leaf_node (T : BTree) :
    (node leaf T).rootConfigs = T.rootConfigs + 1 := by
  have hb : bad {0} T.shapes = ∅ := by
    ext ⟨a, b⟩
    simp only [bad, Finset.mem_filter, Finset.mem_product, Finset.mem_singleton,
      Finset.notMem_empty, iff_false]
    rintro ⟨⟨rfl, _⟩, h, _⟩
    omega
  rw [rootConfigs_node, shapes_leaf, hb]
  simp [shapes_card]

/-- A caterpillar with `n + 1` leaves. -/
def caterpillar : ℕ → BTree
  | 0 => leaf
  | n + 1 => node leaf (caterpillar n)

theorem caterpillar_correct (n : ℕ) :
    (caterpillar n).leaves = n + 1 ∧ (caterpillar n).rootConfigs = n := by
  induction n with
  | zero => simp [caterpillar, leaves]
  | succ n ih =>
    constructor
    · change 1 + (caterpillar n).leaves = n + 1 + 1
      rw [ih.1]
      omega
    · change (node leaf (caterpillar n)).rootConfigs = n + 1
      rw [rootConfigs_leaf_node, ih.2]

end BTree

/-- The minimum is attained by the caterpillar. -/
theorem disanto_rosenberg_minimum (n : ℕ) (hn : 1 ≤ n) :
    IsLeast {k | ∃ T : BTree, T.leaves = n ∧ T.rootConfigs = k} (n - 1) := by
  constructor
  · obtain ⟨hl, hc⟩ := BTree.caterpillar_correct (n - 1)
    exact ⟨BTree.caterpillar (n - 1), by omega, hc⟩
  · rintro k ⟨T, hT, rfl⟩
    simpa only [hT] using T.rootConfigs_min

namespace DR

def eligible (n : ℕ) : Prop := n ≠ 4 ∧ n ≠ 6 ∧ n ≠ 8
instance (n : ℕ) : Decidable (eligible n) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem F_ge_three {n : ℕ} (hn : 4 ≤ n) : 3 ≤ F n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h : 12 ≤ n
    · have hrec := F_add_three (n := n - 3) (by omega)
      have hi := ih (n - 3) (by omega) (by omega)
      have he : n - 3 + 3 = n := by omega
      rw [he] at hrec
      omega
    · have hfin : ∀ k ∈ Finset.Icc 4 11, 3 ≤ F k := by decide
      exact hfin n (by simp; omega)

theorem loss_eq_F_forces_three {a b : ℕ} (ha : 1 ≤ a) (hb : 3 ≤ b)
    (h : F a + 1 = loss a b) : a = 3 := by
  by_cases h1 : a = 1
  · subst a
    simp [F, loss] at h
  by_cases h2 : a = 2
  · subst a
    have hb1 : b ≠ 1 := by omega
    norm_num [F, drMax, loss, hb1] at h
  by_contra h3
  have hlow := F_ge_three (n := a) (by omega)
  have hle : loss a b ≤ 3 := by unfold loss; split_ifs <;> omega
  omega

/-- In an equality case with a large second subtree, the first subtree has three leaves. -/
theorem arithmetic_eq_right {a b : ℕ} (ha : 1 ≤ a) (hb : 12 ≤ b)
    (heq : (F a + 1) * (F b + 1) = F (a + b) + loss a b) : a = 3 := by
  have hi := arithmetic a (b - 3) ha (by omega)
  have hbrec := F_add_three (n := b - 3) (by omega)
  have hsrec := F_add_three (n := a + (b - 3)) (by omega)
  have hloss := loss_add_three_right a (b - 3) (by omega)
  have hlow := loss_le_F (b := b - 3) ha
  have he : b - 3 + 3 = b := by omega
  have hes : a + (b - 3) + 3 = a + b := by omega
  rw [he] at hbrec hloss
  rw [hes] at hsrec
  rw [hbrec, hsrec, hloss] at heq
  apply loss_eq_F_forces_three ha (b := b - 3) (by omega)
  nlinarith

theorem arithmetic_eq_left {a b : ℕ} (ha : 12 ≤ a) (hb : 1 ≤ b)
    (heq : (F a + 1) * (F b + 1) = F (a + b) + loss a b) : b = 3 := by
  apply arithmetic_eq_right hb ha
  simpa only [Nat.mul_comm, Nat.add_comm, loss_comm b a] using heq

theorem small_maximizer_children :
    ∀ a ∈ Finset.Icc 1 11, ∀ b ∈ Finset.Icc 1 11, eligible (a + b) →
      (F a + 1) * (F b + 1) = F (a + b) + loss a b → eligible a ∧ eligible b ∧ a + b ≤ 14 := by decide

end DR

namespace BTree
open DR

theorem Iso.shapes_eq {T U : BTree} (h : Iso T U) : T.shapes = U.shapes := by
  induction h with
  | leaf => rfl
  | node _ _ h₁ h₂ => simp only [shapes_node, h₁, h₂]
  | @swap a b c d _ _ h₁ h₂ =>
    simp only [shapes_node, h₁, h₂]
    congr 1
    ext z
    simp only [Finset.mem_image, Prod.exists, Finset.mem_product]
    constructor
    · rintro ⟨x, y, ⟨hx, hy⟩, he⟩
      exact ⟨y, x, ⟨hy, hx⟩, by rw [join_comm]; exact he⟩
    · rintro ⟨x, y, ⟨hx, hy⟩, he⟩
      exact ⟨y, x, ⟨hy, hx⟩, by rw [join_comm]; exact he⟩

theorem Iso.rootConfigs_eq {T U : BTree} (h : Iso T U) : T.rootConfigs = U.rootConfigs := by
  simp only [BTree.rootConfigs_eq, h.shapes_eq]

theorem maximizing_node {l r : BTree}
    (h : (node l r).rootConfigs = F (l.leaves + r.leaves)) :
    l.rootConfigs = F l.leaves ∧ r.rootConfigs = F r.leaves ∧
      (F l.leaves + 1) * (F r.leaves + 1) =
        F (l.leaves + r.leaves) + loss l.leaves r.leaves := by
  have hl := l.rootConfigs_le
  have hr := r.rootConfigs_le
  have hloss := loss_le_bad l r
  have harith := arithmetic l.leaves r.leaves (leaves_pos l) (leaves_pos r)
  have hb : (bad l.shapes r.shapes).card ≤ l.shapes.card * r.shapes.card := by
    simpa using Finset.card_le_card (bad_subset l.shapes r.shapes)
  have hactual := Nat.sub_add_cancel hb
  rw [← rootConfigs_node, h, shapes_card, shapes_card] at hactual
  have hp : (l.rootConfigs + 1) * (r.rootConfigs + 1) ≤
      (F l.leaves + 1) * (F r.leaves + 1) := Nat.mul_le_mul (by omega) (by omega)
  have heq : (F l.leaves + 1) * (F r.leaves + 1) =
      F (l.leaves + r.leaves) + loss l.leaves r.leaves := by omega
  have hprod : (l.rootConfigs + 1) * (r.rootConfigs + 1) =
      (F l.leaves + 1) * (F r.leaves + 1) := by omega
  refine ⟨?_, ?_, heq⟩
  · by_contra he
    have hh : l.rootConfigs + 1 ≤ F l.leaves := by omega
    have hh' := Nat.mul_le_mul hh (show r.rootConfigs + 1 ≤ F r.leaves + 1 by omega)
    nlinarith
  · by_contra he
    have hh : r.rootConfigs + 1 ≤ F r.leaves := by omega
    have hh' := Nat.mul_le_mul (show l.rootConfigs + 1 ≤ F l.leaves + 1 by omega) hh
    nlinarith

/-- The initial family, without recursion, for checking the small equality cases. -/
def lowExtremal (n : ℕ) : BTree :=
  if n < 12 then seed n else node triple (seed (n - 3))

theorem extremal_low {n : ℕ} (hn : n ≤ 14) : extremal n = lowExtremal n := by
  rw [extremal, lowExtremal]
  split_ifs with h
  · rfl
  · rw [extremal, if_pos (by omega)]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
/-- This finite check also eliminates the spurious arithmetic equality cases
`(5,5)`, `(5,7)`, `(5,9)`, and `(7,7)`, whose common prunings give a strict loss. -/
theorem small_maximizer_shapes :
    ∀ a ∈ Finset.Icc 1 11, ∀ b ∈ Finset.Icc 1 11, eligible (a + b) →
      (F a + 1) * (F b + 1) = F (a + b) + loss a b →
      (node (seed a) (seed b)).shapes.card - 1 = F (a + b) →
      (node (seed a) (seed b)).code = (lowExtremal (a + b)).code := by
  intro a ha b hb hel harith hshape
  obtain ⟨ha1, ha2⟩ := Finset.mem_Icc.mp ha
  obtain ⟨hb1, hb2⟩ := Finset.mem_Icc.mp hb
  interval_cases a <;> interval_cases b
  all_goals simp [eligible] at hel
  all_goals norm_num [F, drMax, loss] at harith
  all_goals
    first
    | decide
    | rw [← BTree.rootConfigs_eq, rootConfigs_node] at hshape
      revert hshape
      decide

end BTree

namespace BTree
open DR

@[simp] theorem extremal_three : extremal 3 = triple := by rw [extremal]; rfl

/-- All maximizers are unique except at the small leaf counts 4, 6, and 8. -/
theorem extremal_unique_all (n : ℕ) (he : eligible n) (T : BTree)
    (hleaves : T.leaves = n) (hmax : T.rootConfigs = F n) : Iso T (extremal n) := by
  induction n using Nat.strong_induction_on generalizing T with
  | h n ih =>
    cases T with
    | leaf =>
      have hn : n = 1 := hleaves.symm
      subst n
      change Iso leaf (extremal 1)
      rw [extremal]
      exact Iso.leaf
    | node l r =>
      simp only [leaves] at hleaves
      have hlpos := leaves_pos l
      have hrpos := leaves_pos r
      obtain ⟨hlmax, hrmax, harith⟩ := maximizing_node (l := l) (r := r) (by simpa only [hleaves] using hmax)
      have hel : eligible (l.leaves + r.leaves) := by rwa [hleaves]
      by_cases hB : 12 ≤ r.leaves
      · have ha : l.leaves = 3 := arithmetic_eq_right hlpos hB harith
        have hl := ih l.leaves (by omega) (by simp [eligible, ha]) l rfl hlmax
        have hr := ih r.leaves (by omega) (by dsimp [eligible]; omega) r rfl hrmax
        have hn : ¬ n < 12 := by omega
        have hext : extremal n = node (extremal l.leaves) (extremal r.leaves) := by
          rw [extremal, if_neg hn, ha, extremal_three]
          congr 2
          omega
        rw [hext]
        exact Iso.node hl hr
      · by_cases hA : 12 ≤ l.leaves
        · have hb : r.leaves = 3 := arithmetic_eq_left hA hrpos harith
          have hl := ih l.leaves (by omega) (by dsimp [eligible]; omega) l rfl hlmax
          have hr := ih r.leaves (by omega) (by simp [eligible, hb]) r rfl hrmax
          have hn : ¬ n < 12 := by omega
          have hext : extremal n = node (extremal r.leaves) (extremal l.leaves) := by
            rw [extremal, if_neg hn, hb, extremal_three]
            congr 2
            omega
          rw [hext]
          exact Iso.swap hl hr
        · have hla : l.leaves ∈ Finset.Icc 1 11 := by simp; omega
          have hra : r.leaves ∈ Finset.Icc 1 11 := by simp; omega
          obtain ⟨heL, heR, hsum⟩ := small_maximizer_children l.leaves hla r.leaves hra hel harith
          have hl := ih l.leaves (by omega) heL l rfl hlmax
          have hr := ih r.leaves (by omega) heR r rfl hrmax
          rw [extremal, if_pos (by omega)] at hl
          rw [extremal, if_pos (by omega)] at hr
          have hiso := Iso.node hl hr
          have hs : (node (seed l.leaves) (seed r.leaves)).shapes.card - 1 =
              F (l.leaves + r.leaves) := by
            rw [← BTree.rootConfigs_eq, ← hiso.rootConfigs_eq, hmax, hleaves]
          have hc := small_maximizer_shapes l.leaves hla r.leaves hra hel harith hs
          apply (iso_iff_code_eq _ _).mpr
          rw [extremal_low (by omega)]
          exact ((iso_iff_code_eq _ _).mp hiso).trans (by simpa only [hleaves] using hc)

end BTree

/-- For nine or more leaves, every maximizer has the shape of the explicit extremal tree. -/
theorem disanto_rosenberg_unique (n : ℕ) (hn : 9 ≤ n) (T : BTree)
    (hleaves : T.leaves = n) (hmax : T.rootConfigs = drMax n) :
    BTree.Iso T (BTree.extremal n) := by
  apply BTree.extremal_unique_all n (by dsimp [DR.eligible]; omega) T hleaves
  rwa [DR.F_eq_drMax (by omega)]

/-- **Disanto–Rosenberg conjecture.** For `n ≥ 2`, `drMax n` is the maximum number of
non-equivalent root ancestral configurations over trees with `n` leaves. -/
theorem disanto_rosenberg (n : ℕ) (hn : 2 ≤ n) :
    IsGreatest {k | ∃ T : BTree, T.leaves = n ∧ T.rootConfigs = k} (drMax n) := by
  constructor
  · obtain ⟨hl, hc⟩ := BTree.extremal_correct n (by omega)
    exact ⟨BTree.extremal n, hl, hc.trans (DR.F_eq_drMax hn)⟩
  · rintro k ⟨T, hT, rfl⟩
    have h := T.rootConfigs_le
    rwa [hT, DR.F_eq_drMax hn] at h

end KOS.AncestralConfigurations
