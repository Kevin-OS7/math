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

namespace KOS.AncestralConfigurationsIndependent


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

/-! ## Proof

Outline (following `PROOF.md`):
1. Canonical forms: `canon : BTree → BTree` with `canon x = canon y ↔ Iso x y`; hence
   `rootConfigs T = #(S T) - 1` where `S T = T.prunings.image canon` (one tree per shape).
2. Recursion `S (node l r) = insert leaf (image₂ cnode (S l) (S r))`, plus counting bounds for
   `image₂ cnode`.
3. The shapes `leaf`, `cherry`, `c3` are shapes of prunings of every tree with enough leaves.
4. The arithmetic lemma `lemD`.
5. Upper bound `#(S T) ≤ F n + 1` by induction on `T`; matching lower bound by an explicit family.
-/

namespace BTree

/-! ### Canonical forms -/

/-- An injective encoding of plane binary trees into `ℕ`. -/
def enc : BTree → ℕ
  | leaf => 0
  | node l r => Nat.pair (enc l) (enc r) + 1

theorem enc_injective : Function.Injective enc := by
  intro x
  induction x with
  | leaf =>
    intro y h
    cases y with
    | leaf => rfl
    | node l r => simp only [enc] at h; omega
  | node a b iha ihb =>
    intro y h
    cases y with
    | leaf => simp only [enc] at h; omega
    | node c d =>
      simp only [enc, Nat.add_right_cancel_iff, Nat.pair_eq_pair] at h
      rw [iha h.1, ihb h.2]

/-- The node with children `x` and `y`, put in a canonical order. -/
def cnode (x y : BTree) : BTree := if enc x ≤ enc y then node x y else node y x

theorem cnode_comm (x y : BTree) : cnode x y = cnode y x := by
  unfold cnode
  by_cases h1 : enc x ≤ enc y <;> by_cases h2 : enc y ≤ enc x
  · have : x = y := enc_injective (le_antisymm h1 h2)
    subst this; rfl
  · simp [h1, h2]
  · simp [h1, h2]
  · exfalso; omega

theorem cnode_ne_leaf (x y : BTree) : cnode x y ≠ leaf := by
  unfold cnode; split <;> simp

theorem cnode_eq_cnode {x y x' y' : BTree} (h : cnode x y = cnode x' y') :
    (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  unfold cnode at h
  split_ifs at h <;> simp only [node.injEq] at h <;> tauto

theorem cnode_injective (t : BTree) : Function.Injective (cnode t) := by
  intro y y' h
  rcases cnode_eq_cnode h with ⟨_, h⟩ | ⟨h1, h2⟩
  · exact h
  · exact h2.trans h1

/-- Canonical representative of the isomorphism class of a tree. -/
def canon : BTree → BTree
  | leaf => leaf
  | node l r => cnode (canon l) (canon r)

theorem canon_eq_leaf_iff {x : BTree} : canon x = leaf ↔ x = leaf := by
  cases x with
  | leaf => simp [canon]
  | node l r => simpa [canon] using cnode_ne_leaf (canon l) (canon r)

theorem Iso.canon_eq {x y : BTree} (h : Iso x y) : canon x = canon y := by
  induction h with
  | leaf => rfl
  | node _ _ h1 h2 => simp only [canon, h1, h2]
  | swap _ _ h1 h2 => simp only [canon, h1, h2]; exact cnode_comm _ _

theorem iso_of_canon_eq {x y : BTree} (h : canon x = canon y) : Iso x y := by
  induction x generalizing y with
  | leaf =>
    cases y with
    | leaf => exact Iso.leaf
    | node c d =>
      exact absurd h.symm (by simpa [canon] using cnode_ne_leaf (canon c) (canon d))
  | node a b iha ihb =>
    cases y with
    | leaf => exact absurd h (by simpa [canon] using cnode_ne_leaf (canon a) (canon b))
    | node c d =>
      simp only [canon] at h
      rcases cnode_eq_cnode h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Iso.node (iha h1) (ihb h2)
      · exact Iso.swap (iha h1) (ihb h2)

theorem eqvGen_iso_iff {x y : BTree} : Relation.EqvGen Iso x y ↔ canon x = canon y := by
  constructor
  · intro h
    induction h with
    | rel _ _ h => exact h.canon_eq
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  · intro h
    exact Relation.EqvGen.rel _ _ (iso_of_canon_eq h)

/-- `canon` descends to shapes. -/
def qcanon : Quotient shapeSetoid → BTree :=
  Quotient.lift canon (fun _ _ h => eqvGen_iso_iff.1 h)

@[simp] theorem qcanon_mk (P : BTree) : qcanon (Quotient.mk _ P) = canon P := rfl

theorem qcanon_injective : Function.Injective qcanon := by
  intro q₁ q₂ h
  induction q₁ using Quotient.inductionOn
  induction q₂ using Quotient.inductionOn
  exact Quotient.sound (eqvGen_iso_iff.2 h)

/-! ### Shapes of prunings -/

/-- Canonical forms of the prunings of `T` (one tree per shape). -/
def S (T : BTree) : Finset BTree := T.prunings.image canon

theorem rootConfigs_eq_card_erase (T : BTree) : T.rootConfigs = ((S T).erase leaf).card := by
  have mem : ∀ s : {s : Quotient shapeSetoid // ∃ P ∈ T.prunings, P ≠ leaf ∧ Quotient.mk _ P = s},
      qcanon s.1 ∈ (S T).erase leaf := by
    rintro ⟨q, P, hP, hPl, rfl⟩
    simp only [qcanon_mk, Finset.mem_erase, S, Finset.mem_image]
    exact ⟨fun h => hPl (canon_eq_leaf_iff.1 h), P, hP, rfl⟩
  rw [← Nat.card_eq_finsetCard]
  unfold rootConfigs
  apply Nat.card_congr
  refine Equiv.ofBijective (fun s => ⟨qcanon s.1, mem s⟩) ⟨?_, ?_⟩
  · intro s t h
    exact Subtype.ext (qcanon_injective (congrArg Subtype.val h))
  · rintro ⟨z, hz⟩
    simp only [Finset.mem_erase, S, Finset.mem_image] at hz
    obtain ⟨hzl, P, hP, rfl⟩ := hz
    exact ⟨⟨Quotient.mk _ P, P, hP, fun h => hzl (by rw [h]; rfl), rfl⟩, rfl⟩

theorem S_leaf : S leaf = {leaf} := rfl

theorem S_node (l r : BTree) :
    S (node l r) = insert leaf (Finset.image₂ cnode (S l) (S r)) := by
  ext z
  simp only [S, prunings, Finset.mem_image, Finset.mem_insert, Finset.mem_product,
    Finset.mem_image₂]
  constructor
  · rintro ⟨P, hP | ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩, rfl⟩
    · left; subst hP; rfl
    · right; exact ⟨canon x, ⟨x, hx, rfl⟩, canon y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro (rfl | ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩)
    · exact ⟨leaf, Or.inl rfl, rfl⟩
    · exact ⟨node x y, Or.inr ⟨(x, y), ⟨hx, hy⟩, rfl⟩, rfl⟩

theorem leaf_mem_S (T : BTree) : leaf ∈ S T := by
  cases T with
  | leaf => simp [S_leaf]
  | node l r => rw [S_node]; exact Finset.mem_insert_self _ _

theorem leaf_not_mem_image₂ (A B : Finset BTree) : leaf ∉ Finset.image₂ cnode A B := by
  simp only [Finset.mem_image₂, not_exists, not_and]
  intro x _ y _ h
  exact cnode_ne_leaf x y h

theorem card_S_node (l r : BTree) :
    (S (node l r)).card = (Finset.image₂ cnode (S l) (S r)).card + 1 := by
  rw [S_node, Finset.card_insert_of_notMem (leaf_not_mem_image₂ _ _)]

theorem leaves_pos (T : BTree) : 1 ≤ T.leaves := by
  induction T with
  | leaf => simp [leaves]
  | node l r hl _ => simp only [leaves]; omega

/-! ### Small shapes shared by all prunings sets -/

/-- The 2-leaf tree. -/
def cherry : BTree := node leaf leaf

/-- The 3-leaf tree (in canonical form). -/
def c3 : BTree := node leaf cherry

theorem cnode_leaf_leaf : cnode leaf leaf = cherry := by decide
theorem cnode_leaf_cherry : cnode leaf cherry = c3 := by decide
theorem cnode_cherry_leaf : cnode cherry leaf = c3 := by decide

theorem cherry_mem_S {T : BTree} (h : 2 ≤ T.leaves) : cherry ∈ S T := by
  cases T with
  | leaf => simp [leaves] at h
  | node l r =>
    rw [S_node, ← cnode_leaf_leaf]
    exact Finset.mem_insert_of_mem (Finset.mem_image₂_of_mem (leaf_mem_S l) (leaf_mem_S r))

theorem c3_mem_S {T : BTree} (h : 3 ≤ T.leaves) : c3 ∈ S T := by
  cases T with
  | leaf => simp [leaves] at h
  | node l r =>
    rw [S_node]
    apply Finset.mem_insert_of_mem
    simp only [leaves] at h
    by_cases hl : 2 ≤ l.leaves
    · rw [← cnode_cherry_leaf]
      exact Finset.mem_image₂_of_mem (cherry_mem_S hl) (leaf_mem_S r)
    · rw [← cnode_leaf_cherry]
      exact Finset.mem_image₂_of_mem (leaf_mem_S l) (cherry_mem_S (by omega))

/-! ### Counting -/

/-- Upper bound: the pairs in `R` can be dropped when their swaps are kept. -/
theorem card_image₂_add_le (A B : Finset BTree) (R : Finset (BTree × BTree))
    (hR : R ⊆ A ×ˢ B) (hsw : ∀ p ∈ R, p.swap ∈ A ×ˢ B ∧ p.swap ∉ R) :
    (Finset.image₂ cnode A B).card + R.card ≤ A.card * B.card := by
  have h1 : Finset.image₂ cnode A B ⊆ ((A ×ˢ B) \ R).image (fun p => cnode p.1 p.2) := by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_image₂.1 hz
    by_cases hp : (x, y) ∈ R
    · obtain ⟨h1, h2⟩ := hsw _ hp
      exact Finset.mem_image.2 ⟨(y, x), Finset.mem_sdiff.2 ⟨h1, h2⟩, cnode_comm y x⟩
    · exact Finset.mem_image.2
        ⟨(x, y), Finset.mem_sdiff.2 ⟨Finset.mem_product.2 ⟨hx, hy⟩, hp⟩, rfl⟩
  have h2 := (Finset.card_le_card h1).trans Finset.card_image_le
  rw [Finset.card_sdiff_of_subset hR, Finset.card_product] at h2
  have h3 := Finset.card_le_card hR
  rw [Finset.card_product] at h3
  omega

/-- Lower bound: `#(image₂ cnode A B) ≥ #A * #B - C(#A, 2)`. -/
theorem card_image₂_ge (A B : Finset BTree) :
    A.card * B.card ≤ (Finset.image₂ cnode A B).card + A.card.choose 2 := by
  induction A using Finset.induction_on with
  | empty => simp
  | insert t A ht ih =>
    rw [Finset.image₂_insert_left, Finset.card_insert_of_notMem ht]
    have hc := Finset.card_union_add_card_inter (B.image fun b => cnode t b)
      (Finset.image₂ cnode A B)
    have hX : (B.image fun b => cnode t b).card = B.card :=
      Finset.card_image_of_injective _ (cnode_injective t)
    have hI : ((B.image fun b => cnode t b) ∩ Finset.image₂ cnode A B).card ≤ A.card := by
      calc _ ≤ (A.image fun x => cnode t x).card := by
            apply Finset.card_le_card
            intro z hz
            rw [Finset.mem_inter, Finset.mem_image, Finset.mem_image₂] at hz
            obtain ⟨⟨y, hy, rfl⟩, ⟨x, hx, y', hy', h⟩⟩ := hz
            rcases cnode_eq_cnode h with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact absurd (h1 ▸ hx) ht
            · exact Finset.mem_image.2 ⟨x, hx, by rw [h1]⟩
        _ ≤ A.card := Finset.card_image_le
    have hch : (A.card + 1).choose 2 = A.card.choose 2 + A.card := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right, Nat.add_comm]
    rw [hch, Nat.add_mul, Nat.one_mul]
    omega

/-- The penalty `C(min k 3, 2)`. -/
def pen (k : ℕ) : ℕ := if k ≤ 1 then 0 else if k = 2 then 1 else 3

theorem card_image₂_S_add_pen (l r : BTree) :
    (Finset.image₂ cnode (S l) (S r)).card + pen (min l.leaves r.leaves) ≤
      (S l).card * (S r).card := by
  have hl1 := leaves_pos l
  have hr1 := leaves_pos r
  unfold pen
  split_ifs with h1 h2
  · simpa using Finset.card_image₂_le cnode (S l) (S r)
  · have hl : 2 ≤ l.leaves := by omega
    have hr : 2 ≤ r.leaves := by omega
    have := card_image₂_add_le (S l) (S r) {(cherry, leaf)}
      (Finset.singleton_subset_iff.2 (Finset.mem_product.2 ⟨cherry_mem_S hl, leaf_mem_S r⟩))
      (by
        intro p hp
        rw [Finset.mem_singleton] at hp
        subst hp
        exact ⟨Finset.mem_product.2 ⟨leaf_mem_S l, cherry_mem_S hr⟩, by decide⟩)
    simpa using this
  · have hl : 3 ≤ l.leaves := by omega
    have hr : 3 ≤ r.leaves := by omega
    have := card_image₂_add_le (S l) (S r) {(cherry, leaf), (c3, leaf), (c3, cherry)}
      (by
        simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.mem_product]
        exact ⟨⟨cherry_mem_S (by omega), leaf_mem_S r⟩, ⟨c3_mem_S hl, leaf_mem_S r⟩,
          ⟨c3_mem_S hl, cherry_mem_S (by omega)⟩⟩)
      (by
        intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl
        · exact ⟨Finset.mem_product.2 ⟨leaf_mem_S l, cherry_mem_S (by omega)⟩, by decide⟩
        · exact ⟨Finset.mem_product.2 ⟨leaf_mem_S l, c3_mem_S hr⟩, by decide⟩
        · exact ⟨Finset.mem_product.2 ⟨cherry_mem_S (by omega), c3_mem_S hr⟩, by decide⟩)
    have hcard :
        ({(cherry, leaf), (c3, leaf), (c3, cherry)} : Finset (BTree × BTree)).card = 3 := by
      decide
    omega

/-! ### Arithmetic -/

/-- `F 1 = 0` and `F n = drMax n` for `n ≠ 1`: `F n + 1` is the maximal number of shapes of
prunings (including the trivial one) of a tree with `n` leaves. -/
def F (n : ℕ) : ℕ := if n = 1 then 0 else drMax n

theorem drMax_rec3 (n : ℕ) (h : 12 ≤ n) : drMax n = 3 * drMax (n - 3) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 12 := ⟨n - 12, by omega⟩
  have h1 : (m + 12) / 3 = m / 3 + 4 := by omega
  have h2 : (m + 12) % 3 = m % 3 := by omega
  have h3 : (m + 12 - 3) / 3 = m / 3 + 3 := by omega
  have h4 : (m + 12 - 3) % 3 = m % 3 := by omega
  unfold drMax
  rw [h1, h2, h3, h4]
  generalize 2 * (m % 3) ^ 2 + 8 * (m % 3) + 23 = K
  generalize m / 3 = q
  have e1 : 3 ^ (q + 4) * K = 27 * (3 * 3 ^ q * K) := by ring
  have e2 : 3 ^ (q + 3) * K = 27 * (3 ^ q * K) := by ring
  rw [e1, e2, Nat.mul_div_cancel_left _ (by norm_num), Nat.mul_div_cancel_left _ (by norm_num)]
  ring

theorem F_rec3 (n : ℕ) (h : 12 ≤ n) : F n = 3 * F (n - 3) := by
  unfold F
  rw [if_neg (by omega), if_neg (by omega)]
  exact drMax_rec3 n h

theorem F_ge_two (n : ℕ) (h : 3 ≤ n) : 2 ≤ F n := by
  unfold F drMax
  rw [if_neg (by omega)]
  apply (Nat.le_div_iff_mul_le (by norm_num)).2
  have h1 : 3 ≤ 3 ^ (n / 3) := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ (n / 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 23 ≤ 2 * (n % 3) ^ 2 + 8 * (n % 3) + 23 := by omega
  have := Nat.mul_le_mul h1 h2
  omega

theorem pen_le (a b : ℕ) (hb : 1 ≤ b) : pen (min a b) ≤ F b + 1 := by
  by_cases h3 : 3 ≤ b
  · have := F_ge_two b h3
    unfold pen; split_ifs <;> omega
  · unfold pen; split_ifs <;> omega

theorem lemD_base : ∀ a < 12, ∀ b < 12, 1 ≤ a → 1 ≤ b →
    (F a + 1) * (F b + 1) - pen (min a b) ≤ F (a + b) := by
  decide

theorem step_arith (x y c z : ℕ) (hc : c ≤ y) (ih : (x + 1) * y - c ≤ z) :
    (3 * x + 1) * y - c ≤ 3 * z := by
  have h1 : (3 * x + 1) * y = 3 * (x * y) + y := by ring
  have h2 : (x + 1) * y = x * y + y := by ring
  rw [h1]
  rw [h2] at ih
  omega

theorem lemD_step (a b : ℕ) (ha : 12 ≤ a) (hb : 1 ≤ b)
    (ih : (F (a - 3) + 1) * (F b + 1) - pen (min (a - 3) b) ≤ F (a - 3 + b)) :
    (F a + 1) * (F b + 1) - pen (min a b) ≤ F (a + b) := by
  have e1 : F a = 3 * F (a - 3) := F_rec3 a ha
  have e2 : F (a + b) = 3 * F (a - 3 + b) := by
    rw [F_rec3 (a + b) (by omega), show a + b - 3 = a - 3 + b by omega]
  have e3 : pen (min a b) = pen (min (a - 3) b) := by
    unfold pen; split_ifs <;> omega
  have hc : pen (min a b) ≤ F b + 1 := pen_le a b hb
  rw [e1, e2, e3]
  rw [e3] at hc
  exact step_arith _ _ _ _ hc ih

theorem lemD_aux : ∀ s a b, a + b = s → 1 ≤ a → 1 ≤ b →
    (F a + 1) * (F b + 1) - pen (min a b) ≤ F (a + b) := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro a b hs ha hb
    by_cases ha12 : 12 ≤ a
    · exact lemD_step a b ha12 hb (ih (a - 3 + b) (by omega) (a - 3) b rfl (by omega) hb)
    by_cases hb12 : 12 ≤ b
    · have := lemD_step b a hb12 ha (ih (b - 3 + a) (by omega) (b - 3) a rfl (by omega) ha)
      rwa [Nat.mul_comm (F a + 1), min_comm a b, Nat.add_comm a b]
    exact lemD_base a (by omega) b (by omega) ha hb

/-- **Lemma D.** -/
theorem lemD (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (F a + 1) * (F b + 1) - pen (min a b) ≤ F (a + b) :=
  lemD_aux _ a b rfl ha hb

/-! ### Upper bound -/

theorem card_S_le (T : BTree) : (S T).card ≤ F T.leaves + 1 := by
  induction T with
  | leaf => simp [S_leaf, leaves, F]
  | node l r ihl ihr =>
    rw [card_S_node]
    have h1 := card_image₂_S_add_pen l r
    have h2 : (S l).card * (S r).card ≤ (F l.leaves + 1) * (F r.leaves + 1) :=
      Nat.mul_le_mul ihl ihr
    have h3 := lemD l.leaves r.leaves (leaves_pos l) (leaves_pos r)
    simp only [leaves]
    omega

/-! ### Lower bound -/

theorem card_S_cherry : (S cherry).card = 2 := by decide
theorem card_S_c3 : (S c3).card = 3 := by decide

theorem card_S_node_cherry (X : BTree) : 2 * (S X).card ≤ (S (node cherry X)).card := by
  rw [card_S_node]
  have := card_image₂_ge (S cherry) (S X)
  rw [card_S_cherry, show (2 : ℕ).choose 2 = 1 by decide] at this
  omega

theorem card_S_node_c3 (X : BTree) : 3 * (S X).card ≤ (S (node c3 X)).card + 2 := by
  rw [card_S_node]
  have := card_image₂_ge (S c3) (S X)
  rw [card_S_c3, show (3 : ℕ).choose 2 = 3 by decide] at this
  omega

theorem exists_card_S_ge : ∀ n, 1 ≤ n → ∃ T : BTree, T.leaves = n ∧ F n + 1 ≤ (S T).card := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases (show n = 1 ∨ n = 2 ∨ n = 3 ∨ ((4 ≤ n ∧ n ≤ 9) ∨ n = 11) ∨ (n = 10 ∨ 12 ≤ n) by
      omega) with h | h | h | h | h
    · subst h; exact ⟨leaf, rfl, by decide⟩
    · subst h; exact ⟨cherry, rfl, by rw [card_S_cherry]; decide⟩
    · subst h; exact ⟨c3, rfl, by rw [card_S_c3]; decide⟩
    · obtain ⟨T, hT, hc⟩ := ih (n - 2) (by omega) (by omega)
      refine ⟨node cherry T, ?_, ?_⟩
      · simp only [leaves, hT, cherry]; omega
      · have h1 := card_S_node_cherry T
        have h2 : F n = 2 * F (n - 2) + 1 := by
          rcases h with ⟨h3, h4⟩ | h
          · interval_cases n <;> decide
          · subst h; decide
        omega
    · obtain ⟨T, hT, hc⟩ := ih (n - 3) (by omega) (by omega)
      refine ⟨node c3 T, ?_, ?_⟩
      · simp only [leaves, hT, c3, cherry]; omega
      · have h1 := card_S_node_c3 T
        have h2 : F n = 3 * F (n - 3) := by
          rcases h with h | h
          · subst h; decide
          · exact F_rec3 n h
        omega

end BTree

/-- **Disanto–Rosenberg conjecture.** For `n ≥ 2`, `drMax n` is the maximum number of
non-equivalent root ancestral configurations over trees with `n` leaves. -/
theorem disanto_rosenberg (n : ℕ) (hn : 2 ≤ n) :
    IsGreatest {k | ∃ T : BTree, T.leaves = n ∧ T.rootConfigs = k} (drMax n) := by
  have hF : BTree.F n = drMax n := by unfold BTree.F; rw [if_neg (by omega)]
  constructor
  · obtain ⟨T, hT, hc⟩ := BTree.exists_card_S_ge n (by omega)
    refine ⟨T, hT, ?_⟩
    have hu := BTree.card_S_le T
    rw [hT] at hu
    rw [BTree.rootConfigs_eq_card_erase, Finset.card_erase_of_mem (BTree.leaf_mem_S T)]
    omega
  · rintro k ⟨T, hT, rfl⟩
    have hu := BTree.card_S_le T
    rw [hT] at hu
    rw [BTree.rootConfigs_eq_card_erase, Finset.card_erase_of_mem (BTree.leaf_mem_S T)]
    omega


/-! ## Extras (not needed for `disanto_rosenberg`)

* `disanto_rosenberg_min`: the minimum over trees with `n ≥ 1` leaves is `n - 1`, attained by
  the caterpillar.
* `disanto_rosenberg_unique`, `disanto_rosenberg_unique_shape`: for `n ≥ 9` the maximizing shape
  is unique.
-/

namespace BTree

/-! ### Minimum -/

theorem leaves_cnode (x y : BTree) : (cnode x y).leaves = x.leaves + y.leaves := by
  unfold cnode; split <;> simp [leaves, Nat.add_comm]

theorem leaves_canon (x : BTree) : (canon x).leaves = x.leaves := by
  induction x with
  | leaf => rfl
  | node l r ihl ihr => simp only [canon, leaves_cnode, ihl, ihr, leaves]

theorem exists_pruning_leaves (T : BTree) :
    ∀ k, 1 ≤ k → k ≤ T.leaves → ∃ P ∈ T.prunings, P.leaves = k := by
  induction T with
  | leaf =>
    intro k hk1 hk2
    simp only [leaves] at hk2
    exact ⟨leaf, by simp [prunings], by simp only [leaves]; omega⟩
  | node l r ihl ihr =>
    intro k hk1 hk2
    simp only [leaves] at hk2
    by_cases hk : k = 1
    · exact ⟨leaf, by simp [prunings], by simp [leaves, hk]⟩
    · have hl := leaves_pos l
      have hr := leaves_pos r
      obtain ⟨P, hP, hPk⟩ := ihl (min (k - 1) l.leaves) (by omega) (by omega)
      obtain ⟨Q, hQ, hQk⟩ := ihr (k - min (k - 1) l.leaves) (by omega) (by omega)
      refine ⟨node P Q, ?_, ?_⟩
      · simp only [prunings]
        exact Finset.mem_insert_of_mem
          (Finset.mem_image.2 ⟨(P, Q), Finset.mem_product.2 ⟨hP, hQ⟩, rfl⟩)
      · simp only [leaves, hPk, hQk]; omega

theorem leaves_le_card_S (T : BTree) : T.leaves ≤ (S T).card := by
  have h : Finset.Icc 1 T.leaves ⊆ (S T).image leaves := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    obtain ⟨P, hP, rfl⟩ := exists_pruning_leaves T k hk.1 hk.2
    exact Finset.mem_image.2 ⟨canon P, Finset.mem_image.2 ⟨P, hP, rfl⟩, leaves_canon P⟩
  have := (Finset.card_le_card h).trans Finset.card_image_le
  simpa using this

/-- Every tree with `n` leaves has at least `n - 1` non-equivalent root configurations. -/
theorem leaves_sub_one_le_rootConfigs (T : BTree) : T.leaves - 1 ≤ T.rootConfigs := by
  have := leaves_le_card_S T
  rw [rootConfigs_eq_card_erase, Finset.card_erase_of_mem (leaf_mem_S T)]
  omega

/-- The caterpillar with `n + 1` leaves. -/
def caterpillar : ℕ → BTree
  | 0 => leaf
  | n + 1 => node leaf (caterpillar n)

theorem caterpillar_leaves (n : ℕ) : (caterpillar n).leaves = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [caterpillar, leaves, ih]; omega

theorem card_S_caterpillar (n : ℕ) : (S (caterpillar n)).card = n + 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [caterpillar, card_S_node, S_leaf,
      Finset.card_image₂_singleton_left _ (cnode_injective leaf), ih]

/-- The caterpillar with `n + 1` leaves has exactly `n` non-equivalent root configurations. -/
theorem rootConfigs_caterpillar (n : ℕ) : (caterpillar n).rootConfigs = n := by
  rw [rootConfigs_eq_card_erase, Finset.card_erase_of_mem (leaf_mem_S _), card_S_caterpillar]
  rfl

/-! ### Uniqueness of the maximizer for `n ≥ 9` -/

/-- `T` is a maximizer with `n` leaves. -/
def IsMax (n : ℕ) (T : BTree) : Prop := T.leaves = n ∧ (S T).card = F n + 1

/-- Equality in Lemma D. -/
def Deq (a b : ℕ) : Prop := (F a + 1) * (F b + 1) - pen (min a b) = F (a + b)

instance (a b : ℕ) : Decidable (Deq a b) := inferInstanceAs (Decidable (_ = _))

theorem card_S_pos (T : BTree) : 1 ≤ (S T).card := Finset.card_pos.2 ⟨leaf, leaf_mem_S T⟩

theorem IsMax.node' {l r : BTree} {n : ℕ} (h : IsMax n (node l r)) :
    IsMax l.leaves l ∧ IsMax r.leaves r ∧ Deq l.leaves r.leaves := by
  obtain ⟨hn, hc⟩ := h
  simp only [leaves] at hn
  subst hn
  rw [card_S_node] at hc
  have h1 := card_image₂_S_add_pen l r
  have hl := card_S_le l
  have hr := card_S_le r
  have h2 : (S l).card * (S r).card ≤ (F l.leaves + 1) * (F r.leaves + 1) :=
    Nat.mul_le_mul hl hr
  have h3 := lemD l.leaves r.leaves (leaves_pos l) (leaves_pos r)
  have hr0 := card_S_pos r
  have heq : (S l).card * (S r).card = (F l.leaves + 1) * (F r.leaves + 1) := by omega
  have e1 : (S l).card = F l.leaves + 1 := by
    by_contra hne
    have h4 : (S l).card * (S r).card < (F l.leaves + 1) * (S r).card :=
      Nat.mul_lt_mul_of_pos_right (lt_of_le_of_ne hl hne) hr0
    have h5 : (F l.leaves + 1) * (S r).card ≤ (F l.leaves + 1) * (F r.leaves + 1) :=
      Nat.mul_le_mul_left _ hr
    omega
  have e2 : (S r).card = F r.leaves + 1 := by
    rw [e1] at heq
    exact Nat.eq_of_mul_eq_mul_left (by omega) heq
  refine ⟨⟨rfl, e1⟩, ⟨rfl, e2⟩, ?_⟩
  unfold Deq
  omega

theorem eq_leaf_of_leaves {T : BTree} (h : T.leaves = 1) : T = leaf := by
  cases T with
  | leaf => rfl
  | node l r =>
    have := leaves_pos l
    have := leaves_pos r
    simp only [leaves] at h
    omega

theorem canon_of_leaves_two {T : BTree} (h : T.leaves = 2) : canon T = cherry := by
  cases T with
  | leaf => simp [leaves] at h
  | node l r =>
    have := leaves_pos l
    have := leaves_pos r
    simp only [leaves] at h
    obtain rfl := eq_leaf_of_leaves (show l.leaves = 1 by omega)
    obtain rfl := eq_leaf_of_leaves (show r.leaves = 1 by omega)
    exact cnode_leaf_leaf

theorem canon_of_leaves_three {T : BTree} (h : T.leaves = 3) : canon T = c3 := by
  cases T with
  | leaf => simp [leaves] at h
  | node l r =>
    have := leaves_pos l
    have := leaves_pos r
    simp only [leaves] at h
    simp only [canon]
    rcases (show l.leaves = 1 ∧ r.leaves = 2 ∨ l.leaves = 2 ∧ r.leaves = 1 by omega) with
      ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain rfl := eq_leaf_of_leaves h1
      rw [canon_of_leaves_two h2]
      exact cnode_leaf_cherry
    · obtain rfl := eq_leaf_of_leaves h2
      rw [canon_of_leaves_two h1]
      exact cnode_cherry_leaf

/-- The 4-leaf tree made of two cherries. -/
def cc : BTree := node cherry cherry

theorem cnode_cherry_cherry : cnode cherry cherry = cc := by decide

theorem cc_mem_S {l r : BTree} (hl : 2 ≤ l.leaves) (hr : 2 ≤ r.leaves) : cc ∈ S (node l r) := by
  rw [S_node, ← cnode_cherry_cherry]
  exact Finset.mem_insert_of_mem (Finset.mem_image₂_of_mem (cherry_mem_S hl) (cherry_mem_S hr))

theorem card_image₂_add_six {A B : Finset BTree} (hA : leaf ∈ A ∧ cherry ∈ A ∧ c3 ∈ A ∧ cc ∈ A)
    (hB : leaf ∈ B ∧ cherry ∈ B ∧ c3 ∈ B ∧ cc ∈ B) :
    (Finset.image₂ cnode A B).card + 6 ≤ A.card * B.card := by
  obtain ⟨a1, a2, a3, a4⟩ := hA
  obtain ⟨b1, b2, b3, b4⟩ := hB
  have := card_image₂_add_le A B
    {(cherry, leaf), (c3, leaf), (c3, cherry), (cc, leaf), (cc, cherry), (cc, c3)}
    (by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.mem_product]
      exact ⟨⟨a2, b1⟩, ⟨a3, b1⟩, ⟨a3, b2⟩, ⟨a4, b1⟩, ⟨a4, b2⟩, ⟨a4, b3⟩⟩)
    (by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨Finset.mem_product.2 ⟨a1, b2⟩, by decide⟩
      · exact ⟨Finset.mem_product.2 ⟨a1, b3⟩, by decide⟩
      · exact ⟨Finset.mem_product.2 ⟨a2, b3⟩, by decide⟩
      · exact ⟨Finset.mem_product.2 ⟨a1, b4⟩, by decide⟩
      · exact ⟨Finset.mem_product.2 ⟨a2, b4⟩, by decide⟩
      · exact ⟨Finset.mem_product.2 ⟨a3, b4⟩, by decide⟩)
  have hcard : ({(cherry, leaf), (c3, leaf), (c3, cherry), (cc, leaf), (cc, cherry), (cc, c3)} :
      Finset (BTree × BTree)).card = 6 := by decide
  omega

/-- A maximizer cannot have two children that both contain the shapes `leaf, cherry, c3, cc`. -/
theorem IsMax.not_both_cc {l r : BTree} {n : ℕ} (h : IsMax n (node l r))
    (hl : 3 ≤ l.leaves) (hr : 3 ≤ r.leaves) (hlc : cc ∈ S l) (hrc : cc ∈ S r) : False := by
  obtain ⟨⟨_, hl'⟩, ⟨_, hr'⟩, hd⟩ := h.node'
  obtain ⟨hn, hc⟩ := h
  have h6 := card_image₂_add_six ⟨leaf_mem_S l, cherry_mem_S (by omega), c3_mem_S hl, hlc⟩
    ⟨leaf_mem_S r, cherry_mem_S (by omega), c3_mem_S hr, hrc⟩
  simp only [leaves] at hn
  subst hn
  rw [card_S_node] at hc
  unfold Deq at hd
  have hp : pen (min l.leaves r.leaves) = 3 := by unfold pen; split_ifs <;> omega
  rw [hp] at hd
  rw [hl', hr'] at h6
  omega

theorem F_ge_three (n : ℕ) (h : 4 ≤ n) : 3 ≤ F n := by
  by_cases h6 : n ≤ 5
  · interval_cases n <;> decide
  · unfold F drMax
    rw [if_neg (by omega)]
    apply (Nat.le_div_iff_mul_le (by norm_num)).2
    have h1 : 9 ≤ 3 ^ (n / 3) := by
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ (n / 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 23 ≤ 2 * (n % 3) ^ 2 + 8 * (n % 3) + 23 := by omega
    have := Nat.mul_le_mul h1 h2
    omega

theorem pen_lt (a b : ℕ) (hb : 1 ≤ b) (hb3 : b ≠ 3) : pen (min a b) < F b + 1 := by
  by_cases h4 : 4 ≤ b
  · have := F_ge_three b h4
    unfold pen; split_ifs <;> omega
  · have hF2 : F 2 = 1 := by decide
    rcases (show b = 1 ∨ b = 2 by omega) with rfl | rfl
    · unfold pen; split_ifs <;> omega
    · unfold pen; split_ifs <;> omega

theorem step_arith_strict (x y c z : ℕ) (hc : c < y) (ih : (x + 1) * y - c ≤ z) :
    (3 * x + 1) * y - c < 3 * z := by
  have h1 : (3 * x + 1) * y = 3 * (x * y) + y := by ring
  have h2 : (x + 1) * y = x * y + y := by ring
  rw [h1]
  rw [h2] at ih
  omega

theorem lemD_step_strict (a b : ℕ) (ha : 12 ≤ a) (hb : 1 ≤ b) (hb3 : b ≠ 3) :
    (F a + 1) * (F b + 1) - pen (min a b) < F (a + b) := by
  have ih := lemD (a - 3) b (by omega) hb
  have e1 : F a = 3 * F (a - 3) := F_rec3 a ha
  have e2 : F (a + b) = 3 * F (a - 3 + b) := by
    rw [F_rec3 (a + b) (by omega), show a + b - 3 = a - 3 + b by omega]
  have e3 : pen (min a b) = pen (min (a - 3) b) := by
    unfold pen; split_ifs <;> omega
  have hc : pen (min a b) < F b + 1 := pen_lt a b hb hb3
  rw [e1, e2, e3]
  rw [e3] at hc
  exact step_arith_strict _ _ _ _ hc ih

theorem lemD_strict_base : ∀ a < 12, ∀ b < 12, (1 ≤ a ∧ 1 ≤ b ∧ a ≠ 3 ∧ b ≠ 3 ∧ 15 ≤ a + b) →
    (F a + 1) * (F b + 1) - pen (min a b) < F (a + b) := by
  decide

/-- Strict form of Lemma D: for `a + b ≥ 15` equality forces `a = 3` or `b = 3`. -/
theorem lemD_strict (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (ha3 : a ≠ 3) (hb3 : b ≠ 3)
    (hab : 15 ≤ a + b) : (F a + 1) * (F b + 1) - pen (min a b) < F (a + b) := by
  by_cases ha12 : 12 ≤ a
  · exact lemD_step_strict a b ha12 hb hb3
  by_cases hb12 : 12 ≤ b
  · have := lemD_step_strict b a hb12 ha ha3
    rwa [Nat.mul_comm (F a + 1), min_comm a b, Nat.add_comm a b]
  exact lemD_strict_base a (by omega) b (by omega) ⟨ha, hb, ha3, hb3, hab⟩

theorem Deq_comm {a b : ℕ} (h : Deq a b) : Deq b a := by
  unfold Deq at *
  rwa [Nat.mul_comm (F b + 1), min_comm b a, Nat.add_comm b a]

theorem Deq_large {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : 15 ≤ a + b) (h : Deq a b) :
    a = 3 ∨ b = 3 := by
  by_cases ha3 : a = 3
  · exact Or.inl ha3
  by_cases hb3 : b = 3
  · exact Or.inr hb3
  have := lemD_strict a b ha hb ha3 hb3 hab
  unfold Deq at h
  omega

set_option synthInstance.maxSize 4096 in
/-- The equality cases of Lemma D with `5 ≤ a + b ≤ 14` that matter below. -/
theorem Deq_small : ∀ a < 15, ∀ b < 15, (1 ≤ a ∧ a ≤ b ∧ Deq a b) →
    (a + b = 5 → a = 2) ∧ (a + b = 7 → a = 2) ∧ (a + b = 9 → a = 2) ∧
    (a + b = 10 → a = 3 ∨ a = 5) ∧ (a + b = 11 → a = 2) ∧ (a + b = 12 → a = 3 ∨ a = 5) ∧
    (a + b = 13 → a = 3) ∧ (a + b = 14 → a = 3 ∨ a = 5 ∨ a = 7) := by
  decide

/-- Splitting a maximizer at the root, smaller child first. -/
theorem IsMax.split {n : ℕ} {T : BTree} (h : IsMax n T) (hn : 2 ≤ n) :
    ∃ l r : BTree, (IsMax n (node l r) ∨ IsMax n (node r l)) ∧
      canon T = cnode (canon l) (canon r) ∧ l.leaves ≤ r.leaves ∧ l.leaves + r.leaves = n ∧
      IsMax l.leaves l ∧ IsMax r.leaves r ∧ Deq l.leaves r.leaves := by
  cases T with
  | leaf => exact absurd h.1 (by simp only [leaves]; omega)
  | node l r =>
    have hn' := h.1
    simp only [leaves] at hn'
    obtain ⟨hl, hr, hd⟩ := h.node'
    by_cases hlr : l.leaves ≤ r.leaves
    · exact ⟨l, r, Or.inl h, rfl, hlr, hn', hl, hr, hd⟩
    · exact ⟨r, l, Or.inr h, cnode_comm _ _, by omega, by omega, hr, hl, Deq_comm hd⟩

/-- Maximizers with 5, 7 or 9 leaves contain the shape `cc`. -/
theorem IsMax.cc_mem {n : ℕ} {T : BTree} (h : IsMax n T) (hn : n = 5 ∨ n = 7 ∨ n = 9) :
    cc ∈ S T := by
  cases T with
  | leaf => exact absurd h.1 (by simp only [leaves]; omega)
  | node l r =>
    obtain ⟨-, -, hd⟩ := h.node'
    have hsum := h.1
    simp only [leaves] at hsum
    have hl1 := leaves_pos l
    have hr1 := leaves_pos r
    apply cc_mem_S
    · by_cases hlr : l.leaves ≤ r.leaves
      · have := Deq_small l.leaves (by omega) r.leaves (by omega) ⟨hl1, hlr, hd⟩
        omega
      · have := Deq_small r.leaves (by omega) l.leaves (by omega) ⟨hr1, by omega, Deq_comm hd⟩
        omega
    · by_cases hlr : l.leaves ≤ r.leaves
      · have := Deq_small l.leaves (by omega) r.leaves (by omega) ⟨hl1, hlr, hd⟩
        omega
      · have := Deq_small r.leaves (by omega) l.leaves (by omega) ⟨hr1, by omega, Deq_comm hd⟩
        omega

/-- All maximizers with `n` leaves have the same shape. -/
def Uniq (n : ℕ) : Prop := ∀ T T' : BTree, IsMax n T → IsMax n T' → canon T = canon T'

theorem uniq_two : Uniq 2 := fun _ _ hT hT' => by
  rw [canon_of_leaves_two hT.1, canon_of_leaves_two hT'.1]

theorem uniq_three : Uniq 3 := fun _ _ hT hT' => by
  rw [canon_of_leaves_three hT.1, canon_of_leaves_three hT'.1]

/-- If the smaller child of every maximizer with `n` leaves has exactly `a` leaves, uniqueness
for `a` and `n - a` gives uniqueness for `n`. -/
theorem uniq_step (n a : ℕ) (hn : 2 ≤ n) (h1 : Uniq a) (h2 : Uniq (n - a))
    (hmin : ∀ l r : BTree, (IsMax n (node l r) ∨ IsMax n (node r l)) → l.leaves ≤ r.leaves →
      l.leaves + r.leaves = n → IsMax l.leaves l → IsMax r.leaves r → Deq l.leaves r.leaves →
      l.leaves = a) :
    Uniq n := by
  have key : ∀ T, IsMax n T → ∃ l r : BTree,
      canon T = cnode (canon l) (canon r) ∧ IsMax a l ∧ IsMax (n - a) r := by
    intro T hT
    obtain ⟨l, r, hTlr, hc, hle, hsum, hl, hr, hd⟩ := hT.split hn
    have ha : l.leaves = a := hmin l r hTlr hle hsum hl hr hd
    have hb : r.leaves = n - a := by omega
    refine ⟨l, r, hc, ?_, ?_⟩
    · rw [← ha]; exact hl
    · rw [← hb]; exact hr
  intro T T' hT hT'
  obtain ⟨l, r, hc, hl, hr⟩ := key T hT
  obtain ⟨l', r', hc', hl', hr'⟩ := key T' hT'
  rw [hc, hc', h1 l l' hl hl', h2 r r' hr hr']

/-- The excluded equality cases `(5,5), (5,7), (5,9), (7,7)`. -/
theorem not_bad {n : ℕ} {l r : BTree} (hT : IsMax n (node l r) ∨ IsMax n (node r l))
    (hl : IsMax l.leaves l) (hr : IsMax r.leaves r)
    (hl' : l.leaves = 5 ∨ l.leaves = 7 ∨ l.leaves = 9)
    (hr' : r.leaves = 5 ∨ r.leaves = 7 ∨ r.leaves = 9) : False := by
  have hlc := hl.cc_mem hl'
  have hrc := hr.cc_mem hr'
  rcases hT with hT | hT
  · exact hT.not_both_cc (by omega) (by omega) hlc hrc
  · exact hT.not_both_cc (by omega) (by omega) hrc hlc

theorem uniq_all : ∀ n, (n = 2 ∨ n = 3 ∨ n = 5 ∨ n = 7 ∨ 9 ≤ n) → Uniq n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    -- the smaller child of a maximizer: `Deq_small` / `Deq_large` and `not_bad`
    have hsmall : ∀ l r : BTree, l.leaves ≤ r.leaves → l.leaves + r.leaves = n →
        Deq l.leaves r.leaves → n < 15 →
        (n = 5 → l.leaves = 2) ∧ (n = 7 → l.leaves = 2) ∧ (n = 9 → l.leaves = 2) ∧
        (n = 10 → l.leaves = 3 ∨ l.leaves = 5) ∧ (n = 11 → l.leaves = 2) ∧
        (n = 12 → l.leaves = 3 ∨ l.leaves = 5) ∧ (n = 13 → l.leaves = 3) ∧
        (n = 14 → l.leaves = 3 ∨ l.leaves = 5 ∨ l.leaves = 7) := by
      intro l r hle hsum hd hn15
      have := Deq_small l.leaves (by omega) r.leaves (by omega) ⟨leaves_pos l, hle, hd⟩
      rw [hsum] at this
      exact this
    rcases hn with rfl | rfl | rfl | rfl | hn9
    · exact uniq_two
    · exact uniq_three
    · refine uniq_step 5 2 (by omega) uniq_two uniq_three ?_
      intro l r _ hle hsum _ _ hd
      exact (hsmall l r hle hsum hd (by omega)).1 rfl
    · refine uniq_step 7 2 (by omega) uniq_two (ih 5 (by omega) (by omega)) ?_
      intro l r _ hle hsum _ _ hd
      exact (hsmall l r hle hsum hd (by omega)).2.1 rfl
    · by_cases h15 : 15 ≤ n
      · refine uniq_step n 3 (by omega) uniq_three (ih (n - 3) (by omega) (by omega)) ?_
        intro l r _ hle hsum _ _ hd
        rcases Deq_large (leaves_pos l) (leaves_pos r) (by omega) hd with h | h
        · exact h
        · omega
      · have hs := fun l r hle hsum hd => hsmall l r hle hsum hd (by omega)
        rcases (show n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 by omega) with
          rfl | rfl | rfl | rfl | rfl | rfl
        · refine uniq_step 9 2 (by omega) uniq_two (ih 7 (by omega) (by omega)) ?_
          intro l r _ hle hsum _ _ hd
          exact (hs l r hle hsum hd).2.2.1 rfl
        · refine uniq_step 10 3 (by omega) uniq_three (ih 7 (by omega) (by omega)) ?_
          intro l r hT hle hsum hl hr hd
          rcases (hs l r hle hsum hd).2.2.2.1 rfl with h | h
          · exact h
          · exact (not_bad hT hl hr (by omega) (by omega)).elim
        · refine uniq_step 11 2 (by omega) uniq_two (ih 9 (by omega) (by omega)) ?_
          intro l r _ hle hsum _ _ hd
          exact (hs l r hle hsum hd).2.2.2.2.1 rfl
        · refine uniq_step 12 3 (by omega) uniq_three (ih 9 (by omega) (by omega)) ?_
          intro l r hT hle hsum hl hr hd
          rcases (hs l r hle hsum hd).2.2.2.2.2.1 rfl with h | h
          · exact h
          · exact (not_bad hT hl hr (by omega) (by omega)).elim
        · refine uniq_step 13 3 (by omega) uniq_three (ih 10 (by omega) (by omega)) ?_
          intro l r _ hle hsum _ _ hd
          exact (hs l r hle hsum hd).2.2.2.2.2.2.1 rfl
        · refine uniq_step 14 3 (by omega) uniq_three (ih 11 (by omega) (by omega)) ?_
          intro l r hT hle hsum hl hr hd
          rcases (hs l r hle hsum hd).2.2.2.2.2.2.2 rfl with h | h | h
          · exact h
          · exact (not_bad hT hl hr (by omega) (by omega)).elim
          · exact (not_bad hT hl hr (by omega) (by omega)).elim

end BTree

/-- **Minimum.** For `n ≥ 1`, the minimum number of non-equivalent root ancestral configurations
over trees with `n` leaves is `n - 1` (attained by the caterpillar). -/
theorem disanto_rosenberg_min (n : ℕ) (hn : 1 ≤ n) :
    IsLeast {k | ∃ T : BTree, T.leaves = n ∧ T.rootConfigs = k} (n - 1) := by
  constructor
  · refine ⟨BTree.caterpillar (n - 1), ?_, BTree.rootConfigs_caterpillar (n - 1)⟩
    rw [BTree.caterpillar_leaves]
    omega
  · rintro k ⟨T, hT, rfl⟩
    have := BTree.leaves_sub_one_le_rootConfigs T
    omega

/-- **Uniqueness.** For `n ≥ 9`, any two trees with `n` leaves attaining the maximum `drMax n`
are isomorphic. -/
theorem disanto_rosenberg_unique (n : ℕ) (hn : 9 ≤ n) (T T' : BTree)
    (hT : T.leaves = n) (hT' : T'.leaves = n)
    (h : T.rootConfigs = drMax n) (h' : T'.rootConfigs = drMax n) : BTree.Iso T T' := by
  apply BTree.iso_of_canon_eq
  have hF : BTree.F n = drMax n := by unfold BTree.F; rw [if_neg (by omega)]
  refine BTree.uniq_all n (by omega) T T' ⟨hT, ?_⟩ ⟨hT', ?_⟩
  · rw [BTree.rootConfigs_eq_card_erase, Finset.card_erase_of_mem (BTree.leaf_mem_S T)] at h
    have := BTree.card_S_pos T
    omega
  · rw [BTree.rootConfigs_eq_card_erase, Finset.card_erase_of_mem (BTree.leaf_mem_S T')] at h'
    have := BTree.card_S_pos T'
    omega

/-- **Uniqueness**, phrased with shapes: for `n ≥ 9` exactly one shape with `n` leaves attains
the maximum. -/
theorem disanto_rosenberg_unique_shape (n : ℕ) (hn : 9 ≤ n) :
    ∃! s : Quotient BTree.shapeSetoid,
      ∃ T : BTree, Quotient.mk _ T = s ∧ T.leaves = n ∧ T.rootConfigs = drMax n := by
  obtain ⟨T, hT, hc⟩ := (disanto_rosenberg n (by omega)).1
  refine ⟨Quotient.mk _ T, ⟨T, rfl, hT, hc⟩, ?_⟩
  rintro s ⟨T', rfl, hT', hc'⟩
  exact Quotient.sound (Relation.EqvGen.rel _ _ (disanto_rosenberg_unique n hn T' T hT' hT hc' hc))

end KOS.AncestralConfigurationsIndependent
