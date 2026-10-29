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
    (n + k - 1) / k - 1 ≤ minForcingNumber G := by
  classical
  have interval_packing {α : Type _} [DecidableEq α]
      (E : Finset α) (l r : α → ℕ) (q : ℕ)
      (hlr : ∀ x ∈ E, l x ≤ r x)
      (hcover : ∀ t, (E.filter (fun x => l x ≤ t ∧ t ≤ r x)).card ≤ q) :
      ∃ T ⊆ E, E.card ≤ q * T.card ∧
        ∀ x ∈ T, ∀ y ∈ T, x ≠ y → r x < l y ∨ r y < l x := by
    classical
    induction E using Finset.strongInductionOn with
    | _ E ih =>
      by_cases hE : E.Nonempty
      · obtain ⟨e, he, hmin⟩ := E.exists_min_image r hE
        let U := E.filter (fun x => r e < l x)
        have hUE : U ⊆ E := Finset.filter_subset _ _
        have heU : e ∉ U := by simp [U, not_lt.mpr (hlr e he)]
        have hUs : U ⊂ E := Finset.ssubset_iff_subset_ne.mpr ⟨hUE, by
          intro h
          exact heU (h.symm ▸ he)⟩
        obtain ⟨T, hTU, hsize, hsep⟩ := ih U hUs
          (fun x hx => hlr x (hUE hx)) (fun t => le_trans
            (Finset.card_le_card (Finset.filter_subset_filter _ hUE)) (hcover t))
        have heT : e ∉ T := fun h => heU (hTU h)
        have hcount : E.card ≤ q + U.card := by
          have hc := hcover (r e)
          have hh : E.filter (fun x => l x ≤ r e ∧ r e ≤ r x) =
              E.filter (fun x => l x ≤ r e) := by
            ext x
            simp only [Finset.mem_filter]
            constructor
            · tauto
            · intro hx
              exact ⟨hx.1, hx.2, hmin x hx.1⟩
          rw [hh] at hc
          have hs := Finset.card_filter_add_card_filter_not
            (s := E) (p := fun x => l x ≤ r e)
          have hu : E.filter (fun x => ¬ l x ≤ r e) = U := by
            ext x
            simp [U]
          rw [hu] at hs
          omega
        refine ⟨insert e T, Finset.insert_subset_iff.mpr ⟨he, hTU.trans hUE⟩, ?_, ?_⟩
        · rw [Finset.card_insert_of_notMem heT]
          nlinarith
        · intro x hx y hy hxy
          rcases Finset.mem_insert.mp hx with hxe | hxT
          · subst x
            left
            rcases Finset.mem_insert.mp hy with hye | hyT
            · exact (hxy hye.symm).elim
            · exact (Finset.mem_filter.mp (hTU hyT)).2
          · rcases Finset.mem_insert.mp hy with hye | hyT
            · subst y
              right
              exact (Finset.mem_filter.mp (hTU hxT)).2
            · exact hsep x hxT y hyT hxy
      · have : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hE
        subst E
        exact ⟨∅, by simp, by simp, by simp⟩

  have periodic_exists {α : Type _} [Finite α] (f : α → α) (a : α) :
      (Function.periodicPts f).Nonempty := by
    have aux {i j : ℕ} (hij : f^[i] a = f^[j] a) (hlt : i < j) :
        (Function.periodicPts f).Nonempty := by
      refine ⟨f^[i] a, Function.mk_mem_periodicPts (show 0 < j - i by omega) ?_⟩
      change f^[j-i] (f^[i] a) = f^[i] a
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hlt.le]
      exact hij.symm
    obtain ⟨i, j, hij, hne⟩ : ∃ i j, f^[i] a = f^[j] a ∧ i ≠ j := by
      simpa [Function.Injective] using
        (not_injective_infinite_finite (f^[·] a))
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact aux hij hlt
    · exact aux hij.symm hlt

  have wf_of_unique_perm {α : Type _} [Fintype α] [DecidableEq α]
      (R : α → α → Prop) (S : Finset α) (hrefl : ∀ x, R x x)
      (hu : ∀ p : Equiv.Perm α, (∀ x, R x (p x)) →
        (∀ x ∈ S, p x = x) → p = 1) :
      WellFounded (fun x y => x ∉ S ∧ y ∉ S ∧ x ≠ y ∧ R x y) := by
    classical
    rw [WellFounded.wellFounded_iff_has_min]
    intro T hT
    by_contra hn
    push Not at hn
    have hpre : ∀ x : T, ∃ y : T,
        y.val ∉ S ∧ x.val ∉ S ∧ y.val ≠ x.val ∧ R y.val x.val := by
      intro x
      obtain ⟨y, hy, hxy⟩ := hn x.val x.property
      exact ⟨⟨y, hy⟩, hxy⟩
    choose f hf using hpre
    let pp : Equiv.Perm (Function.periodicPts f) :=
      (Function.bijOn_periodicPts f).equiv f
    let pT : Equiv.Perm T := Equiv.Perm.ofSubtype pp
    let p : Equiv.Perm α := Equiv.Perm.ofSubtype pT
    have hp : ∀ x, p x = x ∨
        (p x ∉ S ∧ x ∉ S ∧ p x ≠ x ∧ R (p x) x) := by
      intro x
      by_cases hx : x ∈ T
      · by_cases hxper : (⟨x, hx⟩ : T) ∈ Function.periodicPts f
        · right
          have heq : p x = (f ⟨x, hx⟩).val := by
            simp only [p, Equiv.Perm.ofSubtype_apply_of_mem _ hx,
              pT, Equiv.Perm.ofSubtype_apply_of_mem _ hxper]
            rfl
          rw [heq]
          exact hf ⟨x, hx⟩
        · left
          simp [p, pT, Equiv.Perm.ofSubtype_apply_of_mem _ hx,
            Equiv.Perm.ofSubtype_apply_of_not_mem _ hxper]
      · left
        exact Equiv.Perm.ofSubtype_apply_of_not_mem _ hx
    have hpid : p.symm = 1 := hu p.symm (by
      intro x
      rcases hp (p.symm x) with hx | hx
      · have heq : x = p.symm x := by simpa using hx
        rw [← heq]
        exact hrefl x
      · simpa using hx.2.2.2) (by
      intro x hx
      have heq : p x = x := (hp x).resolve_right (fun h => h.2.1 hx)
      exact (p.symm_apply_eq).mpr heq.symm)
    obtain ⟨a, ha⟩ := hT
    obtain ⟨z, hz⟩ := periodic_exists f (⟨a, ha⟩ : T)
    have heq : p z.val = (f z).val := by
      simp only [p, Equiv.Perm.ofSubtype_apply_of_mem _ z.property,
        pT, Equiv.Perm.ofSubtype_apply_of_mem _ hz]
      rfl
    have hid : p = 1 := inv_eq_one.mp hpid
    have hneq := (hf z).2.2.1
    apply hneq
    simpa [hid] using heq.symm

  have rank_of_unique_perm {α : Type _} [Fintype α] [DecidableEq α]
      (R : α → α → Prop) (S : Finset α) (hrefl : ∀ x, R x x)
      (hu : ∀ p : Equiv.Perm α, (∀ x, R x (p x)) →
        (∀ x ∈ S, p x = x) → p = 1) :
      ∃ rank : α → ℕ, Function.Injective rank ∧
        (∀ x, rank x < Fintype.card α) ∧
        ∀ x y, x ∉ S → y ∉ S → R x y → rank x ≤ rank y := by
    classical
    let r := fun x y => x ∉ S ∧ y ∉ S ∧ x ≠ y ∧ R x y
    have hw : WellFounded r := wf_of_unique_perm R S hrefl hu
    letI : IsWellFounded α r := ⟨hw⟩
    letI : LinearOrder α := IsWellFounded.wellOrderExtension r
    let e := (Fintype.orderIsoFinOfCardEq α rfl).symm
    refine ⟨fun x => (e x).val, ?_, ?_, ?_⟩
    · exact fun x y h => e.injective (Fin.ext h)
    · intro x
      exact (e x).isLt
    · intro x y hx hy hxy
      by_cases heq : x = y
      · simp [heq]
      · have hr : r x y := ⟨hx, hy, heq, hxy⟩
        have hlt : x < y := Prod.Lex.left _ _ (IsWellFounded.rank_lt_of_rel hr)
        exact (e.monotone hlt.le)

  have interval_overlap {α : Type _} [Fintype α] [DecidableEq α]
      (S : Finset α) (p : Equiv.Perm α) (rank : α → ℕ)
      (hinj : Function.Injective rank) (N : ℕ)
      (l r : α → ℕ)
      (hl : ∀ x, l x = if x ∈ S then 0 else rank x + 1)
      (hr : ∀ x, r x = if p x ∈ S then N + 1 else rank (p x) + 1)
      (hlr : ∀ x, l x ≤ r x) :
      ∀ t, ((Finset.univ : Finset α).filter
        (fun x => l x ≤ t ∧ t ≤ r x)).card ≤ S.card + 1 := by
    classical
    intro t
    let L := (Finset.univ : Finset α).filter (fun x => l x ≤ t)
    let B := (Finset.univ : Finset α).filter (fun x => r x < t)
    let D := (Finset.univ : Finset α).filter (fun x => x ∉ S ∧ rank x + 1 ≤ t)
    let D₀ := (Finset.univ : Finset α).filter (fun x => x ∉ S ∧ rank x + 1 < t)
    let E := (Finset.univ : Finset α).filter (fun x => rank x + 1 = t)
    have hL : L = S ∪ D := by
      ext x
      by_cases hx : x ∈ S <;> simp [L, D, hl, hx]
    have hD : D ⊆ D₀ ∪ E := by
      intro x hx
      have h : x ∉ S ∧ rank x + 1 ≤ t := (Finset.mem_filter.mp hx).2
      apply Finset.mem_union.mpr
      rcases lt_or_eq_of_le h.2 with ht | ht
      · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.1, ht⟩)
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩)
    have hE : E.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro x hx y hy
      apply hinj
      have hx' := (Finset.mem_filter.mp hx).2
      have hy' := (Finset.mem_filter.mp hy).2
      omega
    have hD₀ : D₀.card ≤ B.card := by
      rw [← Finset.card_image_of_injective D₀ p.symm.injective]
      apply Finset.card_le_card
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      have hx' := (Finset.mem_filter.mp hx).2
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, hr,
        p.apply_symm_apply, if_neg hx'.1]
      exact hx'.2
    have hsize : L.card ≤ S.card + B.card + 1 := by
      have h₁ := Finset.card_le_card hD
      have h₂ := Finset.card_union_le D₀ E
      have h₃ := Finset.card_union_le S D
      rw [← hL] at h₃
      omega
    have hBL : B ⊆ L := by
      intro x hx
      have hx' := (Finset.mem_filter.mp hx).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_trans (hlr x) hx'.le⟩
    have hC : (Finset.univ.filter (fun x => l x ≤ t ∧ t ≤ r x)) = L \ B := by
      ext x
      simp [L, B, and_left_comm]
    rw [hC, Finset.card_sdiff_of_subset hBL]
    omega

  have permutation_bound {α : Type _} [Fintype α] [DecidableEq α]
      (R : α → α → Prop) (S : Finset α) (hrefl : ∀ x, R x x)
      (hu : ∀ p : Equiv.Perm α, (∀ x, R x (p x)) →
        (∀ x ∈ S, p x = x) → p = 1)
      (p : Equiv.Perm α) (hp : ∀ x, R x (p x)) :
      ∃ T : Finset α, Fintype.card α ≤ (S.card + 1) * T.card ∧
        ∀ q : Equiv.Perm α, (∀ x, R x (q x)) →
          (∀ x, x ∉ T → q x = p x) → q = p := by
    classical
    obtain ⟨rank, hinj, hbound, hrank⟩ := rank_of_unique_perm R S hrefl hu
    let N := Fintype.card α
    let l := fun x => if x ∈ S then 0 else rank x + 1
    let r := fun x => if p x ∈ S then N + 1 else rank (p x) + 1
    have hlbound : ∀ x, l x ≤ N := by
      intro x
      have := hbound x
      dsimp [l, N]
      split_ifs <;> omega
    have hlr : ∀ x, l x ≤ r x := by
      intro x
      by_cases hx : x ∈ S
      · simp [l, hx]
      · by_cases hpx : p x ∈ S
        · simp only [l, r, if_neg hx, if_pos hpx]
          have := hbound x
          omega
        · simp only [l, r, if_neg hx, if_neg hpx]
          exact Nat.add_le_add_right (hrank x (p x) hx hpx (hp x)) 1
    obtain ⟨T, _, hsize, hsep⟩ := interval_packing Finset.univ l r (S.card + 1)
      (fun x _ => hlr x)
      (interval_overlap S p rank hinj N l r (fun _ => rfl) (fun _ => rfl) hlr)
    refine ⟨T, by simpa using hsize, ?_⟩
    intro q hq hfix
    let σ := q.trans p.symm
    have hσ : ∀ x, p (σ x) = q x := fun x => p.apply_symm_apply (q x)
    have hσfix : ∀ x, x ∉ T → σ x = x := by
      intro x hx
      change p.symm (q x) = x
      rw [hfix x hx, p.symm_apply_apply]
    have hσT : ∀ x ∈ T, σ x ∈ T := by
      intro x hx
      by_contra hn
      have h := hσfix (σ x) hn
      have he : σ x = x := σ.injective h
      exact hn (he.symm ▸ hx)
    have hforward : ∀ x, l x ≤ l (σ x) := by
      intro x
      by_cases hx : x ∈ T
      · by_cases heq : x = σ x
        · rw [← heq]
        · rcases hsep x hx (σ x) (hσT x hx) heq with h | h
          · exact (hlr x).trans h.le
          · exfalso
            have hxS : x ∉ S := by
              intro hmem
              have : l x = 0 := by simp [l, hmem]
              omega
            have hpxS : p (σ x) ∉ S := by
              intro hmem
              have : r (σ x) = N + 1 := by simp [r, hmem]
              have := hlbound x
              omega
            have hxy := hrank x (p (σ x)) hxS hpxS (by rw [hσ]; exact hq x)
            simp only [l, r, if_neg hxS, if_neg hpxS] at h
            omega
      · rw [hσfix x hx]
    have heql : ∀ x, l x = l (σ x) := by
      have heq : (∑ x : α, l x) = ∑ x : α, l (σ x) := (Equiv.sum_comp σ l).symm
      exact fun x => (Finset.sum_eq_sum_iff_of_le (fun x _ => hforward x)).mp heq
        x (Finset.mem_univ x)
    have hid : ∀ x, σ x = x := by
      intro x
      by_cases hx : x ∈ T
      · by_contra hn
        have hsep' := hsep x hx (σ x) (hσT x hx) (Ne.symm hn)
        have h₁ := hlr x
        have h₂ := hlr (σ x)
        have h₃ := heql x
        omega
      · exact hσfix x hx
    apply Equiv.ext
    intro x
    simpa [hid] using (hσ x).symm

  let edgesOf (A : Set V) (p : A ≃ ↥(Aᶜ)) : Finset (Sym2 V) := by
    classical
    exact Finset.univ.image (fun a : A => s(a.val, (p a).val))

  have cross_eq (A : Set V) (a a' : A) (b b' : ↥(Aᶜ)) :
      s(a.val, b.val) = s(a'.val, b'.val) ↔ a = a' ∧ b = b' := by
    rw [Sym2.eq_iff]
    constructor
    · rintro (⟨h₁, h₂⟩ | ⟨h₁, _⟩)
      · exact ⟨Subtype.ext h₁, Subtype.ext h₂⟩
      · exact (b'.property (h₁ ▸ a.property)).elim
    · rintro ⟨rfl, rfl⟩
      exact Or.inl ⟨rfl, rfl⟩

  have edgeMap_injective (A : Set V) (p : A ≃ ↥(Aᶜ)) :
      Function.Injective (fun a : A => s(a.val, (p a).val)) := by
    intro a a' heq
    exact ((cross_eq A a a' (p a) (p a')).mp heq).1

  have mem_edgesOf (A : Set V) (p : A ≃ ↥(Aᶜ)) (a : A) (b : ↥(Aᶜ)) :
      s(a.val, b.val) ∈ edgesOf A p ↔ p a = b := by
    classical
    simp only [edgesOf, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a', h⟩
      obtain ⟨ha, hb⟩ := (cross_eq A a' a (p a') b).mp h
      subst a'
      exact hb
    · intro h
      exact ⟨a, by rw [h]⟩

  have edgesOf_injective (A : Set V) : Function.Injective (edgesOf A) := by
    intro p q hpq
    apply Equiv.ext
    intro a
    have h : s(a.val, (p a).val) ∈ edgesOf A q := by
      rw [← hpq, mem_edgesOf]
    exact ((mem_edgesOf A q a (p a)).mp h).symm

  have edgesOf_perfect (G : SimpleGraph V) (A : Set V) (p : A ≃ ↥(Aᶜ))
      (hp : ∀ a : A, G.Adj a.val (p a).val) : IsPerfectMatching G (edgesOf A p) := by
    classical
    constructor
    · intro e he
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp he
      exact hp a
    · intro v
      by_cases hv : v ∈ A
      · refine ⟨(p ⟨v, hv⟩).val, ?_, ?_⟩
        · exact (mem_edgesOf A p ⟨v, hv⟩ (p ⟨v, hv⟩)).mpr rfl
        · intro w hw
          obtain ⟨a, _, he⟩ := Finset.mem_image.mp hw
          rcases Sym2.eq_iff.mp he with h | h
          · have ha : a = ⟨v, hv⟩ := Subtype.ext h.1
            simpa [ha] using h.2.symm
          · exact ((p a).property (h.2.symm ▸ hv)).elim
      · refine ⟨(p.symm ⟨v, hv⟩).val, ?_, ?_⟩
        · change s(v, (p.symm ⟨v, hv⟩).val) ∈ edgesOf A p
          rw [Sym2.eq_swap]
          exact (mem_edgesOf A p (p.symm ⟨v, hv⟩) ⟨v, hv⟩).mpr (p.apply_symm_apply _)
        · intro w hw
          obtain ⟨a, _, he⟩ := Finset.mem_image.mp hw
          rcases Sym2.eq_iff.mp he with h | h
          · exact (hv (h.1 ▸ a.property)).elim
          · have hb : p a = ⟨v, hv⟩ := Subtype.ext h.2
            have ha : a = p.symm ⟨v, hv⟩ := (p.eq_symm_apply).mpr hb
            simpa [ha] using h.1.symm

  have matching_equiv (G : SimpleGraph V) (A : Set V)
      (hbi : ∀ v w, G.Adj v w → (v ∈ A ↔ w ∉ A))
      (M : Finset (Sym2 V)) (hM : IsPerfectMatching G M) :
      ∃ p : A ≃ ↥(Aᶜ), M = edgesOf A p ∧ ∀ a : A, G.Adj a.val (p a).val := by
    classical
    choose mate hm using hM.2
    have hadj : ∀ v, G.Adj v (mate v) := fun v => hM.1 _ (hm v).1
    have hmate : ∀ v, mate (mate v) = v := by
      intro v
      symm
      apply (hm (mate v)).2
      simpa only [Sym2.eq_swap] using (hm v).1
    let p : A ≃ ↥(Aᶜ) := {
      toFun := fun a => ⟨mate a.val, (hbi _ _ (hadj a.val)).mp a.property⟩
      invFun := fun b => ⟨mate b.val, (hbi _ _ (hadj b.val).symm).mpr b.property⟩
      left_inv := fun a => Subtype.ext (hmate a.val)
      right_inv := fun b => Subtype.ext (hmate b.val) }
    refine ⟨p, ?_, fun a => hadj a.val⟩
    ext e
    induction e using Sym2.inductionOn with
    | hf v w =>
      constructor
      · intro he
        have hGvw : G.Adj v w := hM.1 _ he
        by_cases hv : v ∈ A
        · have hw : w ∉ A := (hbi _ _ hGvw).mp hv
          apply (mem_edgesOf A p ⟨v, hv⟩ ⟨w, hw⟩).mpr
          apply Subtype.ext
          exact ((hm v).2 w he).symm
        · have hw : w ∈ A := (hbi _ _ hGvw.symm).mpr hv
          rw [Sym2.eq_swap]
          apply (mem_edgesOf A p ⟨w, hw⟩ ⟨v, hv⟩).mpr
          apply Subtype.ext
          apply Eq.symm
          apply (hm w).2 v
          simpa only [Sym2.eq_swap] using he
      · intro he
        obtain ⟨a, _, ha⟩ := Finset.mem_image.mp he
        rw [← ha]
        exact (hm a.val).1

  have graph_bound (G : SimpleGraph V) (A : Set V) [DecidablePred (· ∈ A)]
      (hbi : ∀ v w, G.Adj v w → (v ∈ A ↔ w ∉ A))
      (M₀ S M : Finset (Sym2 V))
      (hM₀ : IsPerfectMatching G M₀) (hS : IsForcingSet G M₀ S)
      (hM : IsPerfectMatching G M) :
      ∃ S₁, IsForcingSet G M S₁ ∧
        Fintype.card A ≤ (S.card + 1) * (Fintype.card A - S₁.card) := by
    classical
    obtain ⟨p₀, hp₀, hadj₀⟩ := matching_equiv G A hbi M₀ hM₀
    obtain ⟨p, hp, hadj⟩ := matching_equiv G A hbi M hM
    let SA := Finset.univ.filter (fun a : A => s(a.val, (p₀ a).val) ∈ S)
    have hSA : SA.image (fun a : A => s(a.val, (p₀ a).val)) = S := by
      apply Finset.Subset.antisymm
      · intro e he
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
        exact (Finset.mem_filter.mp ha).2
      · intro e he
        have heM := hS.1 he
        rw [hp₀] at heM
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp heM
        apply Finset.mem_image.mpr
        exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩, rfl⟩
    have hSAcard : SA.card = S.card := by
      rw [← hSA, Finset.card_image_of_injective _ (edgeMap_injective A p₀)]
    let R := fun x y : A => G.Adj x.val (p₀ y).val
    have hR : ∀ x, R x x := hadj₀
    have huniq : ∀ σ : Equiv.Perm A, (∀ x, R x (σ x)) →
        (∀ x ∈ SA, σ x = x) → σ = 1 := by
      intro σ hσ hσS
      have hpm : IsPerfectMatching G (edgesOf A (σ.trans p₀)) :=
        edgesOf_perfect G A (σ.trans p₀) hσ
      have hsub : S ⊆ edgesOf A (σ.trans p₀) := by
        rw [← hSA]
        intro e he
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
        apply (mem_edgesOf A (σ.trans p₀) a (p₀ a)).mpr
        change p₀ (σ a) = p₀ a
        rw [hσS a ha]
      have heq := hS.2 _ hpm hsub
      rw [hp₀] at heq
      have hpeq := edgesOf_injective A heq
      apply Equiv.ext
      intro a
      apply p₀.injective
      exact congrArg (fun e : A ≃ ↥(Aᶜ) => e a) hpeq
    let π : Equiv.Perm A := p.trans p₀.symm
    have hπ : ∀ x, R x (π x) := by
      intro x
      change G.Adj x.val (p₀ (p₀.symm (p x))).val
      simpa using hadj x
    obtain ⟨T, hsize, hT⟩ := permutation_bound R SA hR huniq π hπ
    let S₁ := Tᶜ.image (fun a : A => s(a.val, (p a).val))
    have hforce : IsForcingSet G M S₁ := by
      constructor
      · rw [hp]
        intro e he
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp he
        exact (mem_edgesOf A p a (p a)).mpr rfl
      · intro N hN hSN
        obtain ⟨q, hq, hadjq⟩ := matching_equiv G A hbi N hN
        have hqvalid : ∀ x, R x ((q.trans p₀.symm) x) := by
          intro x
          change G.Adj x.val (p₀ (p₀.symm (q x))).val
          simpa using hadjq x
        have hfix : ∀ x, x ∉ T → (q.trans p₀.symm) x = π x := by
          intro x hx
          have he : s(x.val, (p x).val) ∈ S₁ :=
            Finset.mem_image.mpr ⟨x, Finset.mem_compl.mpr hx, rfl⟩
          have heN := hSN he
          rw [hq, mem_edgesOf] at heN
          change p₀.symm (q x) = p₀.symm (p x)
          rw [heN]
        have heqp := hT (q.trans p₀.symm) hqvalid hfix
        have heq : q = p := by
          apply Equiv.ext
          intro x
          apply p₀.symm.injective
          exact congrArg (fun e : Equiv.Perm A => e x) heqp
        rw [hq, hp, heq]
    have hcard : S₁.card = Fintype.card A - T.card := by
      rw [Finset.card_image_of_injective _ (edgeMap_injective A p), Finset.card_compl]
    refine ⟨S₁, hforce, ?_⟩
    have hTcard : T.card ≤ Fintype.card A := Finset.card_le_univ _
    rw [hcard, Nat.sub_sub_self hTcard, ← hSAcard]
    exact hsize

  have perfect_subset_eq (G : SimpleGraph V) (M N : Finset (Sym2 V))
      (hM : IsPerfectMatching G M) (hN : IsPerfectMatching G N) (hsub : M ⊆ N) :
      N = M := by
    apply Finset.Subset.antisymm _ hsub
    intro e he
    induction e using Sym2.inductionOn with
    | hf v w =>
      obtain ⟨u, hu, _⟩ := hM.2 v
      have hwu := (hN.2 v).unique he (hsub hu)
      simpa [hwu] using hu

  have forcing_self (G : SimpleGraph V) (M : Finset (Sym2 V))
      (hM : IsPerfectMatching G M) : IsForcingSet G M M :=
    ⟨Finset.Subset.refl _, fun N hN hsub => perfect_subset_eq G M N hM hN hsub⟩

  have forcing_exists (G : SimpleGraph V) (M : Finset (Sym2 V))
      (hM : IsPerfectMatching G M) :
      ∃ S, IsForcingSet G M S ∧ S.card = forcingNumber G M := by
    change sInf {r | ∃ S, IsForcingSet G M S ∧ S.card = r} ∈
      {r | ∃ S, IsForcingSet G M S ∧ S.card = r}
    apply csInf_mem
    exact ⟨M.card, M, forcing_self G M hM, rfl⟩

  have forcing_le (G : SimpleGraph V) (M S : Finset (Sym2 V))
      (hS : IsForcingSet G M S) : forcingNumber G M ≤ S.card := by
    exact csInf_le' ⟨S, hS, rfl⟩

  have min_exists (G : SimpleGraph V) (hpm : ∃ M, IsPerfectMatching G M) :
      ∃ M, IsPerfectMatching G M ∧ forcingNumber G M = minForcingNumber G := by
    obtain ⟨M, hM⟩ := hpm
    change sInf {r | ∃ M, IsPerfectMatching G M ∧ forcingNumber G M = r} ∈
      {r | ∃ M, IsPerfectMatching G M ∧ forcingNumber G M = r}
    apply csInf_mem
    exact ⟨forcingNumber G M, M, hM, rfl⟩

  have max_exists (G : SimpleGraph V) (hpm : ∃ M, IsPerfectMatching G M) :
      ∃ M, IsPerfectMatching G M ∧ forcingNumber G M = maxForcingNumber G := by
    classical
    let s := {r | ∃ M, IsPerfectMatching G M ∧ forcingNumber G M = r}
    have hne : s.Nonempty := by
      obtain ⟨M, hM⟩ := hpm
      exact ⟨forcingNumber G M, M, hM, rfl⟩
    have hfin : s.Finite := (Set.finite_range (forcingNumber G)).subset (by
      rintro r ⟨M, _, hr⟩
      exact ⟨M, hr⟩)
    exact hne.csSup_mem hfin

  have bipartition (G : SimpleGraph V) (hG : G.IsBipartite) :
      ∃ A : Set V, ∀ v w, G.Adj v w → (v ∈ A ↔ w ∉ A) := by
    obtain ⟨A, B, hab⟩ := G.isBipartite_iff_exists_isBipartiteWith.mp hG
    refine ⟨A, ?_⟩
    intro v w hvw
    rcases hab.mem_of_adj hvw with h | h
    · exact ⟨fun _ hw => Set.disjoint_left.mp hab.disjoint hw h.2, fun _ => h.1⟩
    · exact ⟨fun hv => (Set.disjoint_left.mp hab.disjoint hv h.1).elim,
        fun hw => (hw h.2).elim⟩

  have forcing_product_bound (G : SimpleGraph V) (n : ℕ)
      (hG : G.IsBipartite) (horder : Fintype.card V = 2 * n)
      (hpm : ∃ M, IsPerfectMatching G M) :
      n ≤ (minForcingNumber G + 1) * (n - maxForcingNumber G) := by
    classical
    obtain ⟨A, hbi⟩ := bipartition G hG
    obtain ⟨M₀, hM₀, hmin⟩ := min_exists G hpm
    obtain ⟨S, hS, hScard⟩ := forcing_exists G M₀ hM₀
    obtain ⟨M, hM, hmax⟩ := max_exists G hpm
    obtain ⟨p₀, _, _⟩ := matching_equiv G A hbi M₀ hM₀
    have hA : Fintype.card A = n := by
      have hc := Fintype.card_congr p₀
      have hcompl := Fintype.card_compl_set A
      have hle := Fintype.card_subtype_le (fun v => v ∈ A)
      omega
    obtain ⟨S₁, hS₁, hbound⟩ := graph_bound G A hbi M₀ S M hM₀ hS hM
    have hf := forcing_le G M S₁ hS₁
    rw [hmax] at hf
    rw [hA, hScard, hmin] at hbound
    exact hbound.trans (Nat.mul_le_mul_left _ (Nat.sub_le_sub_left hf n))

  have hbound := forcing_product_bound G n hG horder hpm
  have hkpos : 0 < k := by omega
  have hd : n - maxForcingNumber G ≤ k := by omega
  have hmul : n ≤ (minForcingNumber G + 1) * k :=
    hbound.trans (Nat.mul_le_mul_left _ hd)
  have hceil : (n + k - 1) / k < (minForcingNumber G + 1) + 1 := by
    apply (Nat.div_lt_iff_lt_mul hkpos).mpr
    have hnk : 1 ≤ n + k := by omega
    have heq := Nat.sub_add_cancel hnk
    nlinarith
  omega

end Forcing
