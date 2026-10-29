import Mathlib

namespace CosetA

/-- Section 2: "the smallest one is called the coset leader".
The representatives of C_γ={γ,γq,...,γq^(τ-1)} lie in {0,...,n-1}.
For the coprime parameters below, using all natural exponents describes
the same orbit as using one period. -/
def IsCosetLeader (q n x : ℕ) : Prop :=
  x < n ∧ ∀ i : ℕ, x ≤ (x * q ^ i) % n

/-- Section 2: "q=p^e", with p prime, and q a finite field size. -/
def IsPrimePower (q : ℕ) : Prop :=
  ∃ p e : ℕ, Nat.Prime p ∧ 0 < e ∧ q = p ^ e

/-- Section 6: "the largest coset leaders" δ₁,δ₂.
This states that a is largest and b is second largest, in strict order. -/
def FirstTwo (q n a b : ℕ) : Prop :=
  IsCosetLeader q n a ∧ IsCosetLeader q n b ∧ b < a ∧
    ∀ x, IsCosetLeader q n x → x ≤ b ∨ x = a

/-- Section 6: "δ₁=3(q+1)(q^m+1)/4" for q≡1 (mod 4),
and "(3q+1)(q^m+1)/4" for q≡3 (mod 4). -/
def plusDeltaOne (q m : ℕ) : ℕ :=
  if q % 4 = 1 then 3 * (q + 1) * (q ^ m + 1) / 4
  else (3 * q + 1) * (q ^ m + 1) / 4

/-- Section 6: "δ₂=(3q-1)(q^m+1)/4" for q≡1 (mod 4),
and "((3q²+q-4)q^(m-1)-(q-1))/4" for q≡3 (mod 4). -/
def plusDeltaTwo (q m : ℕ) : ℕ :=
  if q % 4 = 1 then (3 * q - 1) * (q ^ m + 1) / 4
  else ((3 * q ^ 2 + q - 4) * q ^ (m - 1) - (q - 1)) / 4

/-- Section 6: "δ₁=q^(m+1)-q^(m-1)-q-1". -/
def minusDeltaOne (q m : ℕ) : ℕ :=
  q ^ (m + 1) - q ^ (m - 1) - q - 1

/-- Section 6: "δ₂=(q²-1)q²-(2q+1)" for m=3;
"(q²-1)q^(m-1)-(q+1)(q^((m-1)/2)+1)" for m>3. -/
def minusDeltaTwo (q m : ℕ) : ℕ :=
  if m = 3 then (q ^ 2 - 1) * q ^ 2 - (2 * q + 1)
  else (q ^ 2 - 1) * q ^ (m - 1) - (q + 1) * (q ^ ((m - 1) / 2) + 1)

-- Domain clarification made before proof: the conjectures are stated for odd m.
-- We use odd m >= 3: for m = 1 the second piecewise formula has no case, and the
-- formulas fail (for q = 3 the two largest leaders modulo 16 are 10 and 8).

/- A period of q modulo n reduces all orbit inequalities to finitely many. -/
theorem leader_of_period {q n x t : ℕ} (ht : 0 < t) (hx : x < n)
    (hp : q ^ t % n = 1)
    (hb : ∀ i < t, x ≤ (x * q ^ i) % n) : IsCosetLeader q n x := by
  refine ⟨hx, ?_⟩
  intro i
  have hpow : q ^ i % n = q ^ (i % t) % n := by
    conv_lhs => rw [← Nat.mod_add_div i t]
    rw [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod (q ^ t), hp, one_pow]
    rw [← Nat.mul_mod, mul_one]
  calc
    x ≤ (x * q ^ (i % t)) % n := hb (i % t) (Nat.mod_lt _ ht)
    _ = (x * q ^ i) % n := by
      rw [Nat.mul_mod x (q ^ (i % t)), Nat.mul_mod x (q ^ i), hpow]

/- The two finite exceptions in the paper argument for A(ii). -/
theorem binary_small_cases : FirstTwo 2 21 9 7 ∧ FirstTwo 2 93 45 33 := by
  constructor
  · refine ⟨leader_of_period (t := 6) (by norm_num) (by norm_num)
      (by norm_num) ?_, leader_of_period (t := 6) (by norm_num) (by norm_num)
      (by norm_num) ?_, by norm_num, ?_⟩
    · decide
    · decide
    · intro x hx
      have hb : ∀ x : Fin 21,
          (∀ i : Fin 6, x.val ≤ (x.val * 2 ^ i.val) % 21) →
            x.val ≤ 7 ∨ x.val = 9 := by decide
      exact hb ⟨x, hx.1⟩ (fun i => hx.2 i.val)
  · refine ⟨leader_of_period (t := 10) (by norm_num) (by norm_num)
      (by norm_num) ?_, leader_of_period (t := 10) (by norm_num) (by norm_num)
      (by norm_num) ?_, by norm_num, ?_⟩
    · decide
    · decide
    · intro x hx
      have hb : ∀ x : Fin 93,
          (∀ i : Fin 10, x.val ≤ (x.val * 2 ^ i.val) % 93) →
            x.val ≤ 33 ∨ x.val = 45 := by decide
      exact hb ⟨x, hx.1⟩ (fun i => hx.2 i.val)

/- The state transition used for q>=3 in Section 3.1 of SOLUTION.md. -/
theorem state_transition (q z z' a b : ℤ) (hq : 3 ≤ q)
    (hz : -1 ≤ z ∧ z ≤ 1) (hz' : -1 ≤ z' ∧ z' ≤ 1)
    (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1)
    (hr : z' = q * z - (q + 1) * (a - b)) :
    z' = -z ∧ a - b = z := by
  rcases hz with ⟨hz0, hz1⟩
  rcases ha with ⟨ha0, ha1⟩
  rcases hb with ⟨hb0, hb1⟩
  interval_cases z <;> interval_cases a <;> interval_cases b <;>
    simp_all <;> omega

/- The binary exceptional transition: spacing three forces the state zero.
The sequences a,b are the digits in the two half-blocks, and z is their
normalized difference. This statement is uniform in the sequence length. -/
theorem sparse_binary_states_zero (z a b : ℕ → ℤ)
    (hz : ∀ i, -2 ≤ z i ∧ z i ≤ 2)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1)
    (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1)
    (hr : ∀ i, z (i + 1) = 2 * z i - 3 * (a i - b i))
    (hsa : ∀ i, a i + a (i + 1) + a (i + 2) ≤ 1)
    (hsb : ∀ i, b i + b (i + 1) + b (i + 2) ≤ 1) :
    ∀ i, z i = 0 := by
  have no_two : ∀ i, -1 ≤ z i ∧ z i ≤ 1 := by
    intro i
    have z0 := hz i
    have z1 := hz (i + 1)
    have z2 := hz (i + 2)
    have z3 := hz (i + 3)
    have a0 := ha i
    have a1 := ha (i + 1)
    have a2 := ha (i + 2)
    have b0 := hb i
    have b1 := hb (i + 1)
    have b2 := hb (i + 2)
    have r0 := hr i
    have r1 : z (i + 2) = 2 * z (i + 1) - 3 * (a (i + 1) - b (i + 1)) := hr (i + 1)
    have r2 : z (i + 3) = 2 * z (i + 2) - 3 * (a (i + 2) - b (i + 2)) := hr (i + 2)
    have sa := hsa i
    have sb := hsb i
    omega
  intro i
  have z0 := no_two i
  have z1 := no_two (i + 1)
  have z2 := no_two (i + 2)
  have z3 := no_two (i + 3)
  have a0 := ha i
  have a1 := ha (i + 1)
  have a2 := ha (i + 2)
  have b0 := hb i
  have b1 := hb (i + 1)
  have b2 := hb (i + 2)
  have r0 := hr i
  have r1 : z (i + 2) = 2 * z (i + 1) - 3 * (a (i + 1) - b (i + 1)) := hr (i + 1)
  have r2 : z (i + 3) = 2 * z (i + 2) - 3 * (a (i + 2) - b (i + 2)) := hr (i + 2)
  have sa := hsa i
  have sb := hsb i
  omega

/- The algebra behind the two-block recurrence, with no digit assumptions. -/
theorem normalized_difference_transition
    (q Q S A B A' B' z z' a b : ℤ) (hS : S ≠ 0)
    (hQS : Q + 1 = (q + 1) * S)
    (hAB : A - B = S * z) (hAB' : A' - B' = S * z')
    (hA : A' = q * A - a * Q + b)
    (hB : B' = q * B - b * Q + a) :
    z' = q * z - (q + 1) * (a - b) := by
  apply mul_left_cancel₀ hS
  calc
    S * z' = A' - B' := hAB'.symm
    _ = q * (A - B) - (Q + 1) * (a - b) := by rw [hA, hB]; ring
    _ = S * (q * z - (q + 1) * (a - b)) := by rw [hAB, hQS]; ring

/- The radius gap used in the q=1 mod 4 plus-family argument. -/
theorem centered_radius_gap (q N M v u : ℤ)
    (hq : 2 ≤ q) (hN : 0 < N) (hM : 0 < M)
    (hv : |v| = M) (hu : |u| ≤ M) (hd : N ∣ q * v - u) :
    N ≤ (q + 1) * M := by
  by_contra h
  have hsmall : (q + 1) * M < N := by omega
  have hu' := abs_le.mp hu
  rcases hd with ⟨k, hk⟩
  have hv' : v = M ∨ v = -M := by
    rcases le_total 0 v with hp | hn
    · left; simpa only [abs_of_nonneg hp] using hv
    · right; have := hv; rw [abs_of_nonpos hn] at this; omega
  rcases hv' with rfl | rfl
  · by_cases hk0 : k = 0
    · subst k; nlinarith
    · have hk' : k ≤ -1 ∨ 1 ≤ k := by omega
      rcases hk' with hk' | hk' <;> nlinarith
  · by_cases hk0 : k = 0
    · subst k; nlinarith
    · have hk' : k ≤ -1 ∨ 1 ≤ k := by omega
      rcases hk' with hk' | hk' <;> nlinarith

/- The first radius bound for the q=3 mod 4 plus-family argument. -/
theorem odd_affine_radius_bound (q N R w u k : ℤ)
    (hq : 0 ≤ q) (hN : 0 < N) (_hR : 0 ≤ R)
    (hw : |w| ≤ R) (hu : |u| ≤ R)
    (hr : q * w - u = (2 * k + 1) * N) :
    N ≤ (q + 1) * R := by
  have hw' := abs_le.mp hw
  have hu' := abs_le.mp hu
  have hk : 0 ≤ k ∨ k ≤ -1 := by omega
  rcases hk with hk | hk
  · nlinarith [mul_nonneg hq (show 0 ≤ R - w by omega)]
  · nlinarith [mul_nonneg hq (show 0 ≤ R + w by omega)]

/- A nonconstant additive orbit cannot stay in the upper half of the residues. -/
theorem large_progression_step (n a d : ℤ) (hn : 0 < n)
    (h : ∀ k : ℤ, n < 2 * ((a + k * d) % n)) : n ∣ d := by
  let g : ℤ := Int.gcd n d
  have hg : 0 < g := by
    dsimp [g]
    exact_mod_cast Int.gcd_pos_of_ne_zero_left d (ne_of_gt hn)
  have hgn : g ∣ n := Int.gcd_dvd_left n d
  have hgd : g ∣ d := Int.gcd_dvd_right n d
  have hgle : g ≤ n := Int.le_of_dvd hn hgn
  have he : (a - (a / g) * Int.gcdB n d * d) % n = a % g := by
    have hm : Int.ModEq n (a - (a / g) * Int.gcdB n d * d) (a % g) := by
      apply Int.modEq_iff_dvd.mpr
      refine ⟨-(a / g) * Int.gcdA n d, ?_⟩
      rw [Int.emod_def]
      have hb : g = n * Int.gcdA n d + d * Int.gcdB n d :=
        Int.gcd_eq_gcd_ab n d
      rw [hb]
      ring
    exact hm.eq.trans (Int.emod_eq_of_lt (Int.emod_nonneg _ (ne_of_gt hg))
      (lt_of_lt_of_le (Int.emod_lt_of_pos _ hg) hgle))
  have hh := h (-(a / g) * Int.gcdB n d)
  have hr := Int.emod_lt_of_pos a hg
  have hh' : n < 2 * (a % g) := by
    convert hh using 1
    simp only [← sub_eq_add_neg, neg_mul, he]
  obtain ⟨j, hj⟩ := hgn
  have hj1 : j = 1 := by nlinarith
  have hng : n = g := by simpa [hj1] using hj
  rwa [hng]

/- Binomial expansion when the square of the increment vanishes modulo n. -/
theorem pow_linear_mod (n b : ℤ) (hb : n ∣ b ^ 2) (k : ℕ) :
    Int.ModEq n ((1 + b) ^ k) (1 + (k : ℤ) * b) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    apply (ih.mul (Int.ModEq.refl (1 + b))).trans
    apply Int.modEq_iff_dvd.mpr
    convert dvd_mul_of_dvd_right hb (-(k : ℤ)) using 1 <;> first | rfl | push_cast; ring

theorem leader_nilpotent_step (q n x b : ℤ) (t : ℕ)
    (hn : 0 < n) (hx : n < 2 * x)
    (hl : ∀ i : ℕ, x ≤ (x * q ^ i) % n)
    (hp : Int.ModEq n (q ^ t) (1 + b)) (hb : n ∣ b ^ 2) : n ∣ x * b := by
  apply large_progression_step n x (x * b) hn
  intro k
  let j := (k % n).toNat
  have hj : (j : ℤ) = k % n := Int.toNat_of_nonneg (Int.emod_nonneg k (ne_of_gt hn))
  have hpj := (hp.pow j).trans (pow_linear_mod n b hb j)
  have hjk : Int.ModEq n (j : ℤ) k := by rw [hj]; exact Int.mod_modEq k n
  have he : Int.ModEq n (x * q ^ (t * j)) (x + k * (x * b)) := by
    rw [pow_mul]
    calc
      x * (q ^ t) ^ j ≡ x * (1 + (j : ℤ) * b) [ZMOD n] := hpj.mul_left x
      _ ≡ x * (1 + k * b) [ZMOD n] := ((hjk.mul_right b).add_left 1).mul_left x
      _ = x + k * (x * b) := by ring
  have hh := hl (t * j)
  rw [he.eq] at hh
  omega

/- Section 2.1: every leader above half the plus modulus is divisible by
`(q+1)/2`.  The conclusion is stated without division. -/
theorem plus_high_divisibility {q m x : ℕ} (hm : Odd m)
    (hl : IsCosetLeader q ((q + 1) * (q ^ m + 1)) x)
    (hx : (q + 1) * (q ^ m + 1) < 2 * x) : q + 1 ∣ 2 * x := by
  let N : ℤ := (q : ℤ) ^ m + 1
  let n : ℤ := ((q : ℤ) + 1) * N
  have hN : 0 < N := by dsimp [N]; positivity
  have hn : 0 < n := by dsimp [n]; positivity
  have hd : (q : ℤ) + 1 ∣ N := by
    have hd := hm.nat_add_dvd_pow_add_pow q 1
    simpa [N] using (Int.natCast_dvd_natCast.mpr hd)
  have hsq : n ∣ N ^ 2 := by
    obtain ⟨c, hc⟩ := hd
    refine ⟨c, ?_⟩
    dsimp [n]
    rw [hc]
    ring
  have hp : Int.ModEq n ((q : ℤ) ^ (2 * m)) (1 + -2 * N) := by
    apply Int.modEq_iff_dvd.mpr
    convert dvd_neg.mpr hsq using 1
    · rfl
    · dsimp only [N]
      rw [mul_comm 2 m, pow_mul]
      ring
  have hb : n ∣ (-2 * N) ^ 2 := by
    convert dvd_mul_of_dvd_right hsq 4 using 1 <;> first | rfl | ring
  have hxl : ∀ i : ℕ, (x : ℤ) ≤ ((x : ℤ) * (q : ℤ) ^ i) % n := by
    intro i
    dsimp only [n, N]
    exact_mod_cast hl.2 i
  have hxh : n < 2 * (x : ℤ) := by dsimp only [n, N]; exact_mod_cast hx
  have hh := leader_nilpotent_step (q : ℤ) n x (-2 * N) (2 * m) hn hxh hxl hp hb
  have hd' : N * ((q : ℤ) + 1) ∣ N * (2 * (x : ℤ)) := by
    have hh' : n ∣ -(x * (-2 * N)) := Int.dvd_neg.mpr hh
    rw [show -(x * (-2 * N)) = N * (2 * x) by ring] at hh'
    simpa only [n, mul_comm N ((q : ℤ) + 1)] using hh'
  have hf : (q : ℤ) + 1 ∣ 2 * (x : ℤ) := (mul_dvd_mul_iff_left (ne_of_gt hN)).mp hd'
  exact_mod_cast hf

/- Scaling a modulus and representative by the same positive integer
preserves and reflects coset minimality. -/
theorem scale_leader_iff {q n x h : ℕ} (hh : 0 < h) :
    IsCosetLeader q (h * n) (h * x) ↔ IsCosetLeader q n x := by
  simp only [IsCosetLeader, mul_assoc, Nat.mul_mod_mul_left,
    mul_lt_mul_iff_right₀ hh, mul_le_mul_iff_right₀ hh]

/- Reflection of a residue in the upper half after multiplication by N-1. -/
theorem upper_reflection (N y : ℤ) (hy : N < y) (hy' : y < 2 * N) :
    (y * (N - 1)) % (2 * N) = if y % 2 = 0 then 2 * N - y else 3 * N - y := by
  split_ifs with he
  · have hy2 : y = 2 * (y / 2) := by omega
    have hm : Int.ModEq (2 * N) (y * (N - 1)) (2 * N - y) := by
      apply Int.modEq_iff_dvd.mpr
      refine ⟨1 - y / 2, ?_⟩
      nlinarith [hy2]
    exact hm.eq.trans (Int.emod_eq_of_lt (by omega) (by omega))
  · have hy2 : y = 2 * (y / 2) + 1 := by omega
    have hm : Int.ModEq (2 * N) (y * (N - 1)) (3 * N - y) := by
      apply Int.modEq_iff_dvd.mpr
      refine ⟨1 - y / 2, ?_⟩
      nlinarith [hy2]
    exact hm.eq.trans (Int.emod_eq_of_lt (by omega) (by omega))

/- The upper-half orbit has odd representatives and is reflected after m steps. -/
theorem upper_orbit_reflection (q N y : ℤ) (m : ℕ)
    (hN : 0 < N) (hp : q ^ m = N - 1) (hy : N < y)
    (hl : ∀ i : ℕ, y ≤ (y * q ^ i) % (2 * N)) :
    ∀ i : ℕ,
      ((y * q ^ i) % (2 * N)) % 2 = 1 ∧
      (y * q ^ (i + m)) % (2 * N) = 3 * N - (y * q ^ i) % (2 * N) ∧
      (y * q ^ i) % (2 * N) ≤ 3 * N - y := by
  intro i
  let r := (y * q ^ i) % (2 * N)
  have hrlo : N < r := lt_of_lt_of_le hy (hl i)
  have hrhi : r < 2 * N := Int.emod_lt_of_pos _ (by omega)
  have he : (y * q ^ (i + m)) % (2 * N) = (r * (N - 1)) % (2 * N) := by
    rw [pow_add, ← mul_assoc, hp]
    exact ((Int.mod_modEq (y * q ^ i) (2 * N)).mul_right (N - 1)).symm
  have href := upper_reflection N r hrlo hrhi
  have hlo := hl (i + m)
  rw [he, href] at hlo
  have hr2 : r % 2 = 1 := by
    by_contra hc
    have hr0 : r % 2 = 0 := by omega
    rw [if_pos hr0] at hlo
    omega
  have href' : (y * q ^ (i + m)) % (2 * N) = 3 * N - r := by
    rw [he, href, if_neg (by omega : r % 2 ≠ 0)]
  refine ⟨hr2, href', ?_⟩
  change r ≤ 3 * N - y
  split_ifs at hlo <;> omega

/- Division by h=(q+1)/2 identifies a high plus-family orbit with an
upper-half orbit modulo 2N. -/
theorem plus_high_reduction {q m x : ℕ} (hq : Odd q) (hm : Odd m)
    (hl : IsCosetLeader q ((q + 1) * (q ^ m + 1)) x)
    (hx : (q + 1) * (q ^ m + 1) < 2 * x) :
    ∃ h y : ℕ, q + 1 = 2 * h ∧ x = h * y ∧ 0 < h ∧
      IsCosetLeader q (2 * (q ^ m + 1)) y ∧ q ^ m + 1 < y := by
  obtain ⟨k, hk⟩ := hq
  have hqk : q + 1 = 2 * (k + 1) := by omega
  have hd := plus_high_divisibility hm hl hx
  rw [hqk] at hd
  have hd' : k + 1 ∣ x := (Nat.mul_dvd_mul_iff_left (by decide : 0 < 2)).mp hd
  obtain ⟨y, hxy⟩ := hd'
  refine ⟨k + 1, y, hqk, hxy, by omega, ?_, ?_⟩
  · apply (scale_leader_iff (h := k + 1) (by omega)).mp
    have hn : (q + 1) * (q ^ m + 1) = (k + 1) * (2 * (q ^ m + 1)) := by
      rw [hqk]; ring
    rwa [hn, hxy] at hl
  · rw [hqk, hxy] at hx
    nlinarith

/- The centered radius is either zero or at least 4N/(q+1) when q=1 mod 4.
Here the radius has been doubled to keep every expression integral. -/
theorem upper_q1_radius_gap (q N y : ℤ) (m : ℕ) (hq : 2 ≤ q)
    (hq4 : q % 4 = 1) (hN : 0 < N) (hp : q ^ m = N - 1)
    (hy : N < y) (hl : ∀ i : ℕ, y ≤ (y * q ^ i) % (2 * N)) :
    2 * y ≤ 3 * N ∧ (2 * y = 3 * N ∨ 4 * N ≤ (q + 1) * (3 * N - 2 * y)) := by
  have href := upper_orbit_reflection q N y m hN hp hy hl
  have hyhi : y < 2 * N := lt_of_le_of_lt (hl 0) (Int.emod_lt_of_pos _ (by omega))
  have hr0 : (y * q ^ 0) % (2 * N) = y := by
    simp only [pow_zero, mul_one, Int.emod_eq_of_lt (by omega : 0 ≤ y) hyhi]
  have hbound := (href 0).2.2
  rw [hr0] at hbound
  refine ⟨by omega, ?_⟩
  by_cases he : 2 * y = 3 * N
  · exact Or.inl he
  right
  let r := (y * q) % (2 * N)
  have hrlo : y ≤ r := by simpa only [pow_one] using hl 1
  have hrhi : r ≤ 3 * N - y := by simpa only [pow_one] using (href 1).2.2
  have hd : 4 * N ∣ q * (2 * y - 3 * N) - (2 * r - 3 * N) := by
    refine ⟨(y * q) / (2 * N) - 3 * (q / 4), ?_⟩
    have hq' : q - 1 = 4 * (q / 4) := by omega
    change q * (2 * y - 3 * N) - (2 * ((y * q) % (2 * N)) - 3 * N) = _
    rw [Int.emod_def]
    calc
      _ = 4 * N * ((y * q) / (2 * N)) - 3 * N * (q - 1) := by ring
      _ = _ := by rw [hq']; ring
  exact centered_radius_gap q (4 * N) (3 * N - 2 * y) (2 * y - 3 * N)
    (2 * r - 3 * N) hq (by omega) (by omega)
    (by rw [abs_of_nonpos (by omega)]; omega) (abs_le.mpr ⟨by omega, by omega⟩) hd

/- A one-point orbit gives a coset leader. -/
theorem leader_of_fixed {q n x : ℕ} (hx : x < n) (he : (x * q) % n = x) :
    IsCosetLeader q n x := by
  refine ⟨hx, ?_⟩
  intro i
  suffices (x * q ^ i) % n = x by omega
  induction i with
  | zero => simpa using Nat.mod_eq_of_lt hx
  | succ i ih =>
    rw [pow_succ, ← mul_assoc, Nat.mul_mod, ih, Nat.mul_mod_mod, he]

/- The smaller of the two points of a two-point orbit is its leader. -/
theorem leader_of_two_cycle {q n a b : ℕ} (ha : a < n) (hab : a ≤ b)
    (h1 : (a * q) % n = b) (h2 : (b * q) % n = a) : IsCosetLeader q n a := by
  refine ⟨ha, ?_⟩
  intro i
  have hr : (a * q ^ i) % n = a ∨ (a * q ^ i) % n = b := by
    induction i with
    | zero => exact Or.inl (by simpa using Nat.mod_eq_of_lt ha)
    | succ i ih =>
      rw [pow_succ, ← mul_assoc, Nat.mul_mod]
      rcases ih with ih | ih
      · right; rw [ih, Nat.mul_mod_mod, h1]
      · left; rw [ih, Nat.mul_mod_mod, h2]
  rcases hr with hr | hr <;> omega

/- Both proposed leaders for q=1 mod 4 are realized by orbits of size at most two. -/
theorem q1_candidate_leaders (k s : ℕ) (hk : 0 < k) (hs : 0 < s) :
    IsCosetLeader (4 * k + 1) (4 * (2 * k + 1) * s) (3 * (2 * k + 1) * s) ∧
    IsCosetLeader (4 * k + 1) (4 * (2 * k + 1) * s) ((6 * k + 1) * s) := by
  have hn : 0 < 4 * (2 * k + 1) * s := by positivity
  have ha : 3 * (2 * k + 1) * s < 4 * (2 * k + 1) * s := by nlinarith
  have hb : (6 * k + 1) * s < 4 * (2 * k + 1) * s := by nlinarith
  have hc : (6 * k + 5) * s < 4 * (2 * k + 1) * s := by nlinarith
  constructor
  · apply leader_of_fixed ha
    have he : 3 * (2 * k + 1) * s * (4 * k + 1) =
        3 * (2 * k + 1) * s + (3 * k) * (4 * (2 * k + 1) * s) := by ring
    rw [he, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha]
  · apply leader_of_two_cycle hb (b := (6 * k + 5) * s) (by nlinarith)
    · have he : (6 * k + 1) * s * (4 * k + 1) =
          (6 * k + 5) * s + (3 * k - 1) * (4 * (2 * k + 1) * s) := by
        have hk' : 3 * k - 1 + 1 = 3 * k := by omega
        nlinarith [hk']
      rw [he, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
    · have he : (6 * k + 5) * s * (4 * k + 1) =
          (6 * k + 1) * s + (3 * k + 1) * (4 * (2 * k + 1) * s) := by ring
      rw [he, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]

/- The entire q=1 mod 4 branch of A(i), without a prime-power assumption. -/
theorem plus_q1_firstTwo (q m : ℕ) (hq : 2 ≤ q) (hq4 : q % 4 = 1) (hm : Odd m) :
    FirstTwo q ((q + 1) * (q ^ m + 1)) (plusDeltaOne q m) (plusDeltaTwo q m) := by
  let k := q / 4
  have hqk : q = 4 * k + 1 := by omega
  have hk : 0 < k := by omega
  have hqo : Odd q := ⟨2 * k, by omega⟩
  have hpodd : Odd (q ^ m) := hqo.pow
  let s := (q ^ m + 1) / 2
  have hNs : q ^ m + 1 = 2 * s := by
    obtain ⟨t, ht⟩ := hpodd
    dsimp [s]
    omega
  have hs : 0 < s := by omega
  have hn : (q + 1) * (q ^ m + 1) = 4 * (2 * k + 1) * s := by rw [hNs, hqk]; ring
  have ha : plusDeltaOne q m = 3 * (2 * k + 1) * s := by
    rw [plusDeltaOne, if_pos hq4]
    have he : 3 * (q + 1) * (q ^ m + 1) = 3 * (2 * k + 1) * s * 4 := by
      rw [hNs, hqk]; ring
    rw [he, Nat.mul_div_cancel _ (by decide : 0 < 4)]
  have hb : plusDeltaTwo q m = (6 * k + 1) * s := by
    rw [plusDeltaTwo, if_pos hq4]
    have he : (3 * q - 1) * (q ^ m + 1) = (6 * k + 1) * s * 4 := by
      rw [hNs, hqk, show 3 * (4 * k + 1) - 1 = 12 * k + 2 by omega]
      ring
    rw [he, Nat.mul_div_cancel _ (by decide : 0 < 4)]
  obtain ⟨hla, hlb⟩ := q1_candidate_leaders k s hk hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ha, hn, hqk]; exact hla
  · rw [hb, hn, hqk]; exact hlb
  · rw [ha, hb]; nlinarith
  · intro x hl
    by_cases hxb : x ≤ plusDeltaTwo q m
    · exact Or.inl hxb
    right
    have hxhi : (q + 1) * (q ^ m + 1) < 2 * x := by rw [hn]; rw [hb] at hxb; nlinarith
    obtain ⟨h, y, hqh, hxy, hh, hly, hy⟩ := plus_high_reduction hqo hm hl hxhi
    have hhk : h = 2 * k + 1 := by omega
    have hgap := upper_q1_radius_gap (q : ℤ) ((q : ℤ) ^ m + 1) y m
      (by exact_mod_cast hq) (by exact_mod_cast hq4) (by positivity) (by ring)
      (by exact_mod_cast hy) (fun i => by exact_mod_cast hly.2 i)
    have hNs' : (q : ℤ) ^ m + 1 = 2 * (s : ℤ) := by exact_mod_cast hNs
    have hqk' : (q : ℤ) = 4 * (k : ℤ) + 1 := by exact_mod_cast hqk
    have hxy' : (x : ℤ) = (2 * (k : ℤ) + 1) * (y : ℤ) := by
      rw [hhk] at hxy
      exact_mod_cast hxy
    have hxb' : (6 * (k : ℤ) + 1) * (s : ℤ) < (x : ℤ) := by
      rw [hb] at hxb
      exact_mod_cast (Nat.lt_of_not_ge hxb)
    rw [hNs', hqk'] at hgap
    rw [ha]
    apply Int.ofNat_inj.mp
    push_cast
    rcases hgap.2 with he | he
    · nlinarith
    · exfalso; nlinarith

/- Multiplication by a suitable power brings a leading base-q digit to the
top position. This is the first extremal word bound without a digit encoding. -/
theorem primitive_max_lower (q m d : ℕ) (hq : 2 ≤ q) (hm : 0 < m) (hd : 0 < d)
    (hmax : ∀ i : ℕ, (d * q ^ i) % (q ^ m - 1) ≤ d) : q ^ (m - 1) ≤ d := by
  by_contra hc
  have hdt : d < q ^ (m - 1) := by omega
  let t := Nat.log q d
  have htl : q ^ t ≤ d := Nat.pow_log_le_self q (by omega)
  have htu : d < q ^ (t + 1) := Nat.lt_pow_succ_log_self (by omega) d
  have htm : t < m - 1 := (Nat.log_lt_iff_lt_pow (by omega) (by omega)).mpr hdt
  let j := m - 1 - t
  have hj : 0 < j := by omega
  have htj : t + j = m - 1 := by omega
  have htj' : t + 1 + j = m := by omega
  have hpj : 2 ≤ q ^ j := le_trans hq (Nat.le_pow hj)
  have hlo : q ^ (m - 1) ≤ d * q ^ j := by
    calc
      q ^ (m - 1) = q ^ t * q ^ j := by rw [← pow_add, htj]
      _ ≤ d * q ^ j := Nat.mul_le_mul_right _ htl
  have hhi : d * q ^ j < q ^ m - 1 := by
    have he : q ^ (t + 1) * q ^ j = q ^ m := by rw [← pow_add, htj']
    have hh := Nat.mul_le_mul_right (q ^ j) (show d + 1 ≤ q ^ (t + 1) by omega)
    rw [he] at hh
    have hQ : q ^ m - 1 + 1 = q ^ m := Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))
    nlinarith
  have hh := hmax j
  rw [Nat.mod_eq_of_lt hhi] at hh
  omega

/- For length 2h+1, a value strictly between the first two proposed maxima
has a rotation larger than itself. -/
theorem primitive_max_gap (q h d : ℕ) (hq : 2 ≤ q) (hh : 0 < h) (hd : 0 < d)
    (hmax : ∀ i : ℕ, (d * q ^ i) % (q ^ (2 * h + 1) - 1) ≤ d)
    (hsmall : d < q ^ (2 * h) + q ^ h) : d = q ^ (2 * h) := by
  have hlo : q ^ (2 * h) ≤ d := by
    simpa using primitive_max_lower q (2 * h + 1) d hq (by omega) hd hmax
  by_contra he
  let e := d - q ^ (2 * h)
  have hepos : 0 < e := by omega
  have heq : d = q ^ (2 * h) + e := by omega
  have hehi : e < q ^ h := by omega
  let t := Nat.log q e
  have htl : q ^ t ≤ e := Nat.pow_log_le_self q (by omega)
  have htu : e < q ^ (t + 1) := Nat.lt_pow_succ_log_self (by omega) e
  have hth : t < h := (Nat.log_lt_iff_lt_pow (by omega) (by omega)).mpr hehi
  let j := 2 * h - t
  have hj : 0 < j := by omega
  have hjh : h ≤ j - 1 := by omega
  have htj : t + j = 2 * h := by omega
  have htj' : t + 1 + j = 2 * h + 1 := by omega
  have hp : q ^ j = q ^ (j - 1) * q := by rw [← pow_succ]; congr 1; omega
  have hpj : 0 < q ^ (j - 1) := pow_pos (by omega) _
  have hrhi : e * q ^ j + q ^ (j - 1) < q ^ (2 * h + 1) - 1 := by
    have hu := Nat.mul_le_mul_right (q ^ j) (show e + 1 ≤ q ^ (t + 1) by omega)
    rw [← pow_add, htj'] at hu
    have hj2 : 2 ≤ j := by omega
    have hpj2 : 2 ≤ q ^ (j - 1) := le_trans hq (Nat.le_pow (by omega))
    have hQ : q ^ (2 * h + 1) - 1 + 1 = q ^ (2 * h + 1) :=
      Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))
    nlinarith
  have hrlo : q ^ (2 * h) + q ^ h ≤ e * q ^ j + q ^ (j - 1) := by
    apply Nat.add_le_add
    · calc
        q ^ (2 * h) = q ^ t * q ^ j := by rw [← pow_add, htj]
        _ ≤ e * q ^ j := Nat.mul_le_mul_right _ htl
    · exact Nat.pow_le_pow_right (by omega) hjh
  have hQ : 1 ≤ q ^ (2 * h + 1) := Nat.one_le_pow _ _ (by omega)
  have hpoly : d * q ^ j = e * q ^ j + q ^ (j - 1) +
      (q ^ (2 * h + 1) - 1) * q ^ (j - 1) := by
    rw [heq, add_mul]
    have hex : 2 * h + j = (2 * h + 1) + (j - 1) := by omega
    rw [← pow_add, hex, pow_add]
    nlinarith [Nat.sub_add_cancel hQ]
  have hr : (d * q ^ j) % (q ^ (2 * h + 1) - 1) = e * q ^ j + q ^ (j - 1) := by
    rw [hpoly, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrhi]
  have hb := hmax j
  rw [hr] at hb
  omega

/- Taking complements converts a positive leader into an orbit maximum. -/
theorem complement_max_of_leader {q n x : ℕ} (hl : IsCosetLeader q n x) (hx : 0 < x) :
    ∀ i : ℕ, ((n - x) * q ^ i) % n ≤ n - x := by
  intro i
  have hxlt := hl.1
  have hn : 0 < n := by omega
  have ha := Nat.mod_lt ((n - x) * q ^ i) hn
  have hb := Nat.mod_lt (x * q ^ i) hn
  have hc := hl.2 i
  have he : (((n - x) * q ^ i) % n + (x * q ^ i) % n) % n = 0 := by
    rw [← Nat.add_mod, ← add_mul, Nat.sub_add_cancel hl.1.le, Nat.mul_mod_right]
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero he
  have hkpos : 0 < k := by
    by_contra hh
    have hk0 : k = 0 := by omega
    rw [hk0, mul_zero] at hk
    omega
  have hk1 : k = 1 := by nlinarith
  rw [hk1, mul_one] at hk
  omega

/- Conversely, a nonzero maximum in an invertible multiplication orbit
gives a coset leader by taking its complement. -/
theorem leader_of_complement_max {q n d : ℕ} (hd : 0 < d) (hdn : d < n)
    (hqn : Nat.Coprime n q) (hmax : ∀ i : ℕ, (d * q ^ i) % n ≤ d) :
    IsCosetLeader q n (n - d) := by
  refine ⟨by omega, ?_⟩
  intro i
  have hn : 0 < n := by omega
  have ha := Nat.mod_lt ((n - d) * q ^ i) hn
  have hb := Nat.mod_lt (d * q ^ i) hn
  have hc := hmax i
  have hpos : 0 < (d * q ^ i) % n := by
    by_contra hz
    have hdiv : n ∣ d * q ^ i := Nat.dvd_of_mod_eq_zero (by omega)
    have hnd : n ∣ d := (hqn.pow_right i).dvd_of_dvd_mul_right hdiv
    have := Nat.le_of_dvd hd hnd
    omega
  have he : (((n - d) * q ^ i) % n + (d * q ^ i) % n) % n = 0 := by
    rw [← Nat.add_mod, ← add_mul, Nat.sub_add_cancel hdn.le, Nat.mul_mod_right]
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero he
  have hkpos : 0 < k := by
    by_contra hh
    have hk0 : k = 0 := by omega
    rw [hk0, mul_zero] at hk
    omega
  have hk1 : k = 1 := by nlinarith
  rw [hk1, mul_one] at hk
  omega

theorem max_of_period {q n d t : ℕ} (ht : 0 < t) (hp : q ^ t % n = 1)
    (hb : ∀ i < t, (d * q ^ i) % n ≤ d) : ∀ i : ℕ, (d * q ^ i) % n ≤ d := by
  intro i
  have hpow : q ^ i % n = q ^ (i % t) % n := by
    conv_lhs => rw [← Nat.mod_add_div i t]
    rw [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod (q ^ t), hp, one_pow]
    rw [← Nat.mul_mod, mul_one]
  calc
    (d * q ^ i) % n = (d * q ^ (i % t)) % n := by
      rw [Nat.mul_mod d (q ^ i), Nat.mul_mod d (q ^ (i % t)), hpow]
    _ ≤ d := hb (i % t) (Nat.mod_lt _ ht)

theorem primitive_period (q m : ℕ) (hq : 2 ≤ q) (hm : 2 ≤ m) :
    q ^ m % (q ^ m - 1) = 1 := by
  have hqm : 4 ≤ q ^ m := by
    calc
      4 ≤ q ^ 2 := by nlinarith
      _ ≤ q ^ m := Nat.pow_le_pow_right (by omega) hm
  have he : q ^ m = 1 + (q ^ m - 1) := by omega
  calc
    q ^ m % (q ^ m - 1) = (1 + (q ^ m - 1)) % (q ^ m - 1) :=
      congrArg (fun z => z % (q ^ m - 1)) he
    _ = 1 := by rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : 1 < q ^ m - 1)]

theorem primitive_pow_shift (q m k : ℕ) (hp : q ^ m % (q ^ m - 1) = 1) :
    Nat.ModEq (q ^ m - 1) (q ^ (m + k)) (q ^ k) := by
  rw [pow_add]
  have hm : Nat.ModEq (q ^ m - 1) (q ^ m) 1 := by
    change _ = 1 % (q ^ m - 1)
    simpa only [Nat.mod_mod] using congrArg (fun z => z % (q ^ m - 1)) hp
  simpa only [one_mul] using hm.mul_right (q ^ k)

theorem primitive_single_max (q m : ℕ) (hq : 2 ≤ q) (hm : 2 ≤ m) :
    ∀ i : ℕ, (q ^ (m - 1) * q ^ i) % (q ^ m - 1) ≤ q ^ (m - 1) := by
  apply max_of_period (t := m) (by omega) (primitive_period q m hq hm)
  intro i hi
  by_cases hi0 : i = 0
  · subst i; simpa using Nat.mod_le (q ^ (m - 1)) (q ^ m - 1)
  have he : m - 1 + i = m + (i - 1) := by omega
  rw [← pow_add, he, primitive_pow_shift q m (i - 1) (primitive_period q m hq hm)]
  exact le_trans (Nat.mod_le _ _) (Nat.pow_le_pow_right (by omega) (by omega))

theorem primitive_double_max (q h : ℕ) (hq : 2 ≤ q) (hh : 0 < h) :
    ∀ i : ℕ, ((q ^ (2 * h) + q ^ h) * q ^ i) % (q ^ (2 * h + 1) - 1) ≤
      q ^ (2 * h) + q ^ h := by
  have hp := primitive_period q (2 * h + 1) hq (by omega)
  apply max_of_period (t := 2 * h + 1) (by omega) hp
  intro i hi
  by_cases hi0 : i = 0
  · subst i; simpa using Nat.mod_le (q ^ (2 * h) + q ^ h) (q ^ (2 * h + 1) - 1)
  have he : 2 * h + i = (2 * h + 1) + (i - 1) := by omega
  have hm1 : Nat.ModEq (q ^ (2 * h + 1) - 1) (q ^ (2 * h + i)) (q ^ (i - 1)) := by
    rw [he]; exact primitive_pow_shift q (2 * h + 1) (i - 1) hp
  by_cases hih : i ≤ h
  · have hm2 := hm1.add (Nat.ModEq.refl (n := q ^ (2 * h + 1) - 1) (q ^ (h + i)))
    rw [add_mul, ← pow_add, ← pow_add, hm2]
    apply le_trans (Nat.mod_le _ _)
    have ha : q ^ (i - 1) ≤ q ^ h := Nat.pow_le_pow_right (by omega) (by omega)
    have hb : q ^ (h + i) ≤ q ^ (2 * h) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  · have he2 : h + i = (2 * h + 1) + (i - h - 1) := by omega
    have hm2 : Nat.ModEq (q ^ (2 * h + 1) - 1) (q ^ (h + i)) (q ^ (i - h - 1)) := by
      rw [he2]; exact primitive_pow_shift q (2 * h + 1) (i - h - 1) hp
    rw [add_mul, ← pow_add, ← pow_add, hm1.add hm2]
    apply le_trans (Nat.mod_le _ _)
    exact Nat.add_le_add (Nat.pow_le_pow_right (by omega) (by omega))
      (Nat.pow_le_pow_right (by omega) (by omega))

/- An integer geometric sequence with ratio at least two is bounded only
when it vanishes. -/
theorem bounded_geometric_zero (q C : ℤ) (u : ℕ → ℤ) (hq : 2 ≤ q)
    (hC : 0 ≤ C) (hu : ∀ i, |u i| ≤ C) (hr : ∀ i, u (i + 1) = q * u i) : u 0 = 0 := by
  have he : ∀ i, u i = q ^ i * u 0 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [hr, ih, pow_succ]; ring
  have hp : ∀ i : ℕ, (i : ℤ) + 1 ≤ q ^ i := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ]; push_cast; nlinarith
  by_contra hz
  have hz' : 1 ≤ |u 0| := by have := abs_nonneg (u 0); have := abs_eq_zero.not.mpr hz; omega
  have hcn : (C.toNat : ℤ) = C := Int.toNat_of_nonneg hC
  have hh := hu (C.toNat + 1)
  rw [he, abs_mul, abs_of_nonneg (by positivity : 0 ≤ q ^ (C.toNat + 1))] at hh
  have hh' := hp (C.toNat + 1)
  push_cast at hh'
  rw [hcn] at hh'
  nlinarith

/- Bounded two-block states are either equal-half states or the alternating
state. This is the arithmetic form of the sparse-word classification. -/
theorem binary_state_classification (q B D : ℤ) (d a z : ℕ → ℤ)
    (hq : 3 ≤ q) (hB : 0 < B)
    (hd : ∀ i, 0 ≤ d i ∧ d i ≤ D) (hmax : ∀ i, d i ≤ d 0)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1)
    (hz : ∀ i, -1 ≤ z i ∧ z i ≤ 1)
    (m : ℕ) (hdz : ∀ i, d i - d (i + m) = B * z i)
    (hr : ∀ i, d (i + 1) = q * d i - (q + 1) * B * a i)
    (hzr : ∀ i, z (i + 1) = q * z i - (q + 1) * (a i - a (i + m))) :
    z 0 = 0 ∨ (q - 1) * d 0 = q * B := by
  have ht : ∀ i, z (i + 1) = -z i ∧ a i - a (i + m) = z i := by
    intro i
    exact state_transition q (z i) (z (i + 1)) (a i) (a (i + m)) hq
      (hz i) (hz (i + 1)) (ha i) (ha (i + m)) (hzr i)
  by_cases hz0 : z 0 = 0
  · exact Or.inl hz0
  right
  have hz01 : z 0 = 1 := by
    have h0 := hdz 0
    have hm := hmax m
    have hb := hz 0
    simp only [zero_add] at h0
    have hz' : z 0 = -1 ∨ z 0 = 1 := by omega
    rcases hz' with hz' | hz'
    · rw [hz'] at h0; nlinarith
    · exact hz'
  have hz2 : ∀ i, z (2 * i) = 1 := by
    intro i
    induction i with
    | zero => simpa using hz01
    | succ i ih =>
      have h1 := (ht (2 * i)).1
      have h2 := (ht (2 * i + 1)).1
      have he : 2 * (i + 1) = 2 * i + 1 + 1 := by omega
      rw [he, h2, h1, ih]; ring
  have ha2 : ∀ i, a (2 * i) = 1 ∧ a (2 * i + 1) = 0 := by
    intro i
    have he := (ht (2 * i)).2
    have ho := (ht (2 * i + 1)).2
    have ze := hz2 i
    have zo := (ht (2 * i)).1
    have a0 := ha (2 * i)
    have a1 := ha (2 * i + 1)
    have b0 := ha (2 * i + m)
    have b1 := ha (2 * i + 1 + m)
    omega
  have hr2 : ∀ i, d (2 * (i + 1)) = q ^ 2 * d (2 * i) - q * (q + 1) * B := by
    intro i
    have h0 := hr (2 * i)
    have h1 := hr (2 * i + 1)
    rw [(ha2 i).1] at h0
    rw [(ha2 i).2, h0] at h1
    rw [show 2 * (i + 1) = 2 * i + 1 + 1 by omega, h1]
    ring
  let u := fun i => (q ^ 2 - 1) * d (2 * i) - q * (q + 1) * B
  have hu : ∀ i, |u i| ≤ (q ^ 2 - 1) * D + q * (q + 1) * B := by
    intro i
    have hi := hd (2 * i)
    have hq2 : 0 ≤ q ^ 2 - 1 := by nlinarith
    dsimp [u]
    apply abs_le.mpr
    constructor <;> nlinarith [mul_nonneg hq2 (show 0 ≤ D - d (2 * i) by omega)]
  have he : u 0 = 0 := by
    have hq2 : 0 ≤ q ^ 2 - 1 := by nlinarith
    have hD : 0 ≤ D := le_trans (hd 0).1 (hd 0).2
    apply bounded_geometric_zero (q ^ 2) ((q ^ 2 - 1) * D + q * (q + 1) * B) u
      (by nlinarith) (by positivity) hu
    intro i
    dsimp [u]
    rw [hr2]
    ring
  dsimp [u] at he
  have hf : (q + 1) * ((q - 1) * d 0 - q * B) = 0 := by nlinarith [he]
  have hf' := (mul_eq_zero.mp hf).resolve_left (by omega : q + 1 ≠ 0)
  omega

/- A small orbit maximum for a minus modulus is either divisible by q+1
or has the alternating value. The bounds encode the binary-digit condition. -/
theorem minus_small_max_classification (q B D : ℤ) (m : ℕ)
    (hq : 3 ≤ q) (hB : 0 < B) (hp : q ^ m = B + 1) (hD : 0 ≤ D)
    (hDn : D < (q + 1) * B)
    (hmax : ∀ i : ℕ, (D * q ^ i) % ((q + 1) * B) ≤ D)
    (hwidth : D < 2 * B) (hstep : q * D < 2 * ((q + 1) * B)) :
    (q + 1) ∣ D ∨ (q - 1) * D = q * B := by
  let n := (q + 1) * B
  let d := fun i : ℕ => (D * q ^ i) % n
  let a := fun i : ℕ => q * d i / n
  let z := fun i : ℕ => (d i - d (i + m)) / B
  have hn : 0 < n := by dsimp [n]; positivity
  have hd : ∀ i, 0 ≤ d i ∧ d i ≤ D := fun i =>
    ⟨Int.emod_nonneg _ (ne_of_gt hn), hmax i⟩
  have hd0 : d 0 = D := by
    dsimp [d]; rw [pow_zero, mul_one, Int.emod_eq_of_lt hD (show D < n from hDn)]
  have ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1 := by
    intro i
    have hi := hd i
    dsimp [a]
    constructor
    · exact Int.ediv_nonneg (mul_nonneg (by omega) hi.1) hn.le
    · have he : q * d i < 2 * n := lt_of_le_of_lt (mul_le_mul_of_nonneg_left hi.2 (by omega)) hstep
      have := (Int.ediv_lt_iff_lt_mul hn).mpr he
      omega
  have hr : ∀ i, d (i + 1) = q * d i - (q + 1) * B * a i := by
    intro i
    have he : d (i + 1) = (q * d i) % n := by
      calc
        d (i + 1) = (q * (D * q ^ i)) % n := by
          dsimp [d]
          congr 1
          rw [pow_succ]
          ring
        _ = (q * d i) % n := ((Int.mod_modEq (D * q ^ i) n).mul_left q).symm
    rw [he, Int.emod_def]
  have hdz : ∀ i, d i - d (i + m) = B * z i := by
    intro i
    have hp' : Int.ModEq B (q ^ m) 1 := by
      apply Int.modEq_iff_dvd.mpr
      exact ⟨-1, by rw [hp]; ring⟩
    have hm : Int.ModEq B (d (i + m)) (d i) := by
      have hmod : ∀ j, Int.ModEq B (d j) (D * q ^ j) := fun j =>
        (Int.mod_modEq (D * q ^ j) n).of_dvd (dvd_mul_left B (q + 1))
      apply (hmod (i + m)).trans
      apply Int.ModEq.trans _ (hmod i).symm
      rw [pow_add, ← mul_assoc]
      simpa only [mul_one] using hp'.mul_left (D * q ^ i)
    exact (Int.mul_ediv_cancel_of_dvd hm.dvd).symm
  have hz : ∀ i, -1 ≤ z i ∧ z i ≤ 1 := by
    intro i
    have h0 := hd i
    have h1 := hd (i + m)
    have he := hdz i
    constructor <;> nlinarith
  have hzr : ∀ i, z (i + 1) = q * z i - (q + 1) * (a i - a (i + m)) := by
    intro i
    apply mul_left_cancel₀ (ne_of_gt hB)
    rw [← hdz (i + 1), show i + 1 + m = i + m + 1 by omega, hr i, hr (i + m)]
    calc
      _ = q * (d i - d (i + m)) - (q + 1) * B * (a i - a (i + m)) := by ring
      _ = _ := by rw [hdz i]; ring
  rcases binary_state_classification q B D d a z hq hB hd
    (fun i => by rw [hd0]; exact (hd i).2) ha hz m hdz hr hzr with hz0 | halt
  · left
    have hdm : d m = D := by
      have he := hdz 0
      rw [hd0, hz0, mul_zero, zero_add] at he
      omega
    have he : Int.ModEq n (D * q ^ m) D := by
      change (D * q ^ m) % n = D % n
      rw [Int.emod_eq_of_lt hD (show D < n from hDn)]
      exact hdm
    have hnD : B * (q + 1) ∣ B * D := by
      have hh : n ∣ D * q ^ m - D := Int.dvd_neg.mp (by simpa using he.dvd)
      rw [hp, show D * (B + 1) - D = B * D by ring] at hh
      simpa only [n, mul_comm B (q + 1)] using hh
    exact (mul_dvd_mul_iff_left (ne_of_gt hB)).mp hnD
  · right; rwa [hd0] at halt

theorem primitive_coprime (q m : ℕ) (hq : 1 ≤ q) (hm : 0 < m) :
    Nat.Coprime (q ^ m - 1) q := by
  have hc : Nat.Coprime (q ^ m) (q ^ m - 1) :=
    (Nat.coprime_self_sub_right (Nat.one_le_pow _ _ hq)).mpr (Nat.coprime_one_right _)
  exact (hc.of_dvd_left (dvd_pow_self q (by omega))).symm

/- The two extremal primitive cosets needed for the minus-family reduction. -/
theorem primitive_firstTwo (q h : ℕ) (hq : 2 ≤ q) (hh : 0 < h) :
    FirstTwo q (q ^ (2 * h + 1) - 1)
      (q ^ (2 * h + 1) - 1 - q ^ (2 * h))
      (q ^ (2 * h + 1) - 1 - (q ^ (2 * h) + q ^ h)) := by
  have hs : 2 ≤ q ^ h := le_trans hq (Nat.le_pow hh)
  have hsq : q ^ (2 * h) = (q ^ h) ^ 2 := by rw [mul_comm 2 h, pow_mul]
  have hQ : q ^ (2 * h + 1) = q ^ (2 * h) * q := pow_succ _ _
  have hB : q ^ (2 * h + 1) - 1 + 1 = q ^ (2 * h + 1) :=
    Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))
  have he : q ^ (2 * h) + q ^ h < q ^ (2 * h + 1) - 1 := by nlinarith
  have he1 : q ^ (2 * h) < q ^ (2 * h + 1) - 1 := by omega
  have hd1 : 0 < q ^ (2 * h) := by positivity
  have hcop := primitive_coprime q (2 * h + 1) (by omega) (by omega)
  refine ⟨leader_of_complement_max hd1 he1 hcop ?_,
    leader_of_complement_max (by positivity) he hcop (primitive_double_max q h hq hh),
    by omega, ?_⟩
  · simpa using primitive_single_max q (2 * h + 1) hq (by omega)
  · intro x hl
    by_cases hx : x ≤ q ^ (2 * h + 1) - 1 - (q ^ (2 * h) + q ^ h)
    · exact Or.inl hx
    right
    have hx0 : 0 < x := by omega
    have hxlt := hl.1
    have hd : 0 < q ^ (2 * h + 1) - 1 - x := by omega
    have hmax := complement_max_of_leader hl hx0
    have hsmall : q ^ (2 * h + 1) - 1 - x < q ^ (2 * h) + q ^ h := by omega
    have heq := primitive_max_gap q h (q ^ (2 * h + 1) - 1 - x) hq hh hd hmax hsmall
    omega

theorem scaled_firstTwo_of_large_divisible {q B a b h : ℕ} (hh : 0 < h)
    (hf : FirstTwo q B a b)
    (hdiv : ∀ x, IsCosetLeader q (h * B) x → h * b < x → h ∣ x) :
    FirstTwo q (h * B) (h * a) (h * b) := by
  refine ⟨(scale_leader_iff hh).mpr hf.1, (scale_leader_iff hh).mpr hf.2.1,
    Nat.mul_lt_mul_of_pos_left hf.2.2.1 hh, ?_⟩
  intro x hx
  by_cases hb : x ≤ h * b
  · exact Or.inl hb
  right
  obtain ⟨y, rfl⟩ := hdiv x hx (by omega)
  have hy := (scale_leader_iff hh).mp hx
  rcases hf.2.2.2 y hy with hy | hy
  · exact (hb (Nat.mul_le_mul_left h hy)).elim
  · rw [hy]

theorem minus_threshold_bounds (q t : ℤ) (hq : 3 ≤ q) (ht : q ^ 2 ≤ t) :
    (q + 1) * (t ^ 2 + t) < 2 * (q * t ^ 2 - 1) ∧
    q * ((q + 1) * (t ^ 2 + t)) < 2 * ((q + 1) * (q * t ^ 2 - 1)) ∧
    (q - 1) * ((q + 1) * (t ^ 2 + t)) < q * (q * t ^ 2 - 1) := by
  have ht3 : 3 ≤ t := by nlinarith
  have ht0 : 0 ≤ t := by omega
  have ht2 : 0 ≤ t ^ 2 - t := by nlinarith
  have h1 : (q + 1) * (t ^ 2 + t) < 2 * (q * t ^ 2 - 1) := by
    nlinarith [mul_nonneg (show 0 ≤ q - 3 by omega) ht2]
  have h2 : q * (t ^ 2 + t) < 2 * (q * t ^ 2 - 1) := by
    nlinarith [mul_nonneg (show 0 ≤ q - 3 by omega) ht2]
  refine ⟨h1, ?_, ?_⟩
  · nlinarith [mul_pos (show 0 < q + 1 by omega)
      (show 0 < 2 * (q * t ^ 2 - 1) - q * (t ^ 2 + t) by linarith)]
  · nlinarith [mul_nonneg ht0 (show 0 ≤ t - q ^ 2 by omega)]

/- The minus-family formulas for q>=3 and m=2h+1>=5, before expanding
the natural-number expressions in the frozen statement. -/
theorem minus_ge_three_large (q h : ℕ) (hq : 3 ≤ q) (hh : 2 ≤ h) :
    FirstTwo q ((q + 1) * (q ^ (2 * h + 1) - 1))
      ((q + 1) * (q ^ (2 * h + 1) - 1 - q ^ (2 * h)))
      ((q + 1) * (q ^ (2 * h + 1) - 1 - (q ^ (2 * h) + q ^ h))) := by
  apply scaled_firstTwo_of_large_divisible (by omega : 0 < q + 1)
    (primitive_firstTwo q h (by omega) (by omega))
  intro x hl hx
  let B := q ^ (2 * h + 1) - 1
  let n := (q + 1) * B
  let D := n - x
  have hB : 0 < B := by
    have hp := Nat.le_pow (a := q) (b := 2 * h + 1) (by omega)
    dsimp [B]; omega
  have hBeq : B + 1 = q ^ (2 * h + 1) := by
    dsimp [B]; omega
  have hxl : x < n := hl.1
  have hx0 : 0 < x := by omega
  have hDn : D < n := by dsimp [D]; omega
  have hDx : D + x = n := Nat.sub_add_cancel hxl.le
  have hmax : ∀ i, (D * q ^ i) % n ≤ D := complement_max_of_leader hl hx0
  have ht : (q : ℤ) ^ 2 ≤ (q : ℤ) ^ h := by
    exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < q) hh
  have hbounds := minus_threshold_bounds (q : ℤ) ((q : ℤ) ^ h) (by exact_mod_cast hq) ht
  have hBcast : (B : ℤ) = (q : ℤ) * ((q : ℤ) ^ h) ^ 2 - 1 := by
    have hb' : (B : ℤ) + 1 = (q : ℤ) ^ (2 * h + 1) := by exact_mod_cast hBeq
    rw [pow_succ, mul_comm 2 h, pow_mul] at hb'
    nlinarith
  have hDsmall : (D : ℤ) < ((q : ℤ) + 1) * (((q : ℤ) ^ h) ^ 2 + (q : ℤ) ^ h) := by
    have hx' : (q + 1) * (B - (q ^ (2 * h) + q ^ h)) < x := hx
    have hsub : B ≤ B - (q ^ (2 * h) + q ^ h) + (q ^ (2 * h) + q ^ h) := by omega
    have hb' : n ≤ (q + 1) * (B - (q ^ (2 * h) + q ^ h)) +
        (q + 1) * (q ^ (2 * h) + q ^ h) := by
      have he := Nat.mul_le_mul_left (q + 1) hsub
      simpa only [mul_add] using he
    have hd' : D < (q + 1) * (q ^ (2 * h) + q ^ h) := by omega
    rw [mul_comm 2 h, pow_mul] at hd'
    exact_mod_cast hd'
  have hc := minus_small_max_classification (q : ℤ) B D (2 * h + 1)
    (by exact_mod_cast hq) (by exact_mod_cast hB)
    (by exact_mod_cast hBeq.symm) (by positivity) (by exact_mod_cast hDn)
    (fun i => by exact_mod_cast hmax i)
    (by rw [hBcast]; linarith [hbounds.1])
    (by rw [hBcast]; nlinarith [hbounds.2.1])
  rcases hc with hc | hc
  · have hdiv : q + 1 ∣ D := by exact_mod_cast hc
    have hnDiv : q + 1 ∣ n := dvd_mul_right (q + 1) B
    have hxDiv := Nat.dvd_sub hnDiv hdiv
    have hnDx : n - D = x := by omega
    rwa [hnDx] at hxDiv
  · rw [hBcast] at hc
    nlinarith [hbounds.2.2]

theorem binary_sparse_digit_spacing (n D : ℤ) (d a : ℕ → ℤ) (hn : 0 < n)
    (hd : ∀ i, 0 ≤ d i ∧ d i ≤ D) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1)
    (hr : ∀ i, d (i + 1) = 2 * d i - n * a i) (hD : 8 * D < 5 * n) :
    ∀ i, a i + a (i + 1) + a (i + 2) ≤ 1 := by
  intro i
  have h0 := hd i
  have h1 := hd (i + 1)
  have h2 := hd (i + 2)
  have h3 := hd (i + 3)
  have r0 := hr i
  have r1 : d (i + 2) = 2 * d (i + 1) - n * a (i + 1) := hr (i + 1)
  have r2 : d (i + 3) = 2 * d (i + 2) - n * a (i + 2) := hr (i + 2)
  have a0 : a i = 0 ∨ a i = 1 := by have := ha i; omega
  have a1 : a (i + 1) = 0 ∨ a (i + 1) = 1 := by have := ha (i + 1); omega
  have a2 : a (i + 2) = 0 ∨ a (i + 2) = 1 := by have := ha (i + 2); omega
  rcases a0 with a0 | a0 <;> rcases a1 with a1 | a1 <;> rcases a2 with a2 | a2 <;>
    rw [a0, a1, a2] <;> rw [a0] at r0 <;> rw [a1] at r1 <;> rw [a2] at r2 <;> nlinarith

/- In the binary minus family, spacing three forces the two half-blocks
of every sufficiently small orbit maximum to agree. -/
theorem binary_minus_small_classification (B D : ℤ) (m : ℕ)
    (hB : 0 < B) (hp : (2 : ℤ) ^ m = B + 1) (hD : 0 ≤ D)
    (hDn : D < 3 * B) (hmax : ∀ i : ℕ, (D * 2 ^ i) % (3 * B) ≤ D)
    (hsparse : 8 * D < 5 * (3 * B)) : 3 ∣ D := by
  let q : ℤ := 2
  have hq : 2 ≤ q := by decide
  have hwidth : D < 3 * B := hDn
  have hstep : q * D < 2 * ((q + 1) * B) := by dsimp [q]; omega
  let n := (q + 1) * B
  let d := fun i : ℕ => (D * q ^ i) % n
  let a := fun i : ℕ => q * d i / n
  let z := fun i : ℕ => (d i - d (i + m)) / B
  have hn : 0 < n := by dsimp [n]; positivity
  have hd : ∀ i, 0 ≤ d i ∧ d i ≤ D := fun i =>
    ⟨Int.emod_nonneg _ (ne_of_gt hn), hmax i⟩
  have hd0 : d 0 = D := by
    dsimp [d]; rw [pow_zero, mul_one, Int.emod_eq_of_lt hD (show D < n from hDn)]
  have ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1 := by
    intro i
    have hi := hd i
    dsimp [a]
    constructor
    · exact Int.ediv_nonneg (mul_nonneg (by omega) hi.1) hn.le
    · have he : q * d i < 2 * n := lt_of_le_of_lt (mul_le_mul_of_nonneg_left hi.2 (by omega)) hstep
      have := (Int.ediv_lt_iff_lt_mul hn).mpr he
      omega
  have hr : ∀ i, d (i + 1) = q * d i - (q + 1) * B * a i := by
    intro i
    have he : d (i + 1) = (q * d i) % n := by
      calc
        d (i + 1) = (q * (D * q ^ i)) % n := by
          dsimp [d]
          congr 1
          rw [pow_succ]
          ring
        _ = (q * d i) % n := ((Int.mod_modEq (D * q ^ i) n).mul_left q).symm
    rw [he, Int.emod_def]
  have hdz : ∀ i, d i - d (i + m) = B * z i := by
    intro i
    have hp' : Int.ModEq B (q ^ m) 1 := by
      apply Int.modEq_iff_dvd.mpr
      exact ⟨-1, by rw [hp]; ring⟩
    have hm : Int.ModEq B (d (i + m)) (d i) := by
      have hmod : ∀ j, Int.ModEq B (d j) (D * q ^ j) := fun j =>
        (Int.mod_modEq (D * q ^ j) n).of_dvd (dvd_mul_left B (q + 1))
      apply (hmod (i + m)).trans
      apply Int.ModEq.trans _ (hmod i).symm
      rw [pow_add, ← mul_assoc]
      simpa only [mul_one] using hp'.mul_left (D * q ^ i)
    exact (Int.mul_ediv_cancel_of_dvd hm.dvd).symm
  have hz : ∀ i, -2 ≤ z i ∧ z i ≤ 2 := by
    intro i
    have h0 := hd i
    have h1 := hd (i + m)
    have he := hdz i
    constructor <;> nlinarith
  have hzr : ∀ i, z (i + 1) = q * z i - (q + 1) * (a i - a (i + m)) := by
    intro i
    apply mul_left_cancel₀ (ne_of_gt hB)
    rw [← hdz (i + 1), show i + 1 + m = i + m + 1 by omega, hr i, hr (i + m)]
    calc
      _ = q * (d i - d (i + m)) - (q + 1) * B * (a i - a (i + m)) := by ring
      _ = _ := by rw [hdz i]; ring
  have hs : ∀ i, a i + a (i + 1) + a (i + 2) ≤ 1 :=
    binary_sparse_digit_spacing (3 * B) D d a hn hd ha hr hsparse
  have hz0 : z 0 = 0 := by
    apply sparse_binary_states_zero z a (fun i => a (i + m)) hz ha (fun i => ha (i + m)) hzr hs
    intro i
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs (i + m)
  have hdm : d m = D := by
    have he := hdz 0
    rw [hd0, hz0, mul_zero, zero_add] at he
    omega
  have he : Int.ModEq n (D * q ^ m) D := by
    change (D * q ^ m) % n = D % n
    rw [Int.emod_eq_of_lt hD (show D < n from hDn)]
    exact hdm
  have hnD : B * (q + 1) ∣ B * D := by
    have hh : n ∣ D * q ^ m - D := Int.dvd_neg.mp (by simpa using he.dvd)
    rw [hp, show D * (B + 1) - D = B * D by ring] at hh
    simpa only [n, mul_comm B (q + 1)] using hh
  exact (mul_dvd_mul_iff_left (ne_of_gt hB)).mp hnD

theorem minus_binary_large (h : ℕ) (hh : 3 ≤ h) :
    FirstTwo 2 (3 * (2 ^ (2 * h + 1) - 1))
      (3 * (2 ^ (2 * h + 1) - 1 - 2 ^ (2 * h)))
      (3 * (2 ^ (2 * h + 1) - 1 - (2 ^ (2 * h) + 2 ^ h))) := by
  apply scaled_firstTwo_of_large_divisible (by decide : 0 < 3)
    (primitive_firstTwo 2 h (by decide) (by omega))
  intro x hl hx
  let B := 2 ^ (2 * h + 1) - 1
  let n := 3 * B
  let D := n - x
  have hB : 0 < B := by
    have hp := Nat.le_pow (a := 2) (b := 2 * h + 1) (by omega)
    dsimp [B]; omega
  have hBeq : B + 1 = 2 ^ (2 * h + 1) := by dsimp [B]; omega
  have hxl : x < n := hl.1
  have hx0 : 0 < x := by omega
  have hDn : D < n := by dsimp [D]; omega
  have hDx : D + x = n := Nat.sub_add_cancel hxl.le
  have hmax : ∀ i, (D * 2 ^ i) % n ≤ D := complement_max_of_leader hl hx0
  have ht : (8 : ℤ) ≤ (2 : ℤ) ^ h := by
    exact_mod_cast Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hh
  have hBcast : (B : ℤ) = 2 * ((2 : ℤ) ^ h) ^ 2 - 1 := by
    have hb' : (B : ℤ) + 1 = (2 : ℤ) ^ (2 * h + 1) := by exact_mod_cast hBeq
    rw [pow_succ, mul_comm 2 h, pow_mul] at hb'
    nlinarith
  have hDsmall : (D : ℤ) < 3 * (((2 : ℤ) ^ h) ^ 2 + (2 : ℤ) ^ h) := by
    have hx' : 3 * (B - (2 ^ (2 * h) + 2 ^ h)) < x := hx
    have hsub : B ≤ B - (2 ^ (2 * h) + 2 ^ h) + (2 ^ (2 * h) + 2 ^ h) := by omega
    have hd' : D < 3 * (2 ^ (2 * h) + 2 ^ h) := by dsimp [n] at hDx; omega
    rw [mul_comm 2 h, pow_mul] at hd'
    exact_mod_cast hd'
  have hc := binary_minus_small_classification B D (2 * h + 1)
    (by exact_mod_cast hB) (by exact_mod_cast hBeq.symm) (by positivity)
    (by exact_mod_cast hDn) (fun i => by exact_mod_cast hmax i)
    (by rw [hBcast]; nlinarith)
  have hdiv : 3 ∣ D := by exact_mod_cast hc
  have hnDiv : 3 ∣ n := dvd_mul_right 3 B
  have hxDiv := Nat.dvd_sub hnDiv hdiv
  have hnDx : n - D = x := by omega
  rwa [hnDx] at hxDiv

/- The alternating orbit supplies the exceptional second place at m=3. -/
theorem minus_three (q : ℕ) (hq : 3 ≤ q) :
    FirstTwo q ((q + 1) * (q ^ 3 - 1))
      ((q + 1) * (q ^ 3 - 1 - q ^ 2))
      ((q + 1) * (q ^ 3 - 1) - q * (q ^ 2 + q + 1)) := by
  let B := q ^ 3 - 1
  let C := q ^ 2 + q + 1
  let n := (q + 1) * B
  have hB : B + 1 = q ^ 3 := by dsimp [B]; have := Nat.le_pow (a := q) (b := 3) (by decide); omega
  have hBC : B = (q - 1) * C := by
    have hq1 : q - 1 + 1 = q := by omega
    dsimp [C]
    nlinarith only [hB, congrArg (fun t => t * (q ^ 2 + q + 1)) hq1]
  have hC : 0 < C := by dsimp [C]; positivity
  have hnC : n = (q ^ 2 - 1) * C := by
    have hq1 : q - 1 + 1 = q := by omega
    have hq2 : q ^ 2 - 1 + 1 = q ^ 2 := Nat.sub_add_cancel (by nlinarith)
    dsimp [n]; rw [hBC, ← mul_assoc]; congr 1; nlinarith only [hq1, hq2]
  have hq2 : q ^ 2 - 1 + 1 = q ^ 2 := Nat.sub_add_cancel (by nlinarith)
  have hqC : 0 < q * C := by positivity
  have hBq : B + C = q * C := by
    have hq1 : q - 1 + 1 = q := by omega
    rw [hBC]
    nlinarith only [congrArg (fun t => t * C) hq1]
  have hqn : n + C = q ^ 2 * C := by
    rw [hnC]
    nlinarith only [congrArg (fun t => t * C) hq2]
  have hBlarge : q ^ 2 + q ≤ B := by
    have hp : 3 * q ^ 2 ≤ q ^ 3 := by
      calc
        3 * q ^ 2 ≤ q * q ^ 2 := Nat.mul_le_mul_right _ hq
        _ = q ^ 3 := by ring
    nlinarith only [hq, hp, hB]
  have hbpos : q * C < n := by
    rw [hnC]
    exact Nat.mul_lt_mul_of_pos_right (by nlinarith only [hq, hq2]) hC
  have hcle : C ≤ q * C := by nlinarith only [hq, hC]
  have hcpos : C < n := by omega
  have hb : n - q * C + q * C = n := Nat.sub_add_cancel hbpos.le
  have hc : n - C + C = n := Nat.sub_add_cancel hcpos.le
  have hlb : IsCosetLeader q n (n - q * C) := by
    apply leader_of_two_cycle (b := n - C) (by omega) (by omega)
    · have hq' : q - 2 + 2 = q := by omega
      have he : (n - q * C) * q = (n - C) + (q - 2) * n := by
        nlinarith only [congrArg (fun t => t * q) hb, hc, hqn,
          congrArg (fun t => t * n) hq']
      rw [he, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega : n - C < n)]
    · have hq' : q - 1 + 1 = q := by omega
      have he : (n - C) * q = (n - q * C) + (q - 1) * n := by
        nlinarith only [congrArg (fun t => t * q) hc, hb,
          congrArg (fun t => t * n) hq']
      rw [he, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega : n - q * C < n)]
  have hf := primitive_firstTwo q 1 (by omega) (by decide)
  norm_num only at hf
  have hA : B - q ^ 2 + q ^ 2 = B := by
    omega
  have hAb : n - q * C < (q + 1) * (B - q ^ 2) := by
    have haDef : (q + 1) * (B - q ^ 2) + (q + 1) * q ^ 2 = n := by
      dsimp [n]
      nlinarith only [congrArg (fun t => (q + 1) * t) hA]
    have hdalt : q * C = (q + 1) * q ^ 2 + q := by dsimp [C]; ring
    omega
  refine ⟨(scale_leader_iff (by omega : 0 < q + 1)).mpr hf.1, hlb, hAb, ?_⟩
  intro x hl
  by_cases hxb : x ≤ n - q * C
  · exact Or.inl hxb
  right
  have hxlt : x < n := hl.1
  have hx0 : 0 < x := by omega
  let D := n - x
  have hDn : D < n := by dsimp [D]; omega
  have hDx : D + x = n := Nat.sub_add_cancel hxlt.le
  have hDsmall : D < q * C := by omega
  have hmax := complement_max_of_leader hl hx0
  have hclass := minus_small_max_classification (q : ℤ) B D 3
    (by exact_mod_cast hq) (by exact_mod_cast (show 0 < B by omega))
    (by exact_mod_cast hB.symm) (by positivity) (by exact_mod_cast hDn)
    (fun i => by exact_mod_cast hmax i)
    (by exact_mod_cast (show D < 2 * B by nlinarith only [hDsmall, hBq, hq, hC]))
    (by exact_mod_cast (show q * D < 2 * ((q + 1) * B) by
      have he := Nat.mul_lt_mul_of_pos_left hDsmall (by omega : 0 < q)
      change q * D < 2 * n
      nlinarith only [he, hqn, hcpos]))
  have hdiv : q + 1 ∣ D := by
    rcases hclass with hc | hc
    · exact_mod_cast hc
    · have hbc' : (B : ℤ) = ((q : ℤ) - 1) * (C : ℤ) := by
        have he : (B : ℤ) = ((q - 1 : ℕ) : ℤ) * (C : ℤ) := by exact_mod_cast hBC
        simpa only [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one] using he
      have hd' : (D : ℤ) < (q : ℤ) * (C : ℤ) := by exact_mod_cast hDsmall
      have hq' : (3 : ℤ) ≤ q := by exact_mod_cast hq
      rw [hbc'] at hc
      have he : (D : ℤ) = (q : ℤ) * (C : ℤ) := by
        apply mul_left_cancel₀ (show (q : ℤ) - 1 ≠ 0 by omega)
        calc
          ((q : ℤ) - 1) * (D : ℤ) = (q : ℤ) * (((q : ℤ) - 1) * (C : ℤ)) := hc
          _ = _ := by ring
      omega
  have hxDiv := Nat.dvd_sub (show q + 1 ∣ n from dvd_mul_right (q + 1) B) hdiv
  have hnx : n - D = x := by omega
  rw [hnx] at hxDiv
  obtain ⟨y, hxy⟩ := hxDiv
  have hly : IsCosetLeader q B y := by
    apply (scale_leader_iff (by omega : 0 < q + 1)).mp
    rwa [hxy] at hl
  rcases hf.2.2.2 y hly with hy | hy
  · have hsub : B ≤ B - (q ^ 2 + q) + (q ^ 2 + q) := by omega
    have hgap : (q + 1) * (B - (q ^ 2 + q)) ≤ n - q * C := by
      have he : B - (q ^ 2 + q) + (q ^ 2 + q) = B := Nat.sub_add_cancel hBlarge
      have hc' : q * C ≤ (q + 1) * (q ^ 2 + q) := by
        dsimp [C]
        nlinarith only [Nat.zero_le (q ^ 2)]
      apply Nat.le_sub_of_add_le
      calc
        (q + 1) * (B - (q ^ 2 + q)) + q * C ≤
            (q + 1) * (B - (q ^ 2 + q)) + (q + 1) * (q ^ 2 + q) := Nat.add_le_add_left hc' _
        _ = n := by rw [← Nat.mul_add, he]
    have hyb : y ≤ B - (q ^ 2 + q) := by simpa only [pow_one] using hy
    have hy' := Nat.mul_le_mul_left (q + 1) hyb
    rw [← hxy] at hy'
    omega
  · rw [hxy, hy]

theorem primitive_deficiency_bound (q h : ℕ) (hq : 2 ≤ q) (hh : 0 < h) :
    q ^ (2 * h) + q ^ h < q ^ (2 * h + 1) - 1 := by
  have hs : 2 ≤ q ^ h := le_trans hq (Nat.le_pow hh)
  have hsq : q ^ (2 * h) = (q ^ h) ^ 2 := by rw [mul_comm 2 h, pow_mul]
  have hQ : q ^ (2 * h + 1) = q ^ (2 * h) * q := pow_succ _ _
  have hB : q ^ (2 * h + 1) - 1 + 1 = q ^ (2 * h + 1) :=
    Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))
  nlinarith

theorem minus_formula_one (q h : ℕ) (hq : 2 ≤ q) (hh : 0 < h) :
    minusDeltaOne q (2 * h + 1) = (q + 1) * (q ^ (2 * h + 1) - 1 - q ^ (2 * h)) := by
  have hlt := primitive_deficiency_bound q h hq hh
  have hB : q ^ (2 * h + 1) - 1 + 1 = q ^ (2 * h + 1) :=
    Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))
  have hA : q ^ (2 * h + 1) - 1 - q ^ (2 * h) + q ^ (2 * h) + 1 = q ^ (2 * h) * q := by
    rw [← pow_succ]
    omega
  have he : q ^ (2 * h + 1 + 1) =
      (q + 1) * (q ^ (2 * h + 1) - 1 - q ^ (2 * h)) + q ^ (2 * h) + q + 1 := by
    calc
      q ^ (2 * h + 1 + 1) = q ^ (2 * h) * q * q := by rw [pow_succ, pow_succ]
      _ = _ := by nlinarith only [congrArg (fun t => (q + 1) * t) hA]
  simp only [minusDeltaOne, Nat.add_sub_cancel]
  rw [he]
  omega

theorem minus_formula_two_large (q h : ℕ) (hq : 2 ≤ q) (hh : 2 ≤ h) :
    minusDeltaTwo q (2 * h + 1) =
      (q + 1) * (q ^ (2 * h + 1) - 1 - (q ^ (2 * h) + q ^ h)) := by
  have hlt := primitive_deficiency_bound q h hq (by omega)
  have hB : q ^ (2 * h + 1) - 1 + 1 = q ^ (2 * h + 1) :=
    Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))
  have hC : q ^ (2 * h + 1) - 1 - (q ^ (2 * h) + q ^ h) +
      q ^ (2 * h) + q ^ h + 1 = q ^ (2 * h) * q := by
    rw [← pow_succ]
    omega
  have hq2 : q ^ 2 - 1 + 1 = q ^ 2 := Nat.sub_add_cancel (by nlinarith)
  have he : (q ^ 2 - 1) * q ^ (2 * h) =
      (q + 1) * (q ^ (2 * h + 1) - 1 - (q ^ (2 * h) + q ^ h)) +
        (q + 1) * (q ^ h + 1) := by
    nlinarith only [congrArg (fun t => (q + 1) * t) hC,
      congrArg (fun t => t * q ^ (2 * h)) hq2]
  rw [minusDeltaTwo, if_neg (by omega : 2 * h + 1 ≠ 3),
    show 2 * h + 1 - 1 = 2 * h by omega, show 2 * h / 2 = h by omega, he]
  omega

theorem minus_formula_two_three (q : ℕ) (hq : 2 ≤ q) :
    minusDeltaTwo q 3 = (q + 1) * (q ^ 3 - 1) - q * (q ^ 2 + q + 1) := by
  have hq3 : q ^ 3 - 1 + 1 = q ^ 3 :=
    Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))
  have hq2 : q ^ 2 - 1 + 1 = q ^ 2 := Nat.sub_add_cancel (by nlinarith)
  have he : (q + 1) * (q ^ 3 - 1) + (2 * q + 1) =
      (q ^ 2 - 1) * q ^ 2 + q * (q ^ 2 + q + 1) := by
    nlinarith only [congrArg (fun t => (q + 1) * t) hq3,
      congrArg (fun t => t * q ^ 2) hq2]
  rw [minusDeltaTwo, if_pos rfl]
  omega

/- The complete minus family, for every integer q>=2. -/
theorem minus_firstTwo_all (q m : ℕ) (hq : 2 ≤ q) (hm : Odd m) (hm3 : 3 ≤ m) :
    FirstTwo q ((q + 1) * (q ^ m - 1)) (minusDeltaOne q m) (minusDeltaTwo q m) := by
  obtain ⟨h, rfl⟩ := hm
  have hh : 0 < h := by omega
  by_cases hh1 : h = 1
  · subst h
    norm_num only
    by_cases hq2 : q = 2
    · subst q
      convert binary_small_cases.1 using 1 <;> norm_num [minusDeltaOne, minusDeltaTwo]
    · rw [minus_formula_two_three q hq]
      have he := minus_formula_one q 1 hq (by decide)
      norm_num only at he
      rw [he]
      exact minus_three q (by omega)
  · rw [minus_formula_one q h hq hh, minus_formula_two_large q h hq (by omega)]
    by_cases hq2 : q = 2
    · subst q
      by_cases hh2 : h = 2
      · subst h
        convert binary_small_cases.2 using 1 <;> norm_num
      · exact minus_binary_large h (by omega)
    · exact minus_ge_three_large q h (by omega) (by omega)

theorem primePower_ge_two {q : ℕ} (hq : IsPrimePower q) : 2 ≤ q := by
  obtain ⟨p, e, hp, he, rfl⟩ := hq
  exact le_trans hp.two_le (Nat.le_pow he)

theorem conjecturesA_minus :
    ∀ q m : ℕ, IsPrimePower q → Odd m → 3 ≤ m →
      FirstTwo q ((q + 1) * (q ^ m - 1)) (minusDeltaOne q m) (minusDeltaTwo q m) := by
  intro q m hq hm hm3
  exact minus_firstTwo_all q m (primePower_ge_two hq) hm hm3

/- The first radius bound for an actual upper-half orbit when q=3 mod 4. -/
theorem upper_q3_radius_lower (q N y : ℤ) (m : ℕ) (hq : 0 ≤ q)
    (hq4 : q % 4 = 3) (hN : 0 < N) (hp : q ^ m = N - 1)
    (hy : N < y) (hl : ∀ i : ℕ, y ≤ (y * q ^ i) % (2 * N)) :
    2 * N ≤ (q + 1) * (3 * N - 2 * y) := by
  have href := upper_orbit_reflection q N y m hN hp hy hl
  have hyhi : y < 2 * N := lt_of_le_of_lt (hl 0) (Int.emod_lt_of_pos _ (by omega))
  have hr0 : (y * q ^ 0) % (2 * N) = y := by
    simp only [pow_zero, mul_one, Int.emod_eq_of_lt (by omega : 0 ≤ y) hyhi]
  have hbound := (href 0).2.2
  rw [hr0] at hbound
  let r := (y * q) % (2 * N)
  have hrlo : y ≤ r := by simpa only [pow_one] using hl 1
  have hrhi : r ≤ 3 * N - y := by simpa only [pow_one] using (href 1).2.2
  have he : q * (2 * y - 3 * N) - (2 * r - 3 * N) =
      (2 * ((y * q) / (2 * N) - 3 * (q / 4) - 2) + 1) * (2 * N) := by
    have hq' : q - 1 = 4 * (q / 4) + 2 := by omega
    change q * (2 * y - 3 * N) - (2 * ((y * q) % (2 * N)) - 3 * N) = _
    rw [Int.emod_def]
    calc
      _ = 4 * N * ((y * q) / (2 * N)) - 3 * N * (q - 1) := by ring
      _ = _ := by rw [hq']; ring
  exact odd_affine_radius_bound q (2 * N) (3 * N - 2 * y)
    (2 * y - 3 * N) (2 * r - 3 * N) ((y * q) / (2 * N) - 3 * (q / 4) - 2)
    hq (by omega) (by omega) (abs_le.mpr ⟨by omega, by omega⟩)
    (abs_le.mpr ⟨by omega, by omega⟩) he

theorem q3_candidate_leader (k s : ℕ) (hs : 0 < s) :
    IsCosetLeader (4 * k + 3) (16 * (k + 1) * s) ((12 * k + 10) * s) := by
  have ha : (12 * k + 10) * s < 16 * (k + 1) * s := by nlinarith
  have hb : (12 * k + 14) * s < 16 * (k + 1) * s := by nlinarith
  apply leader_of_two_cycle ha (b := (12 * k + 14) * s) (by nlinarith)
  · have he : (12 * k + 10) * s * (4 * k + 3) =
        (12 * k + 14) * s + (3 * k + 1) * (16 * (k + 1) * s) := by ring
    rw [he, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
  · have he : (12 * k + 14) * s * (4 * k + 3) =
        (12 * k + 10) * s + (3 * k + 2) * (16 * (k + 1) * s) := by ring
    rw [he, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha]

theorem q3_odd_power_mod {q m : ℕ} (hq : q % 4 = 3) (hm : Odd m) : q ^ m % 4 = 3 := by
  obtain ⟨t, rfl⟩ := hm
  have hs : q ^ 2 % 4 = 1 := by norm_num [pow_two, Nat.mul_mod, hq]
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod (q ^ 2), hs, one_pow, hq]
  norm_num

/- The largest leader in the q=3 mod 4 plus family. -/
theorem plus_q3_largest (q m : ℕ) (hq4 : q % 4 = 3) (hm : Odd m) :
    IsCosetLeader q ((q + 1) * (q ^ m + 1)) (plusDeltaOne q m) ∧
      ∀ x, IsCosetLeader q ((q + 1) * (q ^ m + 1)) x → x ≤ plusDeltaOne q m := by
  let k := q / 4
  have hqk : q = 4 * k + 3 := by omega
  have hqo : Odd q := ⟨2 * k + 1, by omega⟩
  have hpow := q3_odd_power_mod hq4 hm
  let s := (q ^ m + 1) / 4
  have hNs : q ^ m + 1 = 4 * s := by dsimp [s]; omega
  have hs : 0 < s := by omega
  have hn : (q + 1) * (q ^ m + 1) = 16 * (k + 1) * s := by rw [hNs, hqk]; ring
  have ha : plusDeltaOne q m = (12 * k + 10) * s := by
    rw [plusDeltaOne, if_neg (by omega : q % 4 ≠ 1)]
    have he : (3 * q + 1) * (q ^ m + 1) = (12 * k + 10) * s * 4 := by
      rw [hNs, hqk]; ring
    rw [he, Nat.mul_div_cancel _ (by decide : 0 < 4)]
  constructor
  · rw [ha, hn, hqk]; exact q3_candidate_leader k s hs
  intro x hl
  by_contra hxa
  have hxhi : (q + 1) * (q ^ m + 1) < 2 * x := by rw [hn]; rw [ha] at hxa; nlinarith
  obtain ⟨h, y, hqh, hxy, hh, hly, hy⟩ := plus_high_reduction hqo hm hl hxhi
  have hhk : h = 2 * (k + 1) := by omega
  have hgap := upper_q3_radius_lower (q : ℤ) ((q : ℤ) ^ m + 1) y m
    (by positivity) (by exact_mod_cast hq4) (by positivity) (by ring)
    (by exact_mod_cast hy) (fun i => by exact_mod_cast hly.2 i)
  have hNs' : (q : ℤ) ^ m + 1 = 4 * (s : ℤ) := by exact_mod_cast hNs
  have hqk' : (q : ℤ) = 4 * (k : ℤ) + 3 := by exact_mod_cast hqk
  have hxy' : (x : ℤ) = 2 * ((k : ℤ) + 1) * (y : ℤ) := by
    rw [hhk] at hxy
    exact_mod_cast hxy
  have hxa' : (12 * (k : ℤ) + 10) * (s : ℤ) < (x : ℤ) := by
    rw [ha] at hxa
    exact_mod_cast (Nat.lt_of_not_ge hxa)
  rw [hNs', hqk'] at hgap
  nlinarith

theorem conjecturesA_plus_largest :
    ∀ q m : ℕ, IsPrimePower q → Odd q → Odd m → 3 ≤ m →
      IsCosetLeader q ((q + 1) * (q ^ m + 1)) (plusDeltaOne q m) ∧
        ∀ x, IsCosetLeader q ((q + 1) * (q ^ m + 1)) x → x ≤ plusDeltaOne q m := by
  intro q m hq hqo hm _hm3
  have hq4 : q % 4 = 1 ∨ q % 4 = 3 := by have := Nat.odd_iff.mp hqo; omega
  rcases hq4 with hq4 | hq4
  · have hf := plus_q1_firstTwo q m (primePower_ge_two hq) hq4 hm
    refine ⟨hf.1, ?_⟩
    intro x hx
    rcases hf.2.2.2 x hx with hx | hx
    · exact le_trans hx hf.2.2.1.le
    · exact hx.le
  · exact plus_q3_largest q m hq4 hm

/- The complete q=1 mod 4 branch with the hypotheses of the frozen statement. -/
theorem conjecturesA_plus_q1 :
    ∀ q m : ℕ, IsPrimePower q → Odd q → Odd m → 3 ≤ m → q % 4 = 1 →
      FirstTwo q ((q + 1) * (q ^ m + 1)) (plusDeltaOne q m) (plusDeltaTwo q m) := by
  intro q m hq _hqo hm _hm3 hq4
  exact plus_q1_firstTwo q m (primePower_ge_two hq) hq4 hm


theorem sign_alternates {a b : ℤ} (ha : a = 1 ∨ a = -1)
    (hb : b = 1 ∨ b = -1) (hne : a ≠ b) : b = -a := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> omega

theorem alternating_segment (s : ℕ → ℤ) (a k : ℕ)
    (h : ∀ t < k, s (a + t + 1) = -s (a + t)) :
    s (a + k) = (-1) ^ k * s a := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show a + (k + 1) = a + k + 1 by omega, h k (by omega),
      ih (fun t ht => h t (by omega)), pow_succ]
    ring

/- An antiperiodic sign sequence which has a defect has two consecutive
 defects at odd distance at most m-2. -/
theorem odd_defect_gap (s : ℕ → ℤ) (m : ℕ) (hm : Odd m)
    (hs : ∀ i, s i = 1 ∨ s i = -1)
    (ha : ∀ i, s (i + m) = -s i)
    (hd : ∃ i, s i = s (i + 1)) :
    ∃ i d, Odd d ∧ 0 < d ∧ d + 2 ≤ m ∧
      s i = s (i + 1) ∧ s (i + d) = s (i + d + 1) ∧
      s (i + d) = s i ∧
      ∀ t, 0 < t → t < d → s (i + t + 1) = -s (i + t) := by
  classical
  obtain ⟨a, had⟩ := hd
  let t := fun j => s (a + j)
  have ht : ∀ i, t i = 1 ∨ t i = -1 := fun i => hs (a + i)
  have ht0 : t 0 = t 1 := by simpa [t] using had
  have hta : ∀ i, t (i + m) = -t i := by
    intro i
    simpa only [t, Nat.add_assoc] using ha (a + i)
  have hex : ∃ j, Odd j ∧ t j = t (j + 1) := by
    refine ⟨m, hm, ?_⟩
    have h0 := hta 0
    have h1 := hta 1
    simp only [zero_add] at h0
    rw [show m + 1 = 1 + m by omega, h1, h0, ht0]
  let j := Nat.find hex
  have hj := Nat.find_spec hex
  change Odd j ∧ t j = t (j + 1) at hj
  have hjm : j ≤ m := Nat.find_min' hex ⟨hm, by
    have h0 := hta 0
    have h1 := hta 1
    simp only [zero_add] at h0
    rw [show m + 1 = 1 + m by omega, h1, h0, ht0]⟩
  have hj0 : 0 < j := hj.1.pos
  let k := Nat.findGreatest (fun i => t i = t (i + 1)) (j - 1)
  have hkj : k < j := lt_of_le_of_lt (Nat.findGreatest_le _) (by omega)
  have hkd : t k = t (k + 1) := Nat.findGreatest_spec (P := fun i => t i = t (i + 1)) (by omega : 0 ≤ j - 1) ht0
  have hke : Even k := by
    by_contra he
    have hko := Nat.not_even_iff_odd.mp he
    exact Nat.find_min hex hkj ⟨hko, hkd⟩
  let d := j - k
  have hd0 : 0 < d := by omega
  have hdodd : Odd d := by
    rw [Nat.odd_iff] at hj
    have hk2 := Nat.even_iff.mp hke
    exact Nat.odd_iff.mpr (by omega)
  have hkjd : k + d = j := by omega
  have halt : ∀ u, 0 < u → u < d → t (k + u + 1) = -t (k + u) := by
    intro u hu hud
    apply sign_alternates (ht _) (ht _)
    exact Nat.findGreatest_is_greatest (by omega : k < k + u) (by omega : k + u ≤ j - 1)
  have hlast : t j = t k := by
    have he := alternating_segment t (k + 1) (d - 1) (by
      intro u hu
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        halt (u + 1) (by omega) (by omega))
    have hdEven : Even (d - 1) := Nat.even_iff.mpr (by have := Nat.odd_iff.mp hdodd; omega)
    rw [hdEven.neg_one_pow, one_mul, ← hkd,
      show k + 1 + (d - 1) = j by omega] at he
    exact he
  have hdm : d + 2 ≤ m := by
    have hdp : d ≤ m := by omega
    by_contra h
    have hdEq : d = m := by
      have := Nat.odd_iff.mp hdodd
      have := Nat.odd_iff.mp hm
      omega
    have hk0 : k = 0 := by omega
    have hjEq : j = m := by omega
    have hh := hta 0
    rw [hk0, hjEq] at hlast
    have := ht 0
    simp only [zero_add] at hh
    omega
  refine ⟨a + k, d, hdodd, hd0, hdm, ?_, ?_, ?_, ?_⟩
  · simpa only [t, Nat.add_assoc] using hkd
  · simpa only [t, ← hkjd, Nat.add_assoc] using hj.2
  · simpa only [t, ← hkjd, Nat.add_assoc] using hlast
  · intro u hu hud
    simpa only [t, Nat.add_assoc] using halt u hu hud

theorem geometric_segment (q : ℤ) (u : ℕ → ℤ) (a k : ℕ)
    (h : ∀ t < k, u (a + t + 1) = q * u (a + t)) :
    u (a + k) = q ^ k * u a := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show a + (k + 1) = a + k + 1 by omega, h k (by omega),
      ih (fun t ht => h t (by omega)), pow_succ]
    ring

/- The arithmetic inequality supplied by two defects with an alternating
segment between them. -/
theorem defect_block_bound (q B R : ℤ) (w s : ℕ → ℤ) (d : ℕ)
    (hq : 0 ≤ q) (hd : 0 < d)
    (hs : s 0 = 1 ∨ s 0 = -1)
    (hb : ∀ i, -R ≤ w i ∧ w i ≤ R)
    (hr : ∀ i, w (i + 1) = q * w i - B * s i)
    (h0 : s 0 = s 1) (hd0 : s d = s 0) (hd1 : s d = s (d + 1))
    (halt : ∀ t, 0 < t → t < d → s (t + 1) = -s t) :
    B * (q ^ (d + 2) + 2 * q ^ (d + 1) + 2 * q + 1) ≤
      (q ^ (d + 2) + 1) * (q + 1) * R := by
  let u := fun i => (q + 1) * w i - B * s i
  have hg := geometric_segment q u 1 (d - 1) (by
    intro t ht
    dsimp [u]
    rw [hr, halt (1 + t) (by omega) (by omega)]
    ring)
  dsimp [u] at hg
  rw [show 1 + (d - 1) = d by omega, hd0, ← h0, hr 0] at hg
  have hq1 : q ^ (d + 1) = q ^ (d - 1) * q ^ 2 := by
    rw [← pow_add]; congr 1; omega
  have hq2 : q ^ (d + 2) = q ^ (d - 1) * q ^ 3 := by
    rw [← pow_add]; congr 1; omega
  have he : (q + 1) * w (d + 2) =
      q ^ (d + 2) * (q + 1) * w 0 -
        B * s 0 * (q ^ (d + 2) + 2 * q ^ (d + 1) + 2 * q + 1) := by
    rw [show d + 2 = (d + 1) + 1 by omega, hr, hr d, ← hd1, hd0, hq1, hq2]
    linear_combination q ^ 2 * hg
  have hpow : 0 ≤ q ^ (d + 2) * (q + 1) := by positivity
  have b0 := hb 0
  have be := hb (d + 2)
  rcases hs with hs | hs
  · rw [hs, mul_one] at he
    nlinarith only [he, b0, be,
      mul_nonneg hpow (show 0 ≤ R - w 0 by omega),
      mul_nonneg (show 0 ≤ q + 1 by omega) (show 0 ≤ w (d + 2) + R by omega)]
  · rw [hs] at he
    nlinarith only [he, b0, be,
      mul_nonneg hpow (show 0 ≤ R + w 0 by omega),
      mul_nonneg (show 0 ≤ q + 1 by omega) (show 0 ≤ R - w (d + 2) by omega)]

/- Short odd defect blocks force at least the claimed second radius. -/
theorem short_block_radius (q K R : ℤ) (m d : ℕ) (hq : 3 ≤ q)
    (hK : 0 < K) (hd : d + 2 ≤ m)
    (hb : K * (q ^ m + 1) * (q ^ (d + 2) + 2 * q ^ (d + 1) + 2 * q + 1) ≤
      (q ^ (d + 2) + 1) * (q + 1) * R) :
    K * (q ^ m + 1 + 2 * (q ^ (m - 1) + q)) ≤ (q + 1) * R := by
  have ht : q ^ (d + 1) ≤ q ^ (m - 1) := pow_le_pow_right₀ (by omega) (by omega)
  have hm : q ^ m = q ^ (m - 1) * q := by rw [← pow_succ]; congr 1; omega
  have he : (q ^ m + 1) * (q ^ (d + 2) + 2 * q ^ (d + 1) + 2 * q + 1) -
      (q ^ (d + 2) + 1) * (q ^ m + 1 + 2 * (q ^ (m - 1) + q)) =
      2 * (q ^ 2 - 1) * (q ^ (m - 1) - q ^ (d + 1)) := by
    rw [hm, pow_succ q (d + 1)]
    ring
  have hle : (q ^ (d + 2) + 1) * (q ^ m + 1 + 2 * (q ^ (m - 1) + q)) ≤
      (q ^ m + 1) * (q ^ (d + 2) + 2 * q ^ (d + 1) + 2 * q + 1) := by
    nlinarith only [he, mul_nonneg (show 0 ≤ 2 * (q ^ 2 - 1) by nlinarith) (sub_nonneg.mpr ht)]
  have hleK := mul_le_mul_of_nonneg_left hle hK.le
  have hp : 0 < q ^ (d + 2) + 1 := by positivity
  apply (mul_le_mul_iff_right₀ hp).mp
  nlinarith only [hleK, hb]

theorem signed_radius_gap (q K R : ℤ) (w s : ℕ → ℤ) (m : ℕ)
    (hq : 3 ≤ q) (hK : 0 < K) (hm : Odd m)
    (hs : ∀ i, s i = 1 ∨ s i = -1)
    (ha : ∀ i, s (i + m) = -s i)
    (hb : ∀ i, -R ≤ w i ∧ w i ≤ R) (hw0 : w 0 = -R)
    (hr : ∀ i, w (i + 1) = q * w i - K * (q ^ m + 1) * s i)
    (hsmall : (q + 1) * R < K * (q ^ m + 1 + 2 * (q ^ (m - 1) + q))) :
    (q + 1) * R = K * (q ^ m + 1) := by
  by_cases hdef : ∃ i, s i = s (i + 1)
  · obtain ⟨i, d, _hdo, hd, hdm, h0, hd0, hd1, halt⟩ := odd_defect_gap s m hm hs ha hdef
    have hh := defect_block_bound q (K * (q ^ m + 1)) R
      (fun t => w (i + t)) (fun t => s (i + t)) d (by omega) hd
      (by simpa using hs i) (fun t => hb (i + t))
      (fun t => by simpa only [Nat.add_assoc] using hr (i + t))
      (by simpa using h0) (by simpa using hd1) hd0
      (fun t ht htd => by simpa only [Nat.add_assoc] using halt t ht htd)
    have hbound := short_block_radius q K R m d hq hK hdm hh
    omega
  · have halt : ∀ i, s (i + 1) = -s i := by
      intro i
      exact sign_alternates (hs i) (hs (i + 1)) (fun he => hdef ⟨i, he⟩)
    let B := K * (q ^ m + 1)
    let u := fun i => (q + 1) * w i - B * s i
    have hR : 0 ≤ R := by have := hb 0; omega
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hu : ∀ i, |u i| ≤ (q + 1) * R + B := by
      intro i
      apply abs_le.mpr
      have hi := hb i
      dsimp [u]
      rcases hs i with he | he <;> rw [he] <;> constructor <;>
        nlinarith [mul_nonneg (show 0 ≤ q + 1 by omega) (show 0 ≤ R - w i by omega),
          mul_nonneg (show 0 ≤ q + 1 by omega) (show 0 ≤ R + w i by omega)]
    have he := bounded_geometric_zero q ((q + 1) * R + B) u (by omega) (by positivity) hu (by
      intro i
      dsimp [u, B]
      rw [hr, halt]
      ring)
    dsimp [u, B] at he
    rw [hw0] at he
    rcases hs 0 with hs0 | hs0 <;> rw [hs0] at he
    · have hpos : 0 < K * (q ^ m + 1) := by positivity
      nlinarith [mul_nonneg (show 0 ≤ q + 1 by omega) hR]
    · nlinarith only [he]

theorem odd_step_is_signed (q B R w u k : ℤ) (hq : 0 ≤ q) (hB : 0 < B)
    (hw : -R ≤ w ∧ w ≤ R) (hu : -R ≤ u ∧ u ≤ R)
    (hR : R < B) (hsmall : (q + 1) * R < 2 * B)
    (he : q * w - u = (2 * k + 1) * B) :
    w ≠ 0 ∧ u = q * w - B * (if 0 < w then 1 else -1) := by
  have hlo := mul_le_mul_of_nonneg_left hw.1 hq
  have hhi := mul_le_mul_of_nonneg_left hw.2 hq
  have hk : k = 0 ∨ k = -1 := by
    by_cases hk0 : 0 ≤ k
    · left
      by_contra hh
      have hk1 : 1 ≤ k := by omega
      nlinarith
    · right
      by_contra hh
      have hk2 : k ≤ -2 := by omega
      nlinarith
  rcases hk with rfl | rfl
  · have hwpos : 0 < w := by
      by_contra hh
      have hh' := mul_nonpos_of_nonneg_of_nonpos hq (show w ≤ 0 by omega)
      nlinarith
    exact ⟨ne_of_gt hwpos, by rw [if_pos hwpos]; nlinarith only [he]⟩
  · have hwneg : w < 0 := by
      by_contra hh
      have hh' := mul_nonneg hq (show 0 ≤ w by omega)
      nlinarith
    exact ⟨ne_of_lt hwneg, by rw [if_neg (by omega : ¬0 < w)]; nlinarith only [he]⟩

/- The exclusion of intermediate radii, applied directly to multiplication
orbits in the upper half. -/
theorem upper_q3_radius_gap (q N y : ℤ) (m : ℕ) (hq : 3 ≤ q)
    (hq4 : q % 4 = 3) (hm : Odd m) (hm3 : 3 ≤ m)
    (hN : N = q ^ m + 1) (hy : N < y)
    (hl : ∀ i : ℕ, y ≤ (y * q ^ i) % (2 * N))
    (hsmall : (q + 1) * (3 * N - 2 * y) <
      2 * (N + 2 * (q ^ (m - 1) + q))) :
    (q + 1) * (3 * N - 2 * y) = 2 * N := by
  have hNpos : 0 < N := by rw [hN]; positivity
  have href := upper_orbit_reflection q N y m hNpos (by omega) hy hl
  let r := fun i => (y * q ^ i) % (2 * N)
  let w := fun i => 2 * r i - 3 * N
  let R := 3 * N - 2 * y
  let s := fun i => if 0 < w i then (1 : ℤ) else -1
  have hr0 : r 0 = y := by
    dsimp [r]
    rw [pow_zero, mul_one, Int.emod_eq_of_lt (by omega)
      (lt_of_le_of_lt (by simpa using hl 0) (Int.emod_lt_of_pos y (by omega)))]
  have hw0 : w 0 = -R := by dsimp [w, R]; rw [hr0]; ring
  have hb : ∀ i, -R ≤ w i ∧ w i ≤ R := by
    intro i
    have hlo := hl i
    have hhi := (href i).2.2
    change y ≤ r i at hlo
    change r i ≤ 3 * N - y at hhi
    dsimp [w, R]
    constructor <;> omega
  have hR : R < 2 * N := by dsimp [R]; omega
  have hpow : q ^ m = q ^ (m - 1) * q := by rw [← pow_succ]; congr 1; omega
  have hT : q ^ 2 ≤ q ^ (m - 1) := pow_le_pow_right₀ (by omega) (by omega)
  have haux : 2 * (q ^ (m - 1) + q) < N := by
    rw [hN, hpow]
    nlinarith [mul_nonneg (show 0 ≤ q - 3 by omega) (show 0 ≤ q ^ (m - 1) by positivity)]
  have hRsmall : (q + 1) * R < 2 * (2 * N) := by dsimp [R]; omega
  have hsteps : ∀ i, w i ≠ 0 ∧ w (i + 1) = q * w i - (2 * N) * s i := by
    intro i
    have hstep : r (i + 1) = (q * r i) % (2 * N) := by
      dsimp [r]
      rw [pow_succ]
      have he := ((Int.mod_modEq (y * q ^ i) (2 * N)).mul_left q).symm
      convert he.eq using 1
      congr 1
      ring
    apply odd_step_is_signed q (2 * N) R (w i) (w (i + 1))
      ((q * r i) / (2 * N) - 3 * (q / 4) - 2)
      (by omega) (by omega) (hb i) (hb (i + 1)) hR hRsmall
    have hq' : q - 1 = 4 * (q / 4) + 2 := by omega
    dsimp [w]
    rw [hstep, Int.emod_def]
    calc
      _ = 4 * N * ((q * r i) / (2 * N)) - 3 * N * (q - 1) := by ring
      _ = _ := by rw [hq']; ring
  have hwa : ∀ i, w (i + m) = -w i := by
    intro i
    have he := (href i).2.1
    change r (i + m) = 3 * N - r i at he
    dsimp [w]
    rw [he]
    ring
  have hsa : ∀ i, s (i + m) = -s i := by
    intro i
    have hn := (hsteps i).1
    dsimp [s]
    rw [hwa]
    split_ifs <;> omega
  have he := signed_radius_gap q 2 R w s m hq (by omega) hm
    (fun i => by dsimp [s]; split_ifs <;> omega) hsa hb hw0
    (fun i => by simpa only [← hN] using (hsteps i).2)
    (by simpa only [← hN] using hsmall)
  simpa only [← hN] using he



/- Reflection reduces an entire integer multiplication orbit to its first
m representatives. -/
theorem orbit_bounds_of_reflection (q n C x : ℤ) (m : ℕ) (hm : 0 < m)
    (_hn : 0 < n) (hx : 0 ≤ x) (hhi : C - x < n)
    (hC : Int.ModEq n (C * q) C)
    (href : Int.ModEq n (x * q ^ m) (C - x))
    (hb : ∀ i < m, x ≤ (x * q ^ i) % n ∧ (x * q ^ i) % n ≤ C - x) :
    ∀ i, x ≤ (x * q ^ i) % n ∧ (x * q ^ i) % n ≤ C - x := by
  have hCp : ∀ i : ℕ, Int.ModEq n (C * q ^ i) C := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ, ← mul_assoc]
      exact (ih.mul_right q).trans hC
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    by_cases hi : i < m
    · exact hb i hi
    let j := i - m
    have hj : j < i := by omega
    have hij : i = m + j := by omega
    have hp := ih j hj
    let r := (x * q ^ j) % n
    have hr : x ≤ r ∧ r ≤ C - x := hp
    have hmod : Int.ModEq n (x * q ^ i) (C - r) := by
      calc
        x * q ^ i = x * q ^ m * q ^ j := by rw [hij, pow_add]; ring
        _ ≡ (C - x) * q ^ j [ZMOD n] := href.mul_right _
        _ = C * q ^ j - x * q ^ j := by ring
        _ ≡ C - x * q ^ j [ZMOD n] := (hCp j).sub (Int.ModEq.refl _)
        _ ≡ C - r [ZMOD n] := (Int.ModEq.refl C).sub (Int.mod_modEq _ n).symm
    have he : (x * q ^ i) % n = C - r := hmod.eq.trans
      (Int.emod_eq_of_lt (by omega) (by omega))
    rw [he]
    constructor <;> omega

theorem q3_second_size (q : ℤ) (m : ℕ) (hq : 3 ≤ q) (hm : 3 ≤ m) :
    4 * (q ^ (m - 1) + q) < (q - 1) * (q ^ m + 1) := by
  have ht : q ^ 2 ≤ q ^ (m - 1) := pow_le_pow_right₀ (by omega) (by omega)
  have hp : q ^ m = q ^ (m - 1) * q := by rw [← pow_succ]; congr 1; omega
  have hc : 0 ≤ q ^ 2 - q - 6 := by nlinarith
  rw [hp]
  nlinarith [mul_nonneg hc (show 0 ≤ q ^ (m - 1) by positivity)]

/- Explicit orbit of the second plus-family candidate. No word encoding is
needed: its first half consists of two elementary power expressions. -/
theorem q3_second_int_leader (q N A : ℤ) (m : ℕ) (hq : 3 ≤ q)
    (hq4 : q % 4 = 3) (hm : Odd m) (hm3 : 3 ≤ m)
    (hN : N = q ^ m + 1) (hA : 4 * A = (3 * q + 1) * N) :
    let x := A - (q ^ (m - 1) + q)
    0 ≤ x ∧ x < (q + 1) * N ∧
      ∀ i : ℕ, x ≤ (x * q ^ i) % ((q + 1) * N) := by
  let D := q ^ (m - 1) + q
  let n := (q + 1) * N
  let x := A - D
  let C := 2 * A + N
  have hNpos : 0 < N := by rw [hN]; positivity
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hn : 0 < n := by dsimp [n]; positivity
  have hsize : 4 * D < (q - 1) * N := by
    simpa only [D, hN] using q3_second_size q m hq hm3
  have hAx : 0 ≤ x ∧ x < n ∧ C - x < n ∧ A + N < n := by
    dsimp [x, C, n]
    constructor
    · nlinarith
    constructor
    · nlinarith
    constructor <;> nlinarith
  have hqk : q = 4 * (q / 4) + 3 := by omega
  have hAstep : Int.ModEq n (A * q) (A + N) := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-(3 * (q / 4) + 1), ?_⟩
    dsimp [n]
    have he := congrArg (fun z => z * (q - 1)) hA
    rw [hqk] at he ⊢
    have hk : (4 * (q / 4) + 3) / 4 = q / 4 := by omega
    rw [hk]
    nlinarith only [he]
  have hNstep : Int.ModEq n (N * q) (-N) := by
    apply Int.modEq_iff_dvd.mpr
    exact ⟨-1, by dsimp [n]; ring⟩
  have hBstep : Int.ModEq n ((A + N) * q) A := by
    convert hAstep.add hNstep using 1 <;> ring
  have hCstep : Int.ModEq n (C * q) C := by
    convert (hAstep.add hAstep).add hNstep using 1 <;> dsimp [C] <;> ring
  have hApow : ∀ i : ℕ, Int.ModEq n (A * q ^ i) (if Even i then A else A + N) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ, ← mul_assoc]
      apply (ih.mul_right q).trans
      by_cases he : Even i
      · simpa only [if_pos he, if_neg (by simpa only [Nat.even_add_one, not_not] using he : ¬Even (i + 1))]
          using hAstep
      · simpa only [if_neg he, if_pos (Nat.even_add_one.mpr he)] using hBstep
  have hqmod : Int.ModEq (q + 1) q (-1) := by
    apply Int.modEq_iff_dvd.mpr
    exact ⟨-1, by ring⟩
  have hme : Even (m - 1) := Nat.even_iff.mpr (by have := Nat.odd_iff.mp hm; omega)
  have hDdiv : q + 1 ∣ D := by
    have hh := (hqmod.pow (m - 1)).add hqmod
    rw [hme.neg_one_pow, show (1 : ℤ) + -1 = 0 by ring] at hh
    exact Int.dvd_neg.mp (by simpa only [zero_sub] using hh.dvd)
  have hDm : Int.ModEq n (D * q ^ m) (-D) := by
    apply Int.modEq_iff_dvd.mpr
    have hh : n ∣ -(D * N) := Int.dvd_neg.mpr (mul_dvd_mul_right hDdiv N)
    convert hh using 1
    rw [hN]
    ring
  have href : Int.ModEq n (x * q ^ m) (C - x) := by
    have ha := hApow m
    rw [if_neg (Nat.not_even_iff_odd.mpr hm)] at ha
    convert ha.sub hDm using 1 <;> dsimp [x, C] <;> ring
  suffices hb : ∀ i : ℕ, x ≤ (x * q ^ i) % n ∧ (x * q ^ i) % n ≤ C - x from
    ⟨hAx.1, hAx.2.1, fun i => (hb i).1⟩
  apply orbit_bounds_of_reflection q n C x m (by omega) hn hAx.1 hAx.2.2.1 hCstep href
  intro i hi
  by_cases hi0 : i = 0
  · subst i
    rw [pow_zero, mul_one, Int.emod_eq_of_lt hAx.1 hAx.2.1]
    dsimp [x, C]
    constructor <;> omega
  have hi1 : 1 ≤ i := by omega
  let c := (q ^ 2 - 1) * q ^ (i - 1)
  have hc : 0 ≤ c := mul_nonneg (by nlinarith) (by positivity)
  have hci : c + q ^ (i - 1) = q ^ (i + 1) := by
    dsimp [c]
    have he : q ^ (i + 1) = q ^ 2 * q ^ (i - 1) := by rw [← pow_add]; congr 1; omega
    rw [he]; ring
  have hcN : c < N := by
    have hp : q ^ (i + 1) ≤ q ^ m := pow_le_pow_right₀ (by omega) (by omega)
    rw [hN]
    have hp0 : 0 < q ^ (i - 1) := by positivity
    omega
  have hDpow : Int.ModEq n (D * q ^ i) (N * (-1) ^ (i - 1) + c) := by
    have he : D * q ^ i = N * q ^ (i - 1) + c := by
      have hiq : q ^ i = q ^ (i - 1) * q := by rw [← pow_succ]; congr 1; omega
      have hmq : q ^ m = q ^ (m - 1) * q := by rw [← pow_succ]; congr 1; omega
      dsimp [D, c]
      rw [hiq, hN, hmq]
      ring
    rw [he]
    have hh : Int.ModEq n (q ^ (i - 1) * N) ((-1) ^ (i - 1) * N) :=
      (hqmod.pow (i - 1)).mul_right'
    simpa only [mul_comm N] using hh.add_right c
  by_cases hie : Even i
  · have hio : Odd (i - 1) := Nat.odd_iff.mpr (by have := Nat.even_iff.mp hie; omega)
    have hmod : Int.ModEq n (x * q ^ i) (A + N - c) := by
      have hh := (hApow i).sub hDpow
      rw [if_pos hie, hio.neg_one_pow] at hh
      convert hh using 1 <;> ring
    have he : (x * q ^ i) % n = A + N - c := hmod.eq.trans
      (Int.emod_eq_of_lt (by dsimp [x] at hAx; omega) (by omega))
    rw [he]
    dsimp [x, C]
    constructor <;> omega
  · have hio : Odd i := Nat.not_even_iff_odd.mp hie
    have hie' : Even (i - 1) := Nat.even_iff.mpr (by have := Nat.odd_iff.mp hio; omega)
    have him : i + 1 ≤ m - 1 := by
      have := Nat.odd_iff.mp hio
      have := Nat.odd_iff.mp hm
      omega
    have hcD : c < D := by
      have hp := pow_le_pow_right₀ (by omega : (1 : ℤ) ≤ q) him
      have hp0 : 0 < q ^ (i - 1) := by positivity
      dsimp [D]
      omega
    have hmod : Int.ModEq n (x * q ^ i) (A - c) := by
      have hh := (hApow i).sub hDpow
      rw [if_neg hie, hie'.neg_one_pow] at hh
      convert hh using 1 <;> ring
    have he : (x * q ^ i) % n = A - c := hmod.eq.trans
      (Int.emod_eq_of_lt (by dsimp [x] at hAx; omega) (by omega))
    rw [he]
    dsimp [x, C]
    constructor <;> omega



theorem q3_formula_data (q m : ℕ) (hq4 : q % 4 = 3) (hm : Odd m) (hm3 : 3 ≤ m) :
    4 * plusDeltaOne q m = (3 * q + 1) * (q ^ m + 1) ∧
      plusDeltaTwo q m + (q ^ (m - 1) + q) = plusDeltaOne q m ∧
      (q + 1) * (q ^ m + 1) < 2 * plusDeltaTwo q m := by
  have hq : 3 ≤ q := by omega
  have hp4 := q3_odd_power_mod hq4 hm
  have hN4 : 4 ∣ q ^ m + 1 := Nat.dvd_of_mod_eq_zero (by omega)
  have hA : 4 * plusDeltaOne q m = (3 * q + 1) * (q ^ m + 1) := by
    rw [plusDeltaOne, if_neg (by omega : q % 4 ≠ 1), Nat.mul_comm 4]
    exact Nat.div_mul_cancel (dvd_mul_of_dvd_right hN4 _)
  have hsize := q3_second_size (q : ℤ) m (by exact_mod_cast hq) hm3
  have hA' : 4 * (plusDeltaOne q m : ℤ) =
      (3 * (q : ℤ) + 1) * ((q : ℤ) ^ m + 1) := by exact_mod_cast hA
  have hDlt : q ^ (m - 1) + q < plusDeltaOne q m := by
    have hh : (q : ℤ) ^ (m - 1) + q < (plusDeltaOne q m : ℤ) := by
      have hNpos : 0 < (q : ℤ) ^ m + 1 := by positivity
      nlinarith
    exact_mod_cast hh
  have hcoef : 3 * q ^ 2 + q - 4 + 4 = 3 * q ^ 2 + q := Nat.sub_add_cancel (by nlinarith)
  have hqsub : q - 1 + 1 = q := Nat.sub_add_cancel (by omega)
  have hT : 1 ≤ q ^ (m - 1) := Nat.one_le_pow _ _ (by omega)
  have hprod : q - 1 ≤ (3 * q ^ 2 + q - 4) * q ^ (m - 1) := by nlinarith
  have hfsub := Nat.sub_add_cancel hprod
  have hp : q ^ m = q ^ (m - 1) * q := by rw [← pow_succ]; congr 1; omega
  have hF : (3 * q ^ 2 + q - 4) * q ^ (m - 1) - (q - 1) =
      4 * (plusDeltaOne q m - (q ^ (m - 1) + q)) := by
    have hsub := Nat.sub_add_cancel hDlt.le
    rw [hp] at hA
    nlinarith only [hA, hfsub, hqsub, hsub,
      congrArg (fun z => z * q ^ (m - 1)) hcoef]
  have hB : plusDeltaTwo q m = plusDeltaOne q m - (q ^ (m - 1) + q) := by
    rw [plusDeltaTwo, if_neg (by omega : q % 4 ≠ 1), hF, Nat.mul_div_right _ (by decide : 0 < 4)]
  have hBA : plusDeltaTwo q m + (q ^ (m - 1) + q) = plusDeltaOne q m := by omega
  refine ⟨hA, hBA, ?_⟩
  have hBA' : (plusDeltaTwo q m : ℤ) + ((q : ℤ) ^ (m - 1) + q) = plusDeltaOne q m := by
    exact_mod_cast hBA
  have hh : ((q : ℤ) + 1) * ((q : ℤ) ^ m + 1) < 2 * (plusDeltaTwo q m : ℤ) := by
    nlinarith only [hsize, hA', hBA']
  exact_mod_cast hh

/- The remaining plus branch, with both minimality and the exclusion of
all leaders strictly between the two displayed formulas. -/
theorem plus_q3_firstTwo (q m : ℕ) (hq4 : q % 4 = 3) (hm : Odd m) (hm3 : 3 ≤ m) :
    FirstTwo q ((q + 1) * (q ^ m + 1)) (plusDeltaOne q m) (plusDeltaTwo q m) := by
  obtain ⟨hA, hBA, hBhigh⟩ := q3_formula_data q m hq4 hm hm3
  have hq : 3 ≤ q := by omega
  have hA' : 4 * (plusDeltaOne q m : ℤ) =
      (3 * (q : ℤ) + 1) * ((q : ℤ) ^ m + 1) := by exact_mod_cast hA
  have hBA' : (plusDeltaTwo q m : ℤ) + ((q : ℤ) ^ (m - 1) + q) = plusDeltaOne q m := by
    exact_mod_cast hBA
  have hBlead : IsCosetLeader q ((q + 1) * (q ^ m + 1)) (plusDeltaTwo q m) := by
    have hh := q3_second_int_leader (q : ℤ) ((q : ℤ) ^ m + 1) (plusDeltaOne q m) m
      (by exact_mod_cast hq) (by exact_mod_cast hq4) hm hm3 rfl hA'
    have he : (plusDeltaOne q m : ℤ) - ((q : ℤ) ^ (m - 1) + q) = plusDeltaTwo q m := by omega
    dsimp only at hh
    rw [he] at hh
    exact ⟨by exact_mod_cast hh.2.1, fun i => by exact_mod_cast hh.2.2 i⟩
  refine ⟨(plus_q3_largest q m hq4 hm).1, hBlead, by omega, ?_⟩
  intro x hl
  by_cases hxb : x ≤ plusDeltaTwo q m
  · exact Or.inl hxb
  right
  have hqo : Odd q := Nat.odd_iff.mpr (by omega)
  have hxhigh : (q + 1) * (q ^ m + 1) < 2 * x := by omega
  obtain ⟨h, y, hqh, hxy, _hh, hly, hy⟩ := plus_high_reduction hqo hm hl hxhigh
  have hqh' : (q : ℤ) + 1 = 2 * (h : ℤ) := by exact_mod_cast hqh
  have hxy' : (x : ℤ) = (h : ℤ) * (y : ℤ) := by exact_mod_cast hxy
  have h4x : 4 * (x : ℤ) = 2 * ((q : ℤ) + 1) * (y : ℤ) := by rw [hqh', hxy']; ring
  have hxb' : (plusDeltaTwo q m : ℤ) < (x : ℤ) := by exact_mod_cast (Nat.lt_of_not_ge hxb)
  have hsmall : ((q : ℤ) + 1) * (3 * ((q : ℤ) ^ m + 1) - 2 * (y : ℤ)) <
      2 * ((q : ℤ) ^ m + 1 + 2 * ((q : ℤ) ^ (m - 1) + q)) := by
    nlinarith only [h4x, hA', hBA', hxb']
  have hgap := upper_q3_radius_gap (q : ℤ) ((q : ℤ) ^ m + 1) y m
    (by exact_mod_cast hq) (by exact_mod_cast hq4) hm hm3 rfl
    (by exact_mod_cast hy) (fun i => by exact_mod_cast hly.2 i) hsmall
  have he : (x : ℤ) = plusDeltaOne q m := by nlinarith only [hgap, h4x, hA']
  exact_mod_cast he

theorem conjecturesA :
    (∀ q m : ℕ, IsPrimePower q → Odd q → Odd m → 3 ≤ m →
      FirstTwo q ((q + 1) * (q ^ m + 1)) (plusDeltaOne q m) (plusDeltaTwo q m)) ∧
    (∀ q m : ℕ, IsPrimePower q → Odd m → 3 ≤ m →
      FirstTwo q ((q + 1) * (q ^ m - 1)) (minusDeltaOne q m) (minusDeltaTwo q m)) := by
  refine ⟨?_, conjecturesA_minus⟩
  intro q m hq hqo hm hm3
  have hq4 : q % 4 = 1 ∨ q % 4 = 3 := by have := Nat.odd_iff.mp hqo; omega
  rcases hq4 with hq4 | hq4
  · exact plus_q1_firstTwo q m (primePower_ge_two hq) hq4 hm
  · exact plus_q3_firstTwo q m hq4 hm hm3

end CosetA
