import Mathlib

namespace CosetB

/-- Section 2: "The smallest integer in C_x is called the coset leader".
The orbit is {x*q^i mod n}; taking all natural exponents gives the same
set as one period when gcd(q,n)=1. Representatives satisfy x<n. -/
def IsCosetLeader (q n x : ℕ) : Prop :=
  x < n ∧ ∀ i : ℕ, x ≤ (x * q ^ i) % n

/-- Conjecture 25: "second and third largest coset leaders".
Rank k means exactly k-1 distinct leaders are larger. -/
def IsRankedLeader (q n x k : ℕ) : Prop :=
  IsCosetLeader q n x ∧
    ∃ s : Finset ℕ, (∀ y, y ∈ s ↔ IsCosetLeader q n y ∧ x < y) ∧ s.card + 1 = k

/-- Section 5.2: "Φ′(x,q) = (q/2)·(q^(2^x)-1)⋯(q^(2^0)-1)"
for x>=0, and q/2 otherwise. The product is empty for x<0. -/
def phiPrime (x : ℤ) (q : ℕ) : ℕ :=
  (q / 2) * ∏ j ∈ Finset.range (x + 1).toNat, (q ^ (2 ^ j) - 1)

/-- Section 5.2: "m=2^r t+2^(r-1) (r≥2,t≥1)". -/
def exponent (r t : ℕ) : ℕ := 2 ^ r * t + 2 ^ (r - 1)

/-- Section 5.2: "δ₁ = n/(q^(2^(r-1))+1)·Φ′(r-2,q)". -/
def deltaOne (q r t : ℕ) : ℕ :=
  ((q ^ exponent r t + 1) / (q ^ (2 ^ (r - 1)) + 1)) *
    phiPrime ((r : ℤ) - 2) q

/-- Section 5.2: "δ₂ = δ₁ - 2·(δ₁+Φ′(r-1,q))/q^(2^r)".
The factor 2 is included in the numerator before exact integer division. -/
def deltaTwo (q r t : ℕ) : ℕ :=
  deltaOne q r t -
    (2 * (deltaOne q r t + phiPrime ((r : ℤ) - 1) q)) / q ^ (2 ^ r)

/-- Section 5.2: "δ₃ = δ₂-(q-1)q²" if t=1;
"δ₂-2·Φ′(r-1,q)" if t>1. -/
def deltaThree (q r t : ℕ) : ℕ :=
  if t = 1 then deltaTwo q r t - (q - 1) * q ^ 2
  else deltaTwo q r t - 2 * phiPrime ((r : ℤ) - 1) q

/-- Conjecture 25 restricted to its non-power-of-two m branch.
The full conjecture implies this assertion, so its negation disproves
the full conjecture. The witness below will have q=4>2, avoiding the
abstract's nonbinary convention as well as any boundary ambiguity. -/
def Conjecture25NonPowerCase : Prop :=
  ∀ q r t : ℕ, (∃ e : ℕ, 0 < e ∧ q = 2 ^ e) → 2 ≤ r → 1 ≤ t →
    IsRankedLeader q (q ^ exponent r t + 1) (deltaTwo q r t) 2 ∧
    IsRankedLeader q (q ^ exponent r t + 1) (deltaThree q r t) 3

theorem conjecture25_false : ¬ Conjecture25NonPowerCase := by
  intro h
  have hc := (h 4 3 1 ⟨2, by norm_num, by norm_num⟩ (by norm_num)
    (by norm_num)).2.1.2 6
  norm_num [deltaThree, deltaTwo, deltaOne, phiPrime, exponent,
    Int.toNat, Finset.prod_range_succ] at hc

/-- The explicit counterexample.  For `q = 4` (a power of two with `q > 2`, as in the paper's
standing assumption) and `m = 2^3·1 + 2^2 = 12` (`r = 3`, `t = 1`), the value `δ₃ = 5875062`
predicted by Conjecture 25 is not even a coset leader modulo `n = 4^12 + 1 = 16777217`:
multiplying it by `4^6` gives the smaller residue `5724774`. -/
theorem counterexample_q4_m12 :
    exponent 3 1 = 12 ∧ deltaThree 4 3 1 = 5875062 ∧
    (deltaThree 4 3 1 * 4 ^ 6) % (4 ^ exponent 3 1 + 1) = 5724774 ∧
    ¬ IsCosetLeader 4 (4 ^ exponent 3 1 + 1) (deltaThree 4 3 1) := by
  refine ⟨by norm_num [exponent], ?_, ?_, ?_⟩
  · norm_num [deltaThree, deltaTwo, deltaOne, phiPrime, exponent, Int.toNat,
      Finset.prod_range_succ]
  · norm_num [deltaThree, deltaTwo, deltaOne, phiPrime, exponent, Int.toNat,
      Finset.prod_range_succ]
  · intro h
    have hc := h.2 6
    norm_num [deltaThree, deltaTwo, deltaOne, phiPrime, exponent, Int.toNat,
      Finset.prod_range_succ] at hc

end CosetB
