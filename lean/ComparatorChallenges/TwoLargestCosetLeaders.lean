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
theorem conjecturesA :
    (∀ q m : ℕ, IsPrimePower q → Odd q → Odd m → 3 ≤ m →
      FirstTwo q ((q + 1) * (q ^ m + 1)) (plusDeltaOne q m) (plusDeltaTwo q m)) ∧
    (∀ q m : ℕ, IsPrimePower q → Odd m → 3 ≤ m →
      FirstTwo q ((q + 1) * (q ^ m - 1)) (minusDeltaOne q m) (minusDeltaTwo q m)) := by sorry

end CosetA
