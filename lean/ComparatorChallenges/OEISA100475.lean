import Mathlib

/-
The definitions `reverseDigits`, `a`, `aStartAt` and `IsUltimatelyPeriodic` below are copied
verbatim from `FormalConjectures/OEIS/100475.lean` of google-deepmind/formal-conjectures
(Copyright 2026 The Formal Conjectures Authors, Apache License 2.0), omitting only the
repository-specific attributes.  `OeisA100475.conjecture` there is the open statement
`∃ x : ℕ, 0 < x ∧ x ≠ 1 ∧ IsUltimatelyPeriodic (aStartAt x)`.
-/

namespace OeisA100475

/-- Reverses the base 10 digits of a natural number. -/
def reverseDigits (k : ℕ) : ℕ :=
  Nat.ofDigits 10 (Nat.digits 10 k |>.reverse)

/-- The primary defining sequence `a`.
a n is the Prime-th recurrence with reversal at each step.
$a(n) = \operatorname{reversal}(p_{a(n-1)})$
with $a(0)=1$, where $p_k$ is the $k$-th prime number (i.e., $p_1=2, p_2=3, \dots$). -/
noncomputable def a : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
    let k := a n
    if k = 0 then 0
    else reverseDigits (Nat.nth Nat.Prime (k - 1))

/-- Definition of the generalized sequence starting at x. -/
noncomputable def aStartAt (x : ℕ) : ℕ → ℕ
  | 0 => x
  | n + 1 =>
    let k := aStartAt x n
    if k = 0 then 0
    else reverseDigits (Nat.nth Nat.Prime (k - 1))

/-- A sequence $f : \mathbb{N} \to \mathbb{N}$ is ultimately periodic if there exist
$N, P \in \mathbb{N}$, with $P>0$, such that for all $n \ge N$, $f(n+P) = f(n)$. -/
def IsUltimatelyPeriodic (f : ℕ → ℕ) : Prop :=
  ∃ N P, P > 0 ∧ ∀ n, n ≥ N → f (n + P) = f n

end OeisA100475

namespace OeisA100475

/-- Negative answer to the question of OEIS A100475: no positive start value other than `1`
(in fact, no positive start value at all) leads to an ultimately periodic orbit. -/
theorem not_conjecture :
    ¬ ∃ x : ℕ, 0 < x ∧ x ≠ 1 ∧ IsUltimatelyPeriodic (aStartAt x) := by
  sorry

end OeisA100475
