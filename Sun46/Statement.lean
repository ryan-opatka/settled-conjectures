import Mathlib

/-!
# A conjecture of Zhi-Wei Sun on twin primes and strict partitions

Z.-W. Sun, *Problems on combinatorial properties of primes*, arXiv:1402.6641, Conjecture 4.6
(also part (i) of the conjecture in OEIS A235343):

> For any integer `n ≥ 60`, there is a positive integer `k < n` such that `m ± 1` and
> `q(m) + 1` are all prime, where `m = φ(k) + φ(n - k)/4`.

Here `φ` is Euler's totient function and `q(m)` is the number of partitions of `m` into
distinct parts (the strict partition function, OEIS A000009).

This file only states the conjecture. `m = φ(k) + φ(n - k)/4` is read as an equation between
rational numbers, so `m ± 1` can be prime only when `m` is a natural number with
`4 * m = 4 * φ k + φ (n - k)`.
-/

namespace Sun46

open Nat

/-- The strict partition function: the number of partitions of `m` into distinct parts. -/
def q (m : ℕ) : ℕ := (Nat.Partition.distincts m).card

/-- `k` works for `n`: `0 < k < n`, and `m = φ(k) + φ(n - k)/4` is a natural number with
`m - 1`, `m + 1` and `q(m) + 1` all prime. -/
def Works (n k : ℕ) : Prop :=
  0 < k ∧ k < n ∧ ∃ m : ℕ, 4 * m = 4 * φ k + φ (n - k) ∧
    (m - 1).Prime ∧ (m + 1).Prime ∧ (q m + 1).Prime

/-- Sun's Conjecture 4.6. -/
def Conjecture : Prop := ∀ n : ℕ, 60 ≤ n → ∃ k, Works n k

/-- The reading above agrees with the literal one over the rationals. -/
theorem works_iff_rat (n k : ℕ) :
    Works n k ↔ 0 < k ∧ k < n ∧ ∃ m : ℕ, (m : ℚ) = φ k + (φ (n - k) : ℚ) / 4 ∧
      (m - 1).Prime ∧ (m + 1).Prime ∧ (q m + 1).Prime := by
  have key : ∀ m : ℕ, 4 * m = 4 * φ k + φ (n - k) ↔ (m : ℚ) = φ k + (φ (n - k) : ℚ) / 4 := by
    intro m
    constructor
    · intro h
      have h' : (4 : ℚ) * m = 4 * φ k + φ (n - k) := by exact_mod_cast h
      linarith
    · intro h
      have h' : (4 : ℚ) * m = 4 * φ k + φ (n - k) := by linarith
      exact_mod_cast h'
  simp only [Works, key]

end Sun46
