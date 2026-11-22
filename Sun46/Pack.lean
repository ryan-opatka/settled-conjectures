import Sun46.Kronecker
import Sun46.Arith

/-!
# Kernel-friendly big numbers

The numbers in `Sun46/Kronecker.lean`, written with operations the kernel evaluates
natively, and the lemmas that connect the two.

The kernel refuses `Nat.pow` when the result is larger than about `2 ^ (2 ^ 24)`, but not
`Nat.shiftLeft`, so powers of two are written as shifts.
-/

namespace Sun46

open Finset

/-- `x % 2 ^ L`. -/
def modP (x L : ℕ) : ℕ := Nat.land x (Nat.shiftLeft 1 L - 1)

/-- `a * 2 ^ b`, by a shift. It has a name of its own because a definition whose body is
`Nat.shiftLeft` applied to closed terms is evaluated in full, by the elaborator and by the kernel,
whenever it is compared with its body. -/
def shl (a b : ℕ) : ℕ := Nat.shiftLeft a b

theorem shl_eq (a b : ℕ) : shl a b = a * 2 ^ b := Nat.shiftLeft_eq a b

theorem modP_eq (x L : ℕ) : modP x L = x % 2 ^ L := by
  have h : Nat.shiftLeft 1 L = 2 ^ L := Nat.one_shiftLeft L
  rw [modP, h]
  exact Nat.and_two_pow_sub_one_eq_mod x L

/-- The exponents of the terms of the pentagonal series with sign `+`. -/
def expP (j : ℕ) : ℕ := bif Nat.beq (j % 2) 0 then gNeg j else gPos j

/-- The exponents of the terms of the pentagonal series with sign `-`. -/
def expN (j : ℕ) : ℕ := bif Nat.beq (j % 2) 0 then gPos j else gNeg j

theorem gPos_le_gNeg_succ (j : ℕ) : gPos j ≤ gNeg (j + 1) :=
  Nat.div_le_div_right (Nat.mul_le_mul (le_refl _) (by omega))

theorem expP_even {j : ℕ} (h : j % 2 = 0) : expP j = gNeg j := by
  simp [expP, beq_true_of_eq h]

theorem expP_odd {j : ℕ} (h : j % 2 = 1) : expP j = gPos j := by
  have : Nat.beq (j % 2) 0 = false := beq_false_of_ne (by omega)
  simp [expP, this]

theorem expN_even {j : ℕ} (h : j % 2 = 0) : expN j = gPos j := by
  simp [expN, beq_true_of_eq h]

theorem expN_odd {j : ℕ} (h : j % 2 = 1) : expN j = gNeg j := by
  have : Nat.beq (j % 2) 0 = false := beq_false_of_ne (by omega)
  simp [expN, this]

theorem expP_mono : Monotone expP := by
  refine monotone_nat_of_le_succ fun j => ?_
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · rw [expP_even h, expP_odd (by omega)]
    exact (gNeg_mono (Nat.le_succ j)).trans (gNeg_le_gPos _)
  · rw [expP_odd h, expP_even (by omega)]
    exact gPos_le_gNeg_succ j

theorem expN_mono : Monotone expN := by
  refine monotone_nat_of_le_succ fun j => ?_
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · rw [expN_even h, expN_odd (by omega)]
    exact gPos_le_gNeg_succ j
  · rw [expN_odd h, expN_even (by omega)]
    exact (gNeg_mono (Nat.le_succ j)).trans (gNeg_le_gPos _)

/-- `∑_{i < cnt} 2 ^ (w * (g (lo + i) - g lo))`, by halving. The first argument bounds the
depth. -/
def pk (g : ℕ → ℕ) (w : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, cnt => cnt
  | f + 1, lo, cnt =>
    bif Nat.ble cnt 1 then cnt
    else Nat.add (pk g w f lo (cnt / 2))
      (Nat.shiftLeft (pk g w f (lo + cnt / 2) (cnt - cnt / 2)) (w * (g (lo + cnt / 2) - g lo)))

theorem pk_eq (g : ℕ → ℕ) (hg : Monotone g) (w : ℕ) : ∀ f lo cnt : ℕ, cnt ≤ 2 ^ f →
    pk g w f lo cnt * 2 ^ (w * g lo) = ∑ i ∈ range cnt, 2 ^ (w * g (lo + i))
  | 0, lo, cnt, h => by
    have hc : cnt ≤ 1 := by simpa using h
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl <;> simp [pk]
  | f + 1, lo, cnt, h => by
    by_cases hc : cnt ≤ 1
    · have hb : Nat.ble cnt 1 = true := Nat.ble_eq_true_of_le hc
      simp only [pk, hb, Bool.cond_true]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl <;> simp
    · have hb : Nat.ble cnt 1 = false := by
        cases hbb : Nat.ble cnt 1
        · rfl
        · exact absurd (Nat.le_of_ble_eq_true hbb) hc
      simp only [pk, hb, Bool.cond_false]
      have hpow : 2 ^ (f + 1) = 2 * 2 ^ f := by ring
      have h1 : cnt / 2 ≤ 2 ^ f := by omega
      have h2 : cnt - cnt / 2 ≤ 2 ^ f := by omega
      have ih1 := pk_eq g hg w f lo (cnt / 2) h1
      have ih2 := pk_eq g hg w f (lo + cnt / 2) (cnt - cnt / 2) h2
      have hle : g lo ≤ g (lo + cnt / 2) := hg (Nat.le_add_right _ _)
      have hsplit : cnt = cnt / 2 + (cnt - cnt / 2) := by omega
      have hexp : w * (g (lo + cnt / 2) - g lo) + w * g lo = w * g (lo + cnt / 2) := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hle]
      calc Nat.add (pk g w f lo (cnt / 2))
            (Nat.shiftLeft (pk g w f (lo + cnt / 2) (cnt - cnt / 2))
              (w * (g (lo + cnt / 2) - g lo))) * 2 ^ (w * g lo)
          = pk g w f lo (cnt / 2) * 2 ^ (w * g lo) +
              pk g w f (lo + cnt / 2) (cnt - cnt / 2) * 2 ^ (w * g (lo + cnt / 2)) := by
            change (pk g w f lo (cnt / 2) +
              pk g w f (lo + cnt / 2) (cnt - cnt / 2) <<< (w * (g (lo + cnt / 2) - g lo))) *
                2 ^ (w * g lo) = _
            rw [Nat.shiftLeft_eq, Nat.add_mul, Nat.mul_assoc, ← pow_add, hexp]
        _ = ∑ i ∈ range (cnt / 2), 2 ^ (w * g (lo + i)) +
              ∑ i ∈ range (cnt - cnt / 2), 2 ^ (w * g (lo + cnt / 2 + i)) := by rw [ih1, ih2]
        _ = ∑ i ∈ range cnt, 2 ^ (w * g (lo + i)) := by
            conv_rhs => rw [hsplit, Finset.sum_range_add]
            simp only [Nat.add_assoc]

/-- The pentagonal sum in `ZMod M`, split into its two signs. -/
theorem pent_sum_cast (M B J : ℕ) :
    ∑ j ∈ range J, (-1) ^ j * ((B : ZMod M) ^ gNeg j - (B : ZMod M) ^ gPos j) =
      ((∑ j ∈ range J, B ^ expP j : ℕ) : ZMod M) - ((∑ j ∈ range J, B ^ expN j : ℕ) : ZMod M) := by
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · rw [expP_even h, expN_even h, (Nat.even_iff.mpr h).neg_one_pow, one_mul]
  · rw [expP_odd h, expN_odd h, (Nat.odd_iff.mpr h).neg_one_pow]
    ring

end Sun46
