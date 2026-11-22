import Sun46.Pack

/-!
# Digits of a packed table

If `K = ∑_{a < n} f a * B ^ a` with every `f a < B`, then `f m` is the base `B` digit of `K` in
position `m`. `tableOK` checks a list of claimed digits of a number, splitting the number in
halves so that the kernel never holds more than a few copies of it.
-/

namespace Sun46

open Finset

theorem sum_lt_pow (B : ℕ) (f : ℕ → ℕ) : ∀ n : ℕ, (∀ a < n, f a < B) →
    ∑ a ∈ range n, f a * B ^ a < B ^ n
  | 0, _ => by simp
  | n + 1, h => by
    have ih := sum_lt_pow B f n fun a ha => h a (by omega)
    have hn : f n + 1 ≤ B := h n (by omega)
    rw [Finset.sum_range_succ, pow_succ]
    calc ∑ a ∈ range n, f a * B ^ a + f n * B ^ n
        < B ^ n + f n * B ^ n := by omega
      _ = (f n + 1) * B ^ n := by ring
      _ ≤ B * B ^ n := Nat.mul_le_mul_right _ hn
      _ = B ^ n * B := by ring

theorem digit_sum (B : ℕ) (hB : 1 < B) (f : ℕ → ℕ) : ∀ n m : ℕ, (∀ a < n, f a < B) → m < n →
    (∑ a ∈ range n, f a * B ^ a) / B ^ m % B = f m
  | 0, m, _, hm => by omega
  | n + 1, m, h, hm => by
    have hpos : 0 < B ^ m := Nat.pow_pos (by omega)
    rw [Finset.sum_range_succ]
    rcases Nat.lt_or_ge m n with hmn | hmn
    · have ih := digit_sum B hB f n m (fun a ha => h a (by omega)) hmn
      have hp : B ^ n = B ^ (n - m - 1) * B * B ^ m := by
        rw [← pow_succ, ← pow_add]
        congr 1
        omega
      have e : f n * B ^ n = f n * B ^ (n - m - 1) * B * B ^ m := by
        rw [hp]; ring
      rw [e, Nat.add_mul_div_right _ _ hpos, Nat.add_mul_mod_self_right, ih]
    · have hmn' : m = n := by omega
      subst hmn'
      have hlt := sum_lt_pow B f m fun a ha => h a (by omega)
      rw [Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hlt, Nat.zero_add]
      exact Nat.mod_eq_of_lt (h m (by omega))

theorem digit_mod (X L a b : ℕ) (h : a + b ≤ L) :
    X % 2 ^ L / 2 ^ a % 2 ^ b = X / 2 ^ a % 2 ^ b := by
  have hL : 2 ^ L = 2 ^ a * 2 ^ (L - a) := by rw [← pow_add]; congr 1; omega
  rw [hL, Nat.mod_mul_right_div_self]
  exact Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by omega))

/-- `tableOK w d X lo cs`: `X` holds `2 ^ d` digits in base `2 ^ w`, the positions `lo`,
`lo + 1`, ... of some larger number; check that each `(m, v)` in `cs` has digit `v` in
position `m`. -/
def tableOK (w : ℕ) : ℕ → ℕ → ℕ → List (ℕ × ℕ) → Bool
  | 0, X, _, cs => cs.all fun c => Nat.beq X c.2
  | d + 1, X, lo, cs =>
    bif cs.isEmpty then true
    else tableOK w d (modP X (w * 2 ^ d)) lo (cs.filter fun c => Nat.blt c.1 (lo + 2 ^ d))
      && tableOK w d (Nat.shiftRight X (w * 2 ^ d)) (lo + 2 ^ d)
        (cs.filter fun c => Nat.ble (lo + 2 ^ d) c.1)

theorem tableOK_sound (w : ℕ) : ∀ (d X lo : ℕ) (cs : List (ℕ × ℕ)), X < 2 ^ (w * 2 ^ d) →
    tableOK w d X lo cs = true → ∀ c ∈ cs, lo ≤ c.1 → c.1 < lo + 2 ^ d →
      X / 2 ^ (w * (c.1 - lo)) % 2 ^ w = c.2
  | 0, X, lo, cs, hX, h, c, hc, h1, h2 => by
    have hc1 : c.1 = lo := by simp at h2; omega
    have hall := List.all_eq_true.mp h c hc
    have hXc : X = c.2 := Nat.eq_of_beq_eq_true hall
    have hXw : X < 2 ^ w := by simpa using hX
    rw [hc1, Nat.sub_self, Nat.mul_zero, pow_zero, Nat.div_one, Nat.mod_eq_of_lt hXw, hXc]
  | d + 1, X, lo, cs, hX, h, c, hc, h1, h2 => by
    unfold tableOK at h
    cases hemp : cs.isEmpty
    · rw [hemp] at h
      simp only [Bool.cond_false, Bool.and_eq_true] at h
      have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by ring
      rcases Nat.lt_or_ge c.1 (lo + 2 ^ d) with hlt | hge
      · have hmem : c ∈ cs.filter fun c => Nat.blt c.1 (lo + 2 ^ d) := by
          rw [List.mem_filter]
          exact ⟨hc, by simpa [Nat.blt_eq] using hlt⟩
        have hX' : modP X (w * 2 ^ d) < 2 ^ (w * 2 ^ d) := by
          rw [modP_eq]; exact Nat.mod_lt _ (Nat.pow_pos (by norm_num))
        have ih := tableOK_sound w d _ lo _ hX' h.1 c hmem h1 hlt
        rw [modP_eq, digit_mod] at ih
        · exact ih
        · have : c.1 - lo + 1 ≤ 2 ^ d := by omega
          calc w * (c.1 - lo) + w = w * (c.1 - lo + 1) := by ring
            _ ≤ w * 2 ^ d := Nat.mul_le_mul_left w this
      · have hmem : c ∈ cs.filter fun c => Nat.ble (lo + 2 ^ d) c.1 := by
          rw [List.mem_filter]
          exact ⟨hc, Nat.ble_eq_true_of_le hge⟩
        have hX' : Nat.shiftRight X (w * 2 ^ d) < 2 ^ (w * 2 ^ d) := by
          change X >>> (w * 2 ^ d) < _
          rw [Nat.shiftRight_eq_div_pow]
          apply Nat.div_lt_of_lt_mul
          rw [← pow_add, ← Nat.mul_add, ← hpow]
          exact hX
        have ih := tableOK_sound w d _ (lo + 2 ^ d) _ hX' h.2 c hmem hge (by omega)
        have e : w * (c.1 - lo) = w * 2 ^ d + w * (c.1 - (lo + 2 ^ d)) := by
          rw [← Nat.mul_add]; congr 1; omega
        have hsh : Nat.shiftRight X (w * 2 ^ d) = X / 2 ^ (w * 2 ^ d) :=
          Nat.shiftRight_eq_div_pow X _
        rw [hsh, Nat.div_div_eq_div_mul, ← pow_add, ← e] at ih
        exact ih
    · have : cs = [] := List.isEmpty_iff.mp hemp
      subst this
      simp at hc

end Sun46
