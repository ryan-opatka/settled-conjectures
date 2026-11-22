import Sun46.Data

/-!
# Checking every `k`

For a fixed `n`, `rangeOK n S a c` checks each `k` in `[a, a + c)`: either `φ(n - k)` is not
divisible by `4`, or `m - 1` or `m + 1` fails the `gcd` test, or bit `m` of `S` is set, where
`m = φ(k) + φ(n - k)/4`. With `S = bitsOf L` this says that every `m` that could matter lies
in the list `L`.
-/

namespace Sun46

open Nat

/-- The number with a `1` in each binary position listed. -/
def bitsOf (L : List ℕ) : ℕ := L.foldl (fun acc m => acc ||| 1 <<< m) 0

theorem testBit_foldl (m : ℕ) : ∀ (L : List ℕ) (acc : ℕ),
    (L.foldl (fun acc m => acc ||| 1 <<< m) acc).testBit m = true → acc.testBit m = true ∨ m ∈ L
  | [], acc, h => Or.inl h
  | x :: xs, acc, h => by
    rcases testBit_foldl m xs _ h with h' | h'
    · rw [Nat.testBit_lor, Nat.one_shiftLeft, Nat.testBit_two_pow] at h'
      rcases Bool.or_eq_true_iff.mp h' with h'' | h''
      · exact Or.inl h''
      · exact Or.inr (by simp [of_decide_eq_true h''])
    · exact Or.inr (List.mem_cons_of_mem _ h')

theorem mem_of_testBit_bitsOf {L : List ℕ} {m : ℕ} (h : (bitsOf L).testBit m = true) : m ∈ L := by
  rcases testBit_foldl m L 0 h with h' | h'
  · simp at h'
  · exact h'

/-- Bit `m` of `S`, written with kernel-friendly primitives. -/
def bitAt (S m : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight S m) 1) 1

theorem bitAt_eq (S m : ℕ) : bitAt S m = S.testBit m := by
  have h1 : Nat.land (Nat.shiftRight S m) 1 = (S >>> m) % 2 := Nat.and_one_is_mod _
  have h2 : S.testBit m = decide ((S >>> m) % 2 = 1) := by
    rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  rw [bitAt, h1, h2]
  rcases Nat.mod_two_eq_zero_or_one (S >>> m) with h | h <;> rw [h] <;> rfl

/-- The check for one value of `m`. -/
def stepM (S m : ℕ) : Bool :=
  bif Nat.ble 600 m then
    bif Nat.beq (Nat.gcd (m - 1) P) 1 then
      bif Nat.beq (Nat.gcd (m + 1) P) 1 then bitAt S m else true
    else true
  else false

/-- The check given `a = φ(k)` and `e = φ(n - k)`. -/
def stepE (S a e : ℕ) : Bool :=
  bif Nat.beq (e % 4) 0 then stepM S (a + e / 4) else true

/-- The check for one `k`. -/
def stepOK (n S k : ℕ) : Bool := stepE S (phiF k) (phiF (n - k))

/-- The check for every `k` in `[a, a + c)`. -/
def rangeOK (n S : ℕ) : ℕ → ℕ → Bool
  | _, 0 => true
  | a, c + 1 => bif stepOK n S a then rangeOK n S (a + 1) c else false

theorem stepM_sound {S m : ℕ} (h : stepM S m = true) (h1 : (m - 1).Prime) (h2 : (m + 1).Prime) :
    S.testBit m = true := by
  unfold stepM at h
  by_cases h600 : 600 ≤ m
  · have hg1 : Nat.gcd (m - 1) P = 1 := gcd_of_prime (by omega) h1
    have hg2 : Nat.gcd (m + 1) P = 1 := gcd_of_prime (by omega) h2
    rw [Nat.ble_eq_true_of_le h600, beq_true_of_eq hg1, beq_true_of_eq hg2] at h
    simpa [bitAt_eq] using h
  · have hb : Nat.ble 600 m = false := by
      cases hb : Nat.ble 600 m
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true hb) h600
    rw [hb] at h
    simp at h

theorem stepOK_sound {n S k : ℕ} (hk1 : 1 ≤ k) (hkn : k < n) (hn : n ≤ 271441)
    (h : stepOK n S k = true) {m : ℕ} (hm : 4 * m = 4 * φ k + φ (n - k))
    (h1 : (m - 1).Prime) (h2 : (m + 1).Prime) : S.testBit m = true := by
  have ha : phiF k = φ k := phiF_eq hk1 (by omega)
  have he : phiF (n - k) = φ (n - k) := phiF_eq (by omega) (by omega)
  unfold stepOK stepE at h
  rw [ha, he] at h
  have hmod : φ (n - k) % 4 = 0 := by omega
  have hm' : φ k + φ (n - k) / 4 = m := by omega
  rw [beq_true_of_eq hmod, hm'] at h
  exact stepM_sound (by simpa using h) h1 h2

theorem rangeOK_sound (n S : ℕ) : ∀ c a : ℕ, rangeOK n S a c = true →
    ∀ k, a ≤ k → k < a + c → stepOK n S k = true
  | 0, a, _, k, h1, h2 => by omega
  | c + 1, a, h, k, h1, h2 => by
    unfold rangeOK at h
    cases hs : stepOK n S a
    · rw [hs] at h; simp at h
    · rw [hs] at h
      rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
      · exact hs
      · exact rangeOK_sound n S c (a + 1) (by simpa using h) k hlt (by omega)

/-- If the sweep succeeds, every `k` that works for `n` has its `m` in the list. -/
theorem works_mem {n : ℕ} {L : List ℕ} (hn : n ≤ 271441)
    (h : ∀ k, 1 ≤ k → k < n → stepOK n (bitsOf L) k = true) {k : ℕ} (hw : Works n k) :
    ∃ m ∈ L, (q m + 1).Prime := by
  obtain ⟨hk0, hkn, m, hm, h1, h2, h3⟩ := hw
  exact ⟨m, mem_of_testBit_bitsOf (stepOK_sound hk0 hkn hn (h k hk0 hkn) hm h1 h2), h3⟩

theorem rangeOK_append (n S : ℕ) : ∀ c a d : ℕ, rangeOK n S a c = true →
    rangeOK n S (a + c) d = true → rangeOK n S a (c + d) = true
  | 0, a, d, _, h2 => by simpa using h2
  | c + 1, a, d, h1, h2 => by
    unfold rangeOK at h1
    cases hs : stepOK n S a
    · rw [hs] at h1; simp at h1
    · rw [hs] at h1
      have h1' : rangeOK n S (a + 1) c = true := by simpa using h1
      have h2' : rangeOK n S (a + 1 + c) d = true := by
        have : a + 1 + c = a + (c + 1) := by omega
        rw [this]; exact h2
      have ih := rangeOK_append n S c (a + 1) d h1' h2'
      have hcd : c + 1 + d = (c + d) + 1 := by omega
      rw [hcd]
      unfold rangeOK
      rw [hs]
      simpa using ih

theorem rangeOK_glue {n S a c b d s : ℕ} (hb : b = a + c) (hs : s = c + d)
    (h1 : rangeOK n S a c = true) (h2 : rangeOK n S b d = true) : rangeOK n S a s = true := by
  subst hb hs
  exact rangeOK_append n S c a d h1 h2

/-- The bitmask of `mList`. -/
def Sbits : ℕ := bitsOf mList

end Sun46
