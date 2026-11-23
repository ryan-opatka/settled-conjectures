import Mathlib

/-!
# What the seven files need from the rest of the project

The definitions and lemmas below are copied unchanged from five files of a larger
private project, keeping their original namespaces. Everything else in those files is
left out. Nothing here is new: the shortcut Collatz map, Terras periodicity, and the
rational cycle of a parity word (Lagarias 1990).
-/

namespace Journey.Collatz

/-- One step: halve an even number; triple an odd one, add one, and halve. -/
def T (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- How many of the first `k` steps from `n` are odd steps. -/
def odds : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, n => n % 2 + odds k (T n)

/-- The record of the first `k` steps, read as coin flips: `true` for an odd step. -/
def flips : ℕ → ℕ → List Bool
  | 0, _ => []
  | k + 1, n => (n % 2 == 1) :: flips k (T n)

theorem T_add_even (n m : ℕ) (h : n % 2 = 0) : T (n + 2 * m) = T n + m := by
  have h' : (n + 2 * m) % 2 = 0 := by omega
  unfold T
  rw [ite_eq_left h', ite_eq_left h]
  omega

theorem T_add_odd (n m : ℕ) (h : n % 2 = 1) : T (n + 2 * m) = T n + 3 * m := by
  have h' : ¬ (n + 2 * m) % 2 = 0 := by omega
  have h'' : ¬ n % 2 = 0 := by omega
  unfold T
  rw [ite_eq_right h', ite_eq_right h'']
  omega

theorem T_pos (n : ℕ) (h : 1 ≤ n) : 1 ≤ T n := by
  unfold T
  split <;> omega

theorem iterate_pos (i n : ℕ) (h : 1 ≤ n) : 1 ≤ T^[i] n := by
  induction i generalizing n with
  | zero => exact h
  | succ i ih =>
    rw [Function.iterate_succ_apply]
    exact ih (T n) (T_pos n h)

/-- The periodicity theorem (Terras, Everett). Shifting `n` by a multiple of `2^k` does not
change its first `k` flips, and it shifts the outcome by exactly `3^(odd steps)` per unit. -/
theorem periodicity (k : ℕ) : ∀ n j : ℕ,
    T^[k] (n + 2 ^ k * j) = T^[k] n + 3 ^ odds k n * j ∧
    odds k (n + 2 ^ k * j) = odds k n ∧
    flips k (n + 2 ^ k * j) = flips k n := by
  induction k with
  | zero => intro n j; simp [odds, flips]
  | succ k ih =>
    intro n j
    have hpow : n + 2 ^ (k + 1) * j = n + 2 * (2 ^ k * j) := by ring
    have hpar : (n + 2 ^ (k + 1) * j) % 2 = n % 2 := by
      rw [hpow]; exact Nat.add_mul_mod_self_left n 2 _
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have hT : T (n + 2 ^ (k + 1) * j) = T n + 2 ^ k * j := by
        rw [hpow, T_add_even n _ h]
      obtain ⟨h1, h2, h3⟩ := ih (T n) j
      refine ⟨?_, ?_, ?_⟩
      · rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hT, h1]
        simp only [odds, h, zero_add]
      · simp only [odds]; rw [hpar, hT, h2]
      · simp only [flips]; rw [hpar, hT, h3]
    · have hT : T (n + 2 ^ (k + 1) * j) = T n + 2 ^ k * (3 * j) := by
        rw [hpow, T_add_odd n _ h]; ring
      obtain ⟨h1, h2, h3⟩ := ih (T n) (3 * j)
      refine ⟨?_, ?_, ?_⟩
      · rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hT, h1]
        simp only [odds, h]
        ring
      · simp only [odds]; rw [hpar, hT, h2]
      · simp only [flips]; rw [hpar, hT, h3]

theorem same_flips_same_class (k : ℕ) :
    ∀ n n' : ℕ, flips k n = flips k n' → n ≡ n' [MOD 2 ^ k] := by
  induction k with
  | zero => intro n n' _; simp [Nat.modEq_one]
  | succ k ih =>
    intro n n' h
    simp only [flips, List.cons.injEq] at h
    obtain ⟨hpar, htail⟩ := h
    have hT : T n ≡ T n' [MOD 2 ^ k] := ih _ _ htail
    have hsame : n % 2 = n' % 2 := by
      rcases Nat.mod_two_eq_zero_or_one n with a | a <;>
      rcases Nat.mod_two_eq_zero_or_one n' with b | b <;> simp_all
    rw [pow_succ']
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    · have hn' : n' % 2 = 0 := by omega
      have e1 : 2 * T n = n := by unfold T; rw [ite_eq_left hn]; omega
      have e2 : 2 * T n' = n' := by unfold T; rw [ite_eq_left hn']; omega
      have h2 := Nat.ModEq.mul_left' 2 hT
      rwa [e1, e2] at h2
    · have hn' : n' % 2 = 1 := by omega
      have e1 : 2 * T n = 3 * n + 1 := by unfold T; rw [ite_eq_right (by omega)]; omega
      have e2 : 2 * T n' = 3 * n' + 1 := by unfold T; rw [ite_eq_right (by omega)]; omega
      have h2 := Nat.ModEq.mul_left' 2 hT
      rw [e1, e2] at h2
      have h3 : 3 * n ≡ 3 * n' [MOD 2 * 2 ^ k] := Nat.ModEq.add_right_cancel' 1 h2
      have hc : Nat.gcd (2 * 2 ^ k) 3 = 1 := by
        rw [← pow_succ']; exact Nat.Coprime.pow_left _ (by norm_num)
      exact Nat.ModEq.cancel_left_of_coprime hc h3

/-- Two numbers share their first `k` flips exactly when they share their last `k` binary digits. -/
theorem flips_eq_iff (k n n' : ℕ) : flips k n = flips k n' ↔ n ≡ n' [MOD 2 ^ k] := by
  constructor
  · exact same_flips_same_class k n n'
  · intro h
    have e : ∀ x, flips k x = flips k (x % 2 ^ k) := by
      intro x
      have := (periodicity k (x % 2 ^ k) (x / 2 ^ k)).2.2
      rwa [Nat.mod_add_div] at this
    rw [e n, e n', show n % 2 ^ k = n' % 2 ^ k from h]

/-- For every height there is a number that climbs that many steps without one pause. -/
theorem long_climb (k : ℕ) : ∀ m : ℕ, 1 ≤ m → T^[k] (2 ^ k * m - 1) = 3 ^ k * m - 1 := by
  induction k with
  | zero => intro m hm; simp
  | succ k ih =>
    intro m hm
    have hstep : T (2 ^ (k + 1) * m - 1) = 2 ^ k * (3 * m) - 1 := by
      have hpos : 1 ≤ 2 ^ k * m := Nat.mul_pos (pow_pos (by norm_num) k) hm
      have e : 2 ^ (k + 1) * m = 2 * (2 ^ k * m) := by ring
      have e' : 2 ^ k * (3 * m) = 3 * (2 ^ k * m) := by ring
      rw [e, e']
      generalize 2 ^ k * m = x at hpos ⊢
      unfold T
      rw [ite_eq_right (by omega)]
      omega
    rw [Function.iterate_succ_apply, hstep, ih (3 * m) (by omega)]
    congr 1
    ring

end Journey.Collatz

namespace Journey.Fate

/-- One step along a prescribed flip: `true` climbs, `false` falls. -/
def step : Bool → ℚ → ℚ
  | false, x => x / 2
  | true, x => (3 * x + 1) / 2

/-- Follow a whole pattern. -/
def run : List Bool → ℚ → ℚ
  | [], x => x
  | b :: v, x => run v (step b x)

/-- The constant a pattern accumulates along the way. -/
def cOf : List Bool → ℕ
  | [] => 0
  | false :: v => 2 * cOf v
  | true :: v => 3 ^ v.count true + 2 * cOf v

/-- Following a pattern of length `k` with `m` climbs sends `x` to `(3^m x + c) / 2^k`. -/
theorem run_affine (v : List Bool) : ∀ x : ℚ,
    run v x * 2 ^ v.length = 3 ^ v.count true * x + cOf v := by
  induction v with
  | nil => intro x; simp [run, cOf]
  | cons b v ih =>
    intro x
    cases b
    · have hc : (false :: v).count true = v.count true := by simp
      have h := ih (step false x)
      simp only [run, List.length_cons, hc, cOf, step] at h ⊢
      push_cast
      linear_combination 2 * h
    · have hc : (true :: v).count true = v.count true + 1 := by simp
      have h := ih (step true x)
      simp only [run, List.length_cons, hc, cOf, step] at h ⊢
      push_cast
      linear_combination 2 * h

/-- A power of 2 is never a power of 3. No return is ever exact. -/
theorem two_three_never_agree (k m : ℕ) (hk : 0 < k) : (2 : ℚ) ^ k ≠ 3 ^ m := by
  intro h
  have h' : (2 : ℕ) ^ k = 3 ^ m := by exact_mod_cast h
  have h2 : Even ((2 : ℕ) ^ k) := Nat.even_pow.mpr ⟨even_two, hk.ne'⟩
  have h3 : Odd ((3 : ℕ) ^ m) := Odd.pow ⟨1, by norm_num⟩
  rw [h'] at h2
  exact (Nat.not_even_iff_odd.mpr h3) h2

/-- The fate of a pattern. -/
def fate (v : List Bool) : ℚ := cOf v / (2 ^ v.length - 3 ^ v.count true)

/-- Every pattern is someone's fate, and only one someone's: exactly one rational number,
pushed through the pattern, returns to itself. -/
theorem fate_unique (v : List Bool) (hv : v ≠ []) (x : ℚ) : run v x = x ↔ x = fate v := by
  have hk : 0 < v.length := List.length_pos_iff.mpr hv
  have hne : (2 : ℚ) ^ v.length - 3 ^ v.count true ≠ 0 :=
    sub_ne_zero.mpr (two_three_never_agree _ _ hk)
  have hpow : (2 : ℚ) ^ v.length ≠ 0 := pow_ne_zero _ (by norm_num)
  have haff := run_affine v x
  unfold fate
  constructor
  · intro h
    rw [h] at haff
    rw [eq_div_iff hne]
    linear_combination haff
  · intro h
    rw [eq_div_iff hne] at h
    have h2 : run v x * 2 ^ v.length = x * 2 ^ v.length := by linear_combination haff - h
    exact mul_right_cancel₀ hpow h2

/-- The fate obeys its own pattern from the first step: its numerator is odd exactly
when the pattern begins with a climb. -/
theorem fate_first_step (b : Bool) (v : List Bool) :
    cOf (b :: v) % 2 = if b then 1 else 0 := by
  cases b
  · simp [cOf]
  · change (3 ^ v.count true + 2 * cOf v) % 2 = 1
    rw [Nat.add_mul_mod_self_left, Nat.pow_mod]
    simp

theorem run_append (v w : List Bool) (x : ℚ) : run (v ++ w) x = run w (run v x) := by
  induction v generalizing x with
  | nil => rfl
  | cons b v ih => simp only [List.cons_append, run, ih]

/-- One step carries the fate of a pattern to the fate of the rotated pattern.
So the fate walks its pattern, comes back around, and walks it again, forever. -/
theorem fate_rotates (b : Bool) (v : List Bool) :
    step b (fate (b :: v)) = fate (v ++ [b]) := by
  have h1 : run (b :: v) (fate (b :: v)) = fate (b :: v) :=
    (fate_unique (b :: v) (by simp) _).mpr rfl
  have h2 : run v (step b (fate (b :: v))) = fate (b :: v) := h1
  apply (fate_unique (v ++ [b]) (by simp) _).mp
  rw [run_append, h2]
  rfl

end Journey.Fate

namespace Journey.Room

open Journey.Collatz

/-- Does the `i`-th step from `n` climb? -/
def flipAt (n i : ℕ) : Bool := T^[i] n % 2 == 1

theorem flips_eq_map (k : ℕ) : ∀ n, flips k n = (List.range k).map (flipAt n) := by
  induction k with
  | zero => intro n; rfl
  | succ k ih =>
    intro n
    have h : (flipAt n ∘ Nat.succ) = flipAt (T n) := rfl
    calc flips (k + 1) n = flipAt n 0 :: flips k (T n) := rfl
      _ = flipAt n 0 :: (List.range k).map (flipAt (T n)) := by rw [ih]
      _ = (List.range (k + 1)).map (flipAt n) := by
        rw [List.range_succ_eq_map, List.map_cons, List.map_map, h]

end Journey.Room

namespace Journey.Thread

open Journey.Collatz Journey.Room

/-- Moving along a path shifts its pattern. -/
theorem flipAt_iterate (n i k : ℕ) : flipAt (T^[k] n) i = flipAt n (i + k) := by
  unfold flipAt
  rw [Function.iterate_add_apply]

/-- Two whole numbers walk together for `k` steps exactly when
their last `k` binary digits agree. -/
theorem walk_together_nat (a b k : ℕ) :
    (∀ i < k, flipAt a i = flipAt b i) ↔ a ≡ b [MOD 2 ^ k] := by
  rw [← flips_eq_iff, flips_eq_map, flips_eq_map, List.map_inj_left]
  constructor
  · intro h i hi; exact h i (List.mem_range.mp hi)
  · intro h i hi; exact h i (List.mem_range.mpr hi)

theorem all_ones_flips (k i : ℕ) (hi : i < k) : flipAt (2 ^ k - 1) i = true := by
  obtain ⟨d, rfl⟩ : ∃ d, k = i + (d + 1) := ⟨k - i - 1, by omega⟩
  have h := long_climb i (2 ^ (d + 1)) Nat.one_le_two_pow
  have hodd : T^[i] (2 ^ (i + (d + 1)) - 1) % 2 = 1 := by
    rw [pow_add, h, pow_succ]
    have hpos : 0 < 3 ^ i * 2 ^ d := by positivity
    have e : 3 ^ i * (2 ^ d * 2) = 2 * (3 ^ i * 2 ^ d) := by ring
    rw [e]
    generalize 3 ^ i * 2 ^ d = y at hpos ⊢
    omega
  unfold flipAt
  rw [hodd]
  rfl

/-- To climb `k` times in a row, a number must already end in `k` ones.
A whole number can shadow −1 only as long as its own digits last. -/
theorem climbing_needs_height (m k : ℕ) (h : ∀ i < k, flipAt m i = true) : 2 ^ k ∣ m + 1 := by
  have h1 : m ≡ 2 ^ k - 1 [MOD 2 ^ k] :=
    (walk_together_nat m (2 ^ k - 1) k).mp
      (fun i hi => (h i hi).trans (all_ones_flips k i hi).symm)
  have h2 : m + 1 ≡ 2 ^ k - 1 + 1 [MOD 2 ^ k] := Nat.ModEq.add_right 1 h1
  rw [Nat.sub_add_cancel Nat.one_le_two_pow] at h2
  exact Nat.modEq_zero_iff_dvd.mp (h2.trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl))

/-- No whole number climbs forever, not even from some point on. -/
theorem never_climbs_forever (n : ℕ) : ¬ ∃ N, ∀ i, N ≤ i → flipAt n i = true := by
  rintro ⟨N, hN⟩
  have hall : ∀ i, flipAt (T^[N] n) i = true := fun i => by
    rw [flipAt_iterate]
    exact hN _ (Nat.le_add_left N i)
  have hd := climbing_needs_height (T^[N] n) (T^[N] n + 1) (fun i _ => hall i)
  exact absurd (Nat.le_of_dvd (Nat.succ_pos _) hd) (not_le.mpr Nat.lt_two_pow_self)

end Journey.Thread

namespace Journey.Bases

open Function Journey.Collatz Journey.Room Journey.Thread

/-- From some moment on, the walk stands only on numbers that leave remainder 1 or 2 when
divided by `M`. -/
def LooksHome (M n : ℕ) : Prop := ∃ N, ∀ i, N ≤ i → T^[i] n % M = 1 ∨ T^[i] n % M = 2

theorem two_T (x : ℕ) :
    (x % 2 = 0 ∧ 2 * T x = x) ∨ (x % 2 = 1 ∧ 2 * T x = 3 * x + 1) := by
  unfold T
  split_ifs with h
  · left
    omega
  · right
    omega

/-- What looking like home modulo 5 does force. From a number ending in 1 the step is a
climb, to a number ending in 2. From a number ending in 2 the step goes to a number
ending in 1, and it may be a fall or a climb. -/
theorem what_five_does_force (x : ℕ) (hx : x % 5 = 1 ∨ x % 5 = 2)
    (hT : T x % 5 = 1 ∨ T x % 5 = 2) :
    (x % 5 = 1 ∧ x % 2 = 1 ∧ T x % 5 = 2) ∨ (x % 5 = 2 ∧ T x % 5 = 1) := by
  rcases two_T x with ⟨hp, h2⟩ | ⟨hp, h2⟩
  · omega
  · omega

end Journey.Bases
