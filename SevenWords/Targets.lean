import Mathlib
import SevenWords.NoModulus

/-!
# The conjectures, exactly as stated

Yolcu, Aaronson and Heule state their conjectures about trajectories of the Collatz
function `C`, which sends an odd `n` to `3 n + 1` without halving. Everything earlier in
this project is about the shortcut map `T`. This file states their Theorem 4.10 and
Conjectures 4.11 to 4.14 word for word in terms of `C`, and proves two things.

* Theorem 4.10 follows from the seven forced words: a nonconvergent `C`-trajectory cannot
  avoid the classes 2, 3, 4, 6 modulo 8. So the four cases their program proved are
  re-proved here from descent and turning, and nothing else.
* Each of the open conjectures is equivalent to the statement about steps of `T` used in
  `Barrier`. So a proof of the step form would be a proof of the conjecture as stated.

Nothing in this file is progress on the open conjectures. It fixes the targets.
-/

namespace Journey.Targets

open Function Journey.Collatz Journey.Elsewhere Journey.Barrier Journey.Seven

/-- The Collatz function, as in the paper. -/
def C (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

theorem C_odd (n : ℕ) (h : n % 2 = 1) : C n = 3 * n + 1 := by
  unfold C
  split_ifs with h' <;> omega

theorem T_even (n : ℕ) (h : n % 2 = 0) : T n = C n := by
  simp [T, C, h]

theorem T_odd (n : ℕ) (h : n % 2 = 1) : T n = C (C n) := by
  rw [C_odd n h]
  unfold T C
  split_ifs <;> omega

/-- Every term of the `T`-trajectory is a term of the `C`-trajectory. -/
theorem T_in_C : ∀ (i n : ℕ), ∃ j, T^[i] n = C^[j] n := by
  intro i
  induction i with
  | zero => exact fun n => ⟨0, rfl⟩
  | succ i ih =>
    intro n
    rw [Function.iterate_succ_apply]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · obtain ⟨j, hj⟩ := ih (C n)
      exact ⟨j + 1, by rw [T_even n h, hj, Function.iterate_succ_apply]⟩
    · obtain ⟨j, hj⟩ := ih (C (C n))
      exact ⟨j + 2, by
        rw [T_odd n h, hj, Function.iterate_succ_apply, Function.iterate_succ_apply]⟩

/-- Every odd term of the `C`-trajectory is a term of the `T`-trajectory. -/
theorem odd_C_in_T : ∀ (j n : ℕ), C^[j] n % 2 = 1 → ∃ i, T^[i] n = C^[j] n := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro n h
    match j, ih, h with
    | 0, _, _ => exact ⟨0, rfl⟩
    | 1, _, h =>
      rcases Nat.mod_two_eq_zero_or_one n with hp | hp
      · exact ⟨1, by
          change T n = C n
          exact T_even n hp⟩
      · exfalso
        have hC := C_odd n hp
        have h' : C n % 2 = 1 := h
        omega
    | j + 2, ih, h =>
      rcases Nat.mod_two_eq_zero_or_one n with hp | hp
      · have h' : C^[j + 1] (C n) % 2 = 1 := by
          rw [← Function.iterate_succ_apply]
          exact h
        rw [← T_even n hp] at h'
        obtain ⟨i, hi⟩ := ih (j + 1) (by omega) (T n) h'
        exact ⟨i + 1, by
          rw [Function.iterate_succ_apply, hi, T_even n hp, ← Function.iterate_succ_apply]⟩
      · have h' : C^[j] (C (C n)) % 2 = 1 := by
          rw [← Function.iterate_succ_apply, ← Function.iterate_succ_apply]
          exact h
        rw [← T_odd n hp] at h'
        obtain ⟨i, hi⟩ := ih j (by omega) (T n) h'
        exact ⟨i + 1, by
          rw [Function.iterate_succ_apply, hi, T_odd n hp, ← Function.iterate_succ_apply,
            ← Function.iterate_succ_apply]⟩

/-- The two trajectories reach 1 together. -/
theorem reach_iff (n : ℕ) : (∃ i, T^[i] n = 1) ↔ (∃ j, C^[j] n = 1) := by
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨j, hj⟩ := T_in_C i n
    exact ⟨j, by rw [← hj, hi]⟩
  · rintro ⟨j, hj⟩
    obtain ⟨i, hi⟩ := odd_C_in_T j n (by rw [hj])
    exact ⟨i, by rw [hi, hj]⟩

/-- Every nonconvergent `C`-trajectory contains some term with the property `S`. -/
def Visits (S : ℕ → Prop) : Prop :=
  ∀ n, 1 ≤ n → (∀ j, C^[j] n ≠ 1) → ∃ j, S (C^[j] n)

/-! ## The statements of the paper -/

/-- Theorem 4.10 of the paper: a nonconvergent Collatz trajectory cannot avoid the residue
classes of 2, 3, 4, 6 modulo 8. -/
def Theorem_4_10 : Prop :=
  Visits (· % 8 = 2) ∧ Visits (· % 8 = 3) ∧ Visits (· % 8 = 4) ∧ Visits (· % 8 = 6)

/-- Conjecture 4.11: all nonconvergent `C`-trajectories contain some `n ≡ 1 (mod 8)`. -/
def Conjecture_4_11 : Prop := Visits (· % 8 = 1)

/-- Conjecture 4.12: all nonconvergent `C`-trajectories contain some `n ≡ 5 (mod 8)`. -/
def Conjecture_4_12 : Prop := Visits (· % 8 = 5)

/-- Conjecture 4.13: all nonconvergent `C`-trajectories contain some `n ≡ 7 (mod 8)`. -/
def Conjecture_4_13 : Prop := Visits (· % 8 = 7)

/-- Conjecture 4.14: all nonconvergent `C`-trajectories contain either some
`n ≡ 5 (mod 8)` or some `n ≡ 7 (mod 8)`. -/
def Conjecture_4_14 : Prop := Visits (fun n => n % 8 = 5 ∨ n % 8 = 7)

/-! ## From `C` to `T` -/

theorem never_T_of_never_C (n : ℕ) (h : ∀ j, C^[j] n ≠ 1) : ∀ i, T^[i] n ≠ 1 :=
  fun i hi => by
    obtain ⟨j, hj⟩ := (reach_iff n).mp ⟨i, hi⟩
    exact h j hj

theorem never_C_of_never_T (n : ℕ) (h : ∀ i, T^[i] n ≠ 1) : ∀ j, C^[j] n ≠ 1 :=
  fun j hj => by
    obtain ⟨i, hi⟩ := (reach_iff n).mpr ⟨j, hj⟩
    exact h i hi

/-- For an odd class, the statement about `C`-trajectories is the statement about
`T`-trajectories. -/
theorem visits_odd_iff (r : ℕ) (hr : r % 2 = 1) : Visits (· % 8 = r) ↔ MustVisit r := by
  constructor
  · intro h n hn hne
    obtain ⟨j, hj⟩ := h n hn (never_C_of_never_T n hne)
    have hj' : C^[j] n % 8 = r := hj
    obtain ⟨i, hi⟩ := odd_C_in_T j n (by omega)
    exact ⟨i, by rw [hi]; exact hj'⟩
  · intro h n hn hne
    obtain ⟨i, hi⟩ := h n hn (never_T_of_never_C n hne)
    obtain ⟨j, hj⟩ := T_in_C i n
    exact ⟨j, by
      change C^[j] n % 8 = r
      rw [← hj]
      exact hi⟩

/-- Conjecture 4.11 as stated is the statement in steps: every walk that never comes home
sometimes takes climb, fall, climb. -/
theorem conjecture_4_11_iff : Conjecture_4_11 ↔ Sometimes ClimbFallClimb 1 :=
  (visits_odd_iff 1 (by norm_num)).trans conjecture_411_in_steps

/-- Conjecture 4.12 as stated is: every walk that never comes home sometimes takes climb,
fall, fall. -/
theorem conjecture_4_12_iff : Conjecture_4_12 ↔ Sometimes ClimbFallFall 1 :=
  (visits_odd_iff 5 (by norm_num)).trans conjecture_412_in_steps

/-- Conjecture 4.13 as stated is: every walk that never comes home sometimes climbs three
times in a row. -/
theorem conjecture_4_13_iff : Conjecture_4_13 ↔ Sometimes ThreeClimbs 1 :=
  (visits_odd_iff 7 (by norm_num)).trans conjecture_413_in_steps

/-! ## Theorem 4.10, from the seven words -/

/-- Two steps of a walk that never comes home, taken after its first step, together with
the place before them. -/
theorem two_letters (b1 b2 : Bool) (hw : [b1, b2] ∈ forcedWords) (n : ℕ) (hn : 1 ≤ n)
    (hne : ∀ i, T^[i] n ≠ 1) :
    ∃ i, (T (T^[i] n) % 2 == 1) = b1 ∧ (T (T (T^[i] n)) % 2 == 1) = b2 := by
  have hT : 1 ≤ T n := T_pos n hn
  have hneT : ∀ i, T^[i] (T n) ≠ 1 := fun i hi => hne (i + 1) (by
    rw [Function.iterate_succ_apply]
    exact hi)
  obtain ⟨i, h1, h2, -⟩ := in_our_world [b1, b2] (forced_of_mem _ hw) (T n) hT hneT
  refine ⟨i, ?_, ?_⟩
  · have e : T (T^[i] n) = (Td 1)^[i] (T n) := by
      rw [Td_one_eq, ← Function.iterate_succ_apply' T i n, Function.iterate_succ_apply]
    rw [e]
    exact h1
  · have e : T (T (T^[i] n)) = (Td 1)^[i + 1] (T n) := by
      rw [Td_one_eq, Function.iterate_succ_apply' T i (T n),
        ← Function.iterate_succ_apply' T i n, Function.iterate_succ_apply]
    rw [e]
    exact h2

/-- The class modulo 8 that a place, or the value `3 y + 1` after it, must have, given the
kinds of the next two steps after it. -/
theorem class_from_steps (y : ℕ) :
    (T y % 2 = 1 → T (T y) % 2 = 1 → (y % 2 = 0 → y % 8 = 6) ∧ (y % 2 = 1 → C y % 8 = 6)) ∧
    (T y % 2 = 1 → T (T y) % 2 = 0 → (y % 2 = 0 → y % 8 = 2) ∧ (y % 2 = 1 → C y % 8 = 2)) ∧
    (T y % 2 = 0 → T (T y) % 2 = 1 → (y % 2 = 0 → y % 8 = 4) ∧ (y % 2 = 1 → C y % 8 = 4)) := by
  have t1 := Bases.two_T y
  have t2 := Bases.two_T (T y)
  have hC : y % 2 = 1 → C y = 3 * y + 1 := C_odd y
  refine ⟨fun h1 h2 => ⟨fun h => ?_, fun h => ?_⟩, fun h1 h2 => ⟨fun h => ?_, fun h => ?_⟩,
    fun h1 h2 => ⟨fun h => ?_, fun h => ?_⟩⟩
  · omega
  · rw [hC h]
    omega
  · omega
  · rw [hC h]
    omega
  · omega
  · rw [hC h]
    omega

/-- A class met by the place before two forced steps is met by the `C`-trajectory. -/
theorem visits_of_two (b1 b2 : Bool) (hw : [b1, b2] ∈ forcedWords) (c : ℕ)
    (hc : ∀ y, (T y % 2 == 1) = b1 → (T (T y) % 2 == 1) = b2 →
      (y % 2 = 0 → y % 8 = c) ∧ (y % 2 = 1 → C y % 8 = c)) :
    Visits (· % 8 = c) := by
  intro n hn hne
  obtain ⟨i, h1, h2⟩ := two_letters b1 b2 hw n hn (never_T_of_never_C n hne)
  obtain ⟨j, hj⟩ := T_in_C i n
  obtain ⟨he, ho⟩ := hc (T^[i] n) h1 h2
  rcases Nat.mod_two_eq_zero_or_one (T^[i] n) with hp | hp
  · exact ⟨j, by
      change C^[j] n % 8 = c
      rw [← hj]
      exact he hp⟩
  · exact ⟨j + 1, by
      change C^[j + 1] n % 8 = c
      rw [Function.iterate_succ_apply', ← hj]
      exact ho hp⟩

/-- Theorem 4.10 of the paper, re-proved from the seven forced words. The class 6 comes
from climb, climb; the class 2 from climb, fall; the class 4 from fall, climb; the class 3
from climb, climb, fall. -/
theorem theorem_4_10 : Theorem_4_10 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine visits_of_two true false (by decide) 2 (fun y h1 h2 => ?_)
    have h1' : T y % 2 = 1 := by simpa using h1
    have h2' : T (T y) % 2 = 0 := by
      have : ¬ T (T y) % 2 = 1 := by simpa using h2
      omega
    exact (class_from_steps y).2.1 h1' h2'
  · exact (visits_odd_iff 3 (by norm_num)).mpr must_visit_three
  · refine visits_of_two false true (by decide) 4 (fun y h1 h2 => ?_)
    have h1' : T y % 2 = 0 := by
      have : ¬ T y % 2 = 1 := by simpa using h1
      omega
    have h2' : T (T y) % 2 = 1 := by simpa using h2
    exact (class_from_steps y).2.2 h1' h2'
  · refine visits_of_two true true (by decide) 6 (fun y h1 h2 => ?_)
    have h1' : T y % 2 = 1 := by simpa using h1
    have h2' : T (T y) % 2 = 1 := by simpa using h2
    exact (class_from_steps y).1 h1' h2'

/-- The paper's remark that the case 0 follows from the case 5: after an odd number that is
5 modulo 8 comes `3 n + 1`, which is 0 modulo 8. -/
theorem case_zero_of_case_five (h : Conjecture_4_12) : Visits (· % 8 = 0) := by
  intro n hn hne
  obtain ⟨j, hj⟩ := h n hn hne
  have hj' : C^[j] n % 8 = 5 := hj
  refine ⟨j + 1, ?_⟩
  change C^[j + 1] n % 8 = 0
  rw [Function.iterate_succ_apply']
  rw [C_odd (C^[j] n) (by omega)]
  omega

/-- And Conjecture 4.14 is weaker than each of 4.12 and 4.13. -/
theorem conjecture_4_14_of_4_12 (h : Conjecture_4_12) : Conjecture_4_14 :=
  fun n hn hne => by
    obtain ⟨j, hj⟩ := h n hn hne
    exact ⟨j, Or.inl hj⟩

theorem conjecture_4_14_of_4_13 (h : Conjecture_4_13) : Conjecture_4_14 :=
  fun n hn hne => by
    obtain ⟨j, hj⟩ := h n hn hne
    exact ⟨j, Or.inr hj⟩

end Journey.Targets

#print axioms Journey.Targets.theorem_4_10
#print axioms Journey.Targets.conjecture_4_12_iff
#print axioms Journey.Targets.case_zero_of_case_five
