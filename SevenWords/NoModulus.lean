import Mathlib
import SevenWords.Realize

/-!
# No modulus helps

`Seven` showed that exactly seven words of steps are forced in every world, and that the
worlds of 5, 13, 47 and 59 each show it alone. That left a gap. An argument that reasons
modulo some number `m` carries over to every world prime to `m`. If `m` were a multiple of
5 · 13 · 47 · 59, none of those four worlds would be available, and such an argument might
conceivably prove more.

This file closes the gap. **For every `m`, the words forced in all the worlds prime to
`m` are exactly the same seven.** However the modulus is chosen, there are worlds prime to
it with walks above home that avoid every other word.

The proof builds two endless families of walks.

* *climb, climb, fall, then (climb, fall) `s` times.* It never falls twice running and
  never climbs three times running. Its world is `8 · 4^s − 9 · 3^s`. When `s` is `m!`,
  Fermat's little theorem makes this `8 − 9 = −1` modulo every prime factor of `m` from 5
  up. It works because 8 and 9 are neighbours: three steps take out `2^3`, two climbs put
  in `3^2`, and the difference is 1.
* *`a` climbs, two falls, then (climb, climb, climb, fall, fall) `s` times.* It never
  takes climb, fall, climb; never fall, climb, fall; never fall, climb, climb, fall. Its
  world is `2^(a+2+5s) − 3^(a+3s)`. With `a` and `s` multiples of `m!` this is `4 − 1 = 3`
  modulo every prime factor of `m` from 5 up.

And every word outside the seven contains one of those five words. So the five are the
smallest words that are not forced, and the two families avoid them in worlds prime to
anything.

I did not know this was true when I began. The earlier file could only say "unless the
modulus is a multiple of 180245".

What the theorem says is exact. What it means for proofs is a reading, and I want to keep
the two apart. The reading is this: a walker `n` in the world of `d` is the fraction
`n / d`, and a fraction has a remainder modulo `m` exactly when `d` is prime to `m`. So
reasoning about remainders modulo `m` makes sense, unchanged, in every world prime to `m`.
If such reasoning proved that every walk above home takes some word, it would prove it in
all those worlds, and for every word outside the seven that is false in one of them.

A second reader pointed out how little this reading carries. It rules out only arguments
that never use the fact that the walkers are whole numbers, and `Caution` shows that one
small fact of that kind can be enough to prove a statement that fails next door. So the
theorem is exact, and the reading is weak. It measures what can be known without knowing
the world. It does not measure how hard anything is.

The cycles and the correspondence are classical. The two families, the five smallest
unforced words, and the theorem are what I found. I cannot be sure nobody has done this.
-/

namespace Journey.NoModulus

open Function Journey.Elsewhere Journey.Seven Journey.Realize
open Journey.Fate (step run cOf fate)

/-! ## Small tools -/

theorem succ_mod (i k : ℕ) (hk : 2 ≤ k) :
    (i + 1) % k = if i % k + 1 = k then 0 else i % k + 1 := by
  have hr : i % k < k := Nat.mod_lt _ (by omega)
  rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < k by omega)]
  split_ifs with h
  · rw [h, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

/-- Four moments in a row, as places on a round of length `k`. -/
theorem residues (i k : ℕ) (hk : 2 ≤ k) :
    ∃ r0 r1 r2 r3, r0 = i % k ∧ r1 = (i + 1) % k ∧ r2 = (i + 2) % k ∧ r3 = (i + 3) % k ∧
      r0 < k ∧ (r1 = if r0 + 1 = k then 0 else r0 + 1) ∧
      (r2 = if r1 + 1 = k then 0 else r1 + 1) ∧ (r3 = if r2 + 1 = k then 0 else r2 + 1) :=
  ⟨_, _, _, _, rfl, rfl, rfl, rfl, Nat.mod_lt _ (by omega), succ_mod i k hk,
    succ_mod (i + 1) k hk, succ_mod (i + 2) k hk⟩

theorem occAt_append (s : ℕ → Bool) : ∀ (u v : List Bool) (i : ℕ),
    occAt s i (u ++ v) ↔ occAt s i u ∧ occAt s (i + u.length) v
  | [], v, i => by simp [occAt]
  | b :: u, v, i => by
    change (s i = b ∧ occAt s (i + 1) (u ++ v)) ↔
      ((s i = b ∧ occAt s (i + 1) u) ∧ occAt s (i + (u.length + 1)) v)
    rw [occAt_append s u v (i + 1), show i + 1 + u.length = i + (u.length + 1) by ring]
    tauto

/-- A walk that takes a word takes every stretch of it. -/
theorem occ_of_infix (s : ℕ → Bool) (u w : List Bool) (h : u <:+: w) (i : ℕ)
    (hw : occAt s i w) : ∃ j, occAt s j u := by
  obtain ⟨l1, l2, rfl⟩ := h
  rw [occAt_append, occAt_append] at hw
  exact ⟨_, hw.1.2⟩

/-! ## The five smallest words that are not forced -/

/-- fall fall; climb climb climb; climb fall climb; fall climb fall; fall climb climb
fall. -/
def minimalWords : List (List Bool) :=
  [[false, false], [true, true, true], [true, false, true], [false, true, false],
    [false, true, true, false]]

theorem two_contain :
    ∀ a b : Bool, [a, b] ∉ forcedWords → ∃ u ∈ minimalWords, u <:+: [a, b] := by decide

theorem three_contain :
    ∀ a b c : Bool, [a, b, c] ∉ forcedWords → ∃ u ∈ minimalWords, u <:+: [a, b, c] := by
  decide

/-- Every word of four steps contains one of the five. -/
theorem four_contain : ∀ a b c e : Bool, ∃ u ∈ minimalWords, u <:+: [a, b, c, e] := by
  decide

/-- Every word outside the seven contains one of the five. -/
theorem contains_minimal : ∀ w : List Bool, w ∉ forcedWords → ∃ u ∈ minimalWords, u <:+: w
  | [], h => absurd (by decide) h
  | [a], h => absurd (by cases a <;> decide) h
  | [a, b], h => two_contain a b h
  | [a, b, c], h => three_contain a b c h
  | a :: b :: c :: e :: rest, _ => by
    obtain ⟨u, hu, hi⟩ := four_contain a b c e
    exact ⟨u, hu, hi.trans ⟨[], rest, by simp⟩⟩

/-! ## Worlds prime to `m` -/

theorem cast_world (q K O : ℕ) (h : 3 ^ O < 2 ^ K) (hq : q ∣ 2 ^ K - 3 ^ O) :
    (3 : ZMod q) ^ O = (2 : ZMod q) ^ K := by
  have h0 : ((2 ^ K - 3 ^ O : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hq
  have h1 : (2 ^ K - 3 ^ O) + 3 ^ O = 2 ^ K := Nat.sub_add_cancel h.le
  have h2 := congrArg (Nat.cast : ℕ → ZMod q) h1
  rw [Nat.cast_add, h0, zero_add] at h2
  push_cast at h2
  exact h2

/-- A world `2 ^ K - 3 ^ O` is prime to `m` as soon as the two powers differ modulo every
prime factor of `m` other than 2 and 3. -/
theorem coprime_world (m K O : ℕ) (hK : 0 < K) (hO : 0 < O) (h : 3 ^ O < 2 ^ K)
    (hne : ∀ q, q.Prime → q ∣ m → q ≠ 2 → q ≠ 3 → (3 : ZMod q) ^ O ≠ (2 : ZMod q) ^ K) :
    Nat.Coprime (2 ^ K - 3 ^ O) m := by
  apply Nat.coprime_of_dvd
  intro q hq hqd hqm
  by_cases h2 : q = 2
  · subst h2
    have h2K : 2 ∣ 2 ^ K := dvd_pow_self 2 hK.ne'
    have h3O : 2 ∣ 3 ^ O :=
      (Nat.dvd_add_right hqd).mp (by rw [Nat.sub_add_cancel h.le]; exact h2K)
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h3O
    omega
  · by_cases h3 : q = 3
    · subst h3
      have h3O : 3 ∣ 3 ^ O := dvd_pow_self 3 hO.ne'
      have h2K : 3 ∣ 2 ^ K := by
        have := Nat.dvd_add hqd h3O
        rwa [Nat.sub_add_cancel h.le] at this
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2K
      omega
    · exact hne q hq hqm h2 h3 (cast_world q K O h hqd)

/-- Fermat's little theorem, in the form used here: modulo a prime factor `q` of `m`, any
number prime to `q` raised to the power `m!` is 1. -/
theorem pow_factorial_eq_one (q m a : ℕ) (hq : q.Prime) (hqm : q ∣ m) (hm : 0 < m)
    (ha : ¬ q ∣ a) : ((a : ℕ) : ZMod q) ^ m.factorial = 1 := by
  have : Fact q.Prime := Fact.mk hq
  have ha' : ((a : ℕ) : ZMod q) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact ha
  have hle : q ≤ m := Nat.le_of_dvd hm hqm
  have hdvd : q - 1 ∣ m.factorial :=
    Nat.dvd_factorial (by have := hq.one_lt; omega) (by omega)
  obtain ⟨c, hc⟩ := hdvd
  rw [hc, pow_mul, ZMod.pow_card_sub_one_eq_one ha', one_pow]

theorem two_pow_one (q m : ℕ) (hq : q.Prime) (hqm : q ∣ m) (hm : 0 < m) (h2 : q ≠ 2) :
    (2 : ZMod q) ^ m.factorial = 1 := by
  have h := pow_factorial_eq_one q m 2 hq hqm hm
    (fun hd => h2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hd))
  exact_mod_cast h

theorem three_pow_one (q m : ℕ) (hq : q.Prime) (hqm : q ∣ m) (hm : 0 < m) (h3 : q ≠ 3) :
    (3 : ZMod q) ^ m.factorial = 1 := by
  have h := pow_factorial_eq_one q m 3 hq hqm hm
    (fun hd => h3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hd))
  exact_mod_cast h

/-! ## The first family: climb, climb, fall, then climb, fall for ever -/

/-- The rule: climb at places 0 and 1, and after that at the odd places. -/
def fB (j : ℕ) : Bool := decide (j < 2 ∨ j % 2 = 1)

theorem fB_true (j : ℕ) : fB j = true ↔ (j < 2 ∨ j % 2 = 1) := by
  unfold fB
  exact decide_eq_true_iff

theorem fB_false (j : ℕ) : fB j = false ↔ ¬ (j < 2 ∨ j % 2 = 1) := by
  unfold fB
  exact decide_eq_false_iff_not

theorem climbs_fB (s : ℕ) : climbs fB (2 * s + 3) = s + 2 := by
  induction s with
  | zero =>
    have e0 : fB 0 = true := by decide
    have e1 : fB 1 = true := by decide
    have e2 : fB 2 = false := by decide
    have h1 : climbs fB 1 = climbs fB 0 + if fB 0 then 1 else 0 := climbs_succ fB 0
    have h2 : climbs fB 2 = climbs fB 1 + if fB 1 then 1 else 0 := climbs_succ fB 1
    have h3 : climbs fB 3 = climbs fB 2 + if fB 2 then 1 else 0 := climbs_succ fB 2
    change climbs fB 3 = 2
    rw [h3, h2, h1, climbs_zero, e0, e1, e2]
    rfl
  | succ s ih =>
    have e1 : fB (2 * s + 3) = true := (fB_true _).mpr (by omega)
    have e2 : fB (2 * s + 3 + 1) = false := (fB_false _).mpr (by omega)
    rw [show 2 * (s + 1) + 3 = 2 * s + 3 + 1 + 1 by ring, climbs_succ, climbs_succ, ih,
      e1, e2]
    simp

theorem contracts_B (s : ℕ) (hs : 1 ≤ s) : 3 ^ (s + 2) < 2 ^ (2 * s + 3) := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s _ ih =>
    calc 3 ^ (s + 1 + 2) = 3 * 3 ^ (s + 2) := by ring
      _ < 3 * 2 ^ (2 * s + 3) := by omega
      _ ≤ 4 * 2 ^ (2 * s + 3) := by omega
      _ = 2 ^ (2 * (s + 1) + 3) := by ring

theorem shadow_B1 : shadow fB 1 = 2 := by
  have h : shadow fB 1 = step (fB 0) (shadow fB 0) := shadow_succ fB 0
  have e0 : fB 0 = true := by decide
  rw [h, shadow_zero, e0]
  norm_num [step]

theorem shadow_B2 : shadow fB 2 = 7 / 2 := by
  have h : shadow fB 2 = step (fB 1) (shadow fB 1) := shadow_succ fB 1
  have e1 : fB 1 = true := by decide
  rw [h, shadow_B1, e1]
  norm_num [step]

theorem shadow_B3 : shadow fB 3 = 7 / 4 := by
  have h : shadow fB 3 = step (fB 2) (shadow fB 2) := shadow_succ fB 2
  have e2 : fB 2 = false := by decide
  rw [h, shadow_B2, e2]
  norm_num [step]

/-- From the third step on, the shadow is above 1 before each climb and above 2 before
each fall. -/
theorem shadow_B (i : ℕ) (hi : 3 ≤ i) :
    (i % 2 = 1 → 1 < shadow fB i) ∧ (i % 2 = 0 → 2 < shadow fB i) := by
  induction i, hi using Nat.le_induction with
  | base =>
    constructor
    · intro _
      rw [shadow_B3]
      norm_num
    · intro h
      omega
  | succ i hi ih =>
    constructor
    · intro hodd
      have he : fB i = false := (fB_false i).mpr (by omega)
      have h2 := ih.2 (by omega)
      rw [shadow_succ, he]
      simp only [step]
      linarith
    · intro heven
      have he : fB i = true := (fB_true i).mpr (by omega)
      have h1 := ih.1 (by omega)
      rw [shadow_succ, he]
      simp only [step]
      linarith

theorem shadow_B_ge (j : ℕ) : 1 ≤ shadow fB j := by
  rcases Nat.lt_or_ge j 3 with h | h
  · interval_cases j
    · rw [shadow_zero]
    · rw [shadow_B1]
      norm_num
    · rw [shadow_B2]
      norm_num
  · obtain ⟨h1, h2⟩ := shadow_B j h
    rcases Nat.mod_two_eq_zero_or_one j with e | e
    · linarith [h2 e]
    · linarith [h1 e]

/-- It never falls twice running. -/
theorem no_FF_B (s i : ℕ) :
    ¬ (fB (i % (2 * s + 3)) = false ∧ fB ((i + 1) % (2 * s + 3)) = false) := by
  rintro ⟨h0, h1⟩
  obtain ⟨r0, r1, _, _, e0, e1, _, _, hr, s1, _, _⟩ := residues i (2 * s + 3) (by omega)
  rw [← e0] at h0
  rw [← e1] at h1
  rw [fB_false] at h0 h1
  split_ifs at s1 <;> omega

/-- It never climbs three times running. -/
theorem no_CCC_B (s i : ℕ) :
    ¬ (fB (i % (2 * s + 3)) = true ∧ fB ((i + 1) % (2 * s + 3)) = true ∧
      fB ((i + 2) % (2 * s + 3)) = true) := by
  rintro ⟨h0, h1, h2⟩
  obtain ⟨r0, r1, r2, _, e0, e1, e2, _, hr, s1, s2, _⟩ := residues i (2 * s + 3) (by omega)
  rw [← e0] at h0
  rw [← e1] at h1
  rw [← e2] at h2
  rw [fB_true] at h0 h1 h2
  split_ifs at s1 s2 <;> omega

/-- The first family, in a world prime to `m`. -/
theorem witness_B (m : ℕ) (hm : 0 < m) :
    ∃ d n, d % 2 = 1 ∧ Nat.Coprime d m ∧ (∀ i, d < (Td d)^[i] n) ∧
      (∀ i, ¬ occAt (pat d n) i [false, false]) ∧
      (∀ i, ¬ occAt (pat d n) i [true, true, true]) := by
  obtain ⟨s, hs⟩ : ∃ s, s = m.factorial := ⟨_, rfl⟩
  have hs1 : 1 ≤ s := by
    rw [hs]
    exact Nat.factorial_pos m
  have hcl := climbs_fB s
  have hcon : 3 ^ climbs fB (2 * s + 3) < 2 ^ (2 * s + 3) := by
    rw [hcl]
    exact contracts_B s hs1
  obtain ⟨hodd, habove, hpat⟩ := realize fB (2 * s + 3) (by omega) hcon
    (fun j _ => shadow_B_ge j) ((shadow_B (2 * s + 3) (by omega)).1 (by omega))
  refine ⟨worldOf fB (2 * s + 3), walker fB (2 * s + 3), hodd, ?_, habove, ?_, ?_⟩
  · rw [worldOf_eq, hcl]
    refine coprime_world m (2 * s + 3) (s + 2) (by omega) (by omega) (contracts_B s hs1) ?_
    intro q hq hqm h2 h3 h
    have : Fact q.Prime := Fact.mk hq
    have P2 : (2 : ZMod q) ^ s = 1 := by
      rw [hs]
      exact two_pow_one q m hq hqm hm h2
    have P3 : (3 : ZMod q) ^ s = 1 := by
      rw [hs]
      exact three_pow_one q m hq hqm hm h3
    have e3 : (3 : ZMod q) ^ (s + 2) = 9 := by
      rw [pow_add, P3]
      norm_num
    have e2 : (2 : ZMod q) ^ (2 * s + 3) = 8 := by
      rw [pow_add, mul_comm 2 s, pow_mul, P2]
      norm_num
    rw [e3, e2] at h
    have h1 : (1 : ZMod q) = 0 := by linear_combination h
    exact one_ne_zero h1
  · intro i hi
    obtain ⟨h0, h1, -⟩ := hi
    rw [hpat] at h0 h1
    exact no_FF_B s i ⟨h0, h1⟩
  · intro i hi
    obtain ⟨h0, h1, h2, -⟩ := hi
    rw [hpat] at h0 h1 h2
    exact no_CCC_B s i ⟨h0, h1, h2⟩

/-! ## The second family: `a` climbs, two falls, then climb, climb, climb, fall, fall -/

/-- The rule: climb at the first `a` places, fall twice, and after that climb three times
and fall twice, for ever. -/
def fA (a j : ℕ) : Bool := decide (j < a ∨ (a + 2 ≤ j ∧ (j - (a + 2)) % 5 < 3))

theorem fA_true (a j : ℕ) :
    fA a j = true ↔ (j < a ∨ (a + 2 ≤ j ∧ (j - (a + 2)) % 5 < 3)) := by
  unfold fA
  exact decide_eq_true_iff

theorem fA_false (a j : ℕ) :
    fA a j = false ↔ ¬ (j < a ∨ (a + 2 ≤ j ∧ (j - (a + 2)) % 5 < 3)) := by
  unfold fA
  exact decide_eq_false_iff_not

theorem climbs_fA_low (a : ℕ) : ∀ j, j ≤ a → climbs (fA a) j = j := by
  intro j
  induction j with
  | zero =>
    intro _
    exact climbs_zero _
  | succ j ih =>
    intro hj
    have e : fA a j = true := (fA_true a j).mpr (Or.inl (by omega))
    rw [climbs_succ, ih (by omega), e]
    simp

theorem climbs_fA (a s : ℕ) : climbs (fA a) (a + 2 + 5 * s) = a + 3 * s := by
  induction s with
  | zero =>
    have e1 : fA a a = false := (fA_false a a).mpr (by omega)
    have e2 : fA a (a + 1) = false := (fA_false a (a + 1)).mpr (by omega)
    rw [show a + 2 + 5 * 0 = a + 1 + 1 by omega, climbs_succ, climbs_succ,
      climbs_fA_low a a le_rfl, e1, e2]
    simp
  | succ s ih =>
    have e0 : fA a (a + 2 + 5 * s) = true := (fA_true a _).mpr (Or.inr (by omega))
    have e1 : fA a (a + 2 + 5 * s + 1) = true := (fA_true a _).mpr (Or.inr (by omega))
    have e2 : fA a (a + 2 + 5 * s + 1 + 1) = true := (fA_true a _).mpr (Or.inr (by omega))
    have e3 : fA a (a + 2 + 5 * s + 1 + 1 + 1) = false := (fA_false a _).mpr (by omega)
    have e4 : fA a (a + 2 + 5 * s + 1 + 1 + 1 + 1) = false :=
      (fA_false a _).mpr (by omega)
    rw [show a + 2 + 5 * (s + 1) = a + 2 + 5 * s + 1 + 1 + 1 + 1 + 1 by ring, climbs_succ,
      climbs_succ, climbs_succ, climbs_succ, climbs_succ, ih, e0, e1, e2, e3, e4]
    simp
    omega

theorem contracts_A (a : ℕ) : 3 ^ (a + 3 * (3 * a)) < 2 ^ (a + 2 + 5 * (3 * a)) := by
  have h : (3 ^ 10) ^ a ≤ (2 ^ 16) ^ a := Nat.pow_le_pow_left (by norm_num) a
  calc 3 ^ (a + 3 * (3 * a)) = (3 ^ 10) ^ a := by
        rw [← pow_mul]
        congr 1
        omega
    _ ≤ (2 ^ 16) ^ a := h
    _ < 2 ^ (a + 2 + 5 * (3 * a)) := by
        rw [← pow_mul]
        exact Nat.pow_lt_pow_right (by norm_num) (by omega)

/-- While it climbs, the shadow gains at least one at every step. -/
theorem shadow_A_low (a : ℕ) : ∀ j, j ≤ a → (j : ℚ) + 1 ≤ shadow (fA a) j := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [shadow_zero]
    norm_num
  | succ j ih =>
    intro hj
    have e : fA a j = true := (fA_true a j).mpr (Or.inl (by omega))
    have h := ih (by omega)
    have hj0 : (0 : ℚ) ≤ j := Nat.cast_nonneg j
    rw [shadow_succ, e]
    simp only [step]
    push_cast
    linarith

/-- One round of climb, climb, climb, fall, fall, begun at or above 1. -/
theorem block (a s : ℕ) (h : 1 ≤ shadow (fA a) (a + 2 + 5 * s)) :
    2 ≤ shadow (fA a) (a + 2 + 5 * s + 1) ∧
    7 / 2 ≤ shadow (fA a) (a + 2 + 5 * s + 1 + 1) ∧
    23 / 4 ≤ shadow (fA a) (a + 2 + 5 * s + 1 + 1 + 1) ∧
    23 / 8 ≤ shadow (fA a) (a + 2 + 5 * s + 1 + 1 + 1 + 1) ∧
    23 / 16 ≤ shadow (fA a) (a + 2 + 5 * s + 1 + 1 + 1 + 1 + 1) := by
  have e0 : fA a (a + 2 + 5 * s) = true := (fA_true a _).mpr (Or.inr (by omega))
  have e1 : fA a (a + 2 + 5 * s + 1) = true := (fA_true a _).mpr (Or.inr (by omega))
  have e2 : fA a (a + 2 + 5 * s + 1 + 1) = true := (fA_true a _).mpr (Or.inr (by omega))
  have e3 : fA a (a + 2 + 5 * s + 1 + 1 + 1) = false := (fA_false a _).mpr (by omega)
  have e4 : fA a (a + 2 + 5 * s + 1 + 1 + 1 + 1) = false := (fA_false a _).mpr (by omega)
  have h1 : 2 ≤ shadow (fA a) (a + 2 + 5 * s + 1) := by
    rw [shadow_succ, e0]
    simp only [step]
    linarith
  have h2 : 7 / 2 ≤ shadow (fA a) (a + 2 + 5 * s + 1 + 1) := by
    rw [shadow_succ, e1]
    simp only [step]
    linarith
  have h3 : 23 / 4 ≤ shadow (fA a) (a + 2 + 5 * s + 1 + 1 + 1) := by
    rw [shadow_succ, e2]
    simp only [step]
    linarith
  have h4 : 23 / 8 ≤ shadow (fA a) (a + 2 + 5 * s + 1 + 1 + 1 + 1) := by
    rw [shadow_succ, e3]
    simp only [step]
    linarith
  have h5 : 23 / 16 ≤ shadow (fA a) (a + 2 + 5 * s + 1 + 1 + 1 + 1 + 1) := by
    rw [shadow_succ, e4]
    simp only [step]
    linarith
  exact ⟨h1, h2, h3, h4, h5⟩

theorem shadow_A_mid (a : ℕ) (ha : 3 ≤ a) : 2 ≤ shadow (fA a) (a + 1) := by
  have e1 : fA a a = false := (fA_false a a).mpr (by omega)
  have h0 := shadow_A_low a a le_rfl
  have ha' : (3 : ℚ) ≤ a := by exact_mod_cast ha
  rw [shadow_succ, e1]
  simp only [step]
  linarith

theorem shadow_A_start (a : ℕ) (ha : 3 ≤ a) : ∀ s, 1 ≤ shadow (fA a) (a + 2 + 5 * s) := by
  intro s
  induction s with
  | zero =>
    have e2 : fA a (a + 1) = false := (fA_false a (a + 1)).mpr (by omega)
    have h1 := shadow_A_mid a ha
    rw [show a + 2 + 5 * 0 = a + 1 + 1 by omega, shadow_succ, e2]
    simp only [step]
    linarith
  | succ s ih =>
    have hb := block a s ih
    rw [show a + 2 + 5 * (s + 1) = a + 2 + 5 * s + 1 + 1 + 1 + 1 + 1 by ring]
    linarith [hb.2.2.2.2]

theorem shadow_A_end (a : ℕ) (ha : 3 ≤ a) (s : ℕ) (hs : 1 ≤ s) :
    1 < shadow (fA a) (a + 2 + 5 * s) := by
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have hb := block a s' (shadow_A_start a ha s')
  rw [show a + 2 + 5 * (s' + 1) = a + 2 + 5 * s' + 1 + 1 + 1 + 1 + 1 by ring]
  linarith [hb.2.2.2.2]

theorem shadow_A_ge (a : ℕ) (ha : 3 ≤ a) (j : ℕ) : 1 ≤ shadow (fA a) j := by
  rcases Nat.lt_or_ge j (a + 2) with h | h
  · rcases Nat.lt_or_ge j (a + 1) with h' | h'
    · have h0 := shadow_A_low a j (by omega)
      have hj : (0 : ℚ) ≤ j := Nat.cast_nonneg j
      linarith
    · have ej : j = a + 1 := by omega
      rw [ej]
      linarith [shadow_A_mid a ha]
  · obtain ⟨s, t, ht, rfl⟩ : ∃ s t, t < 5 ∧ j = a + 2 + 5 * s + t :=
      ⟨(j - (a + 2)) / 5, (j - (a + 2)) % 5, Nat.mod_lt _ (by norm_num), by omega⟩
    have h0 := shadow_A_start a ha s
    obtain ⟨h1, h2, h3, h4, _⟩ := block a s h0
    interval_cases t
    · change 1 ≤ shadow (fA a) (a + 2 + 5 * s)
      exact h0
    · linarith
    · change 1 ≤ shadow (fA a) (a + 2 + 5 * s + 1 + 1)
      linarith
    · change 1 ≤ shadow (fA a) (a + 2 + 5 * s + 1 + 1 + 1)
      linarith
    · change 1 ≤ shadow (fA a) (a + 2 + 5 * s + 1 + 1 + 1 + 1)
      linarith

/-- It never takes climb, fall, climb. -/
theorem no_CFC_A (a s i : ℕ) (ha : 3 ≤ a) :
    ¬ (fA a (i % (a + 2 + 5 * s)) = true ∧ fA a ((i + 1) % (a + 2 + 5 * s)) = false ∧
      fA a ((i + 2) % (a + 2 + 5 * s)) = true) := by
  rintro ⟨h0, h1, h2⟩
  obtain ⟨r0, r1, r2, _, e0, e1, e2, _, hr, s1, s2, _⟩ :=
    residues i (a + 2 + 5 * s) (by omega)
  rw [← e0] at h0
  rw [← e1] at h1
  rw [← e2] at h2
  rw [fA_true] at h0 h2
  rw [fA_false] at h1
  split_ifs at s1 s2 <;> omega

/-- It never takes fall, climb, fall. -/
theorem no_FCF_A (a s i : ℕ) (ha : 3 ≤ a) :
    ¬ (fA a (i % (a + 2 + 5 * s)) = false ∧ fA a ((i + 1) % (a + 2 + 5 * s)) = true ∧
      fA a ((i + 2) % (a + 2 + 5 * s)) = false) := by
  rintro ⟨h0, h1, h2⟩
  obtain ⟨r0, r1, r2, _, e0, e1, e2, _, hr, s1, s2, _⟩ :=
    residues i (a + 2 + 5 * s) (by omega)
  rw [← e0] at h0
  rw [← e1] at h1
  rw [← e2] at h2
  rw [fA_false] at h0 h2
  rw [fA_true] at h1
  split_ifs at s1 s2 <;> omega

/-- It never takes fall, climb, climb, fall. -/
theorem no_FCCF_A (a s i : ℕ) (ha : 3 ≤ a) :
    ¬ (fA a (i % (a + 2 + 5 * s)) = false ∧ fA a ((i + 1) % (a + 2 + 5 * s)) = true ∧
      fA a ((i + 2) % (a + 2 + 5 * s)) = true ∧
      fA a ((i + 3) % (a + 2 + 5 * s)) = false) := by
  rintro ⟨h0, h1, h2, h3⟩
  obtain ⟨r0, r1, r2, r3, e0, e1, e2, e3, hr, s1, s2, s3⟩ :=
    residues i (a + 2 + 5 * s) (by omega)
  rw [← e0] at h0
  rw [← e1] at h1
  rw [← e2] at h2
  rw [← e3] at h3
  rw [fA_false] at h0 h3
  rw [fA_true] at h1 h2
  split_ifs at s1 s2 s3 <;> omega

/-- The second family, in a world prime to `m`. -/
theorem witness_A (m : ℕ) (hm : 0 < m) :
    ∃ d n, d % 2 = 1 ∧ Nat.Coprime d m ∧ (∀ i, d < (Td d)^[i] n) ∧
      (∀ i, ¬ occAt (pat d n) i [true, false, true]) ∧
      (∀ i, ¬ occAt (pat d n) i [false, true, false]) ∧
      (∀ i, ¬ occAt (pat d n) i [false, true, true, false]) := by
  obtain ⟨a, ha⟩ : ∃ a, a = m.factorial * 3 := ⟨_, rfl⟩
  have ha3 : 3 ≤ a := by
    have := Nat.factorial_pos m
    omega
  have hcl := climbs_fA a (3 * a)
  have hcon : 3 ^ climbs (fA a) (a + 2 + 5 * (3 * a)) < 2 ^ (a + 2 + 5 * (3 * a)) := by
    rw [hcl]
    exact contracts_A a
  obtain ⟨hodd, habove, hpat⟩ := realize (fA a) (a + 2 + 5 * (3 * a)) (by omega) hcon
    (fun j _ => shadow_A_ge a ha3 j) (shadow_A_end a ha3 (3 * a) (by omega))
  refine ⟨worldOf (fA a) (a + 2 + 5 * (3 * a)), walker (fA a) (a + 2 + 5 * (3 * a)), hodd,
    ?_, habove, ?_, ?_, ?_⟩
  · rw [worldOf_eq, hcl]
    refine coprime_world m (a + 2 + 5 * (3 * a)) (a + 3 * (3 * a)) (by omega) (by omega)
      (contracts_A a) ?_
    intro q hq hqm h2 h3 h
    have : Fact q.Prime := Fact.mk hq
    have P2 := two_pow_one q m hq hqm hm h2
    have P3 := three_pow_one q m hq hqm hm h3
    have e3 : (3 : ZMod q) ^ (a + 3 * (3 * a)) = 1 := by
      rw [show a + 3 * (3 * a) = m.factorial * 30 by rw [ha]; ring, pow_mul, P3, one_pow]
    have e2 : (2 : ZMod q) ^ (a + 2 + 5 * (3 * a)) = 4 := by
      rw [show a + 2 + 5 * (3 * a) = m.factorial * 48 + 2 by rw [ha]; ring, pow_add,
        pow_mul, P2, one_pow]
      norm_num
    rw [e3, e2] at h
    have h0 : ((3 : ℕ) : ZMod q) = 0 := by
      push_cast
      linear_combination -h
    have hd : q ∣ 3 := (ZMod.natCast_eq_zero_iff 3 q).mp h0
    exact h3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hd)
  · intro i hi
    obtain ⟨h0, h1, h2, -⟩ := hi
    rw [hpat] at h0 h1 h2
    exact no_CFC_A a (3 * a) i ha3 ⟨h0, h1, h2⟩
  · intro i hi
    obtain ⟨h0, h1, h2, -⟩ := hi
    rw [hpat] at h0 h1 h2
    exact no_FCF_A a (3 * a) i ha3 ⟨h0, h1, h2⟩
  · intro i hi
    obtain ⟨h0, h1, h2, h3, -⟩ := hi
    rw [hpat] at h0 h1 h2 h3
    exact no_FCCF_A a (3 * a) i ha3 ⟨h0, h1, h2, h3⟩

/-! ## The theorem -/

/-- Each of the five smallest unforced words is avoided, above home, in a world prime to
`m`. -/
theorem witness (m : ℕ) (hm : 0 < m) (u : List Bool) (hu : u ∈ minimalWords) :
    ∃ d n, d % 2 = 1 ∧ Nat.Coprime d m ∧ (∀ i, d < (Td d)^[i] n) ∧
      ∀ i, ¬ occAt (pat d n) i u := by
  simp only [minimalWords, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨d, n, h1, h2, h3, h4, _⟩ := witness_B m hm
    exact ⟨d, n, h1, h2, h3, h4⟩
  · obtain ⟨d, n, h1, h2, h3, _, h5⟩ := witness_B m hm
    exact ⟨d, n, h1, h2, h3, h5⟩
  · obtain ⟨d, n, h1, h2, h3, h4, _, _⟩ := witness_A m hm
    exact ⟨d, n, h1, h2, h3, h4⟩
  · obtain ⟨d, n, h1, h2, h3, _, h5, _⟩ := witness_A m hm
    exact ⟨d, n, h1, h2, h3, h5⟩
  · obtain ⟨d, n, h1, h2, h3, _, _, h6⟩ := witness_A m hm
    exact ⟨d, n, h1, h2, h3, h6⟩

/-- No modulus helps. For every `m` and every word outside the seven, there is a world
prime to `m`, and a walk in it that stays above home for ever and never takes the word. -/
theorem no_modulus_helps (m : ℕ) (hm : 0 < m) (w : List Bool) (hw : w ∉ forcedWords) :
    ∃ d n, d % 2 = 1 ∧ Nat.Coprime d m ∧ (∀ i, d < (Td d)^[i] n) ∧
      ∀ i, ¬ occAt (pat d n) i w := by
  obtain ⟨u, hu, hinf⟩ := contains_minimal w hw
  obtain ⟨d, n, h1, h2, h3, h4⟩ := witness m hm u hu
  refine ⟨d, n, h1, h2, h3, fun i hi => ?_⟩
  obtain ⟨j, hj⟩ := occ_of_infix _ u w hinf i hi
  exact h4 j hj

/-- So, for every `m`: the words forced in all the worlds prime to `m` are exactly the
seven. -/
theorem forced_modulo (m : ℕ) (hm : 0 < m) (w : List Bool) :
    (∀ d, d % 2 = 1 → Nat.Coprime d m → ForcedIn d w) ↔ w ∈ forcedWords := by
  constructor
  · intro h
    by_contra hw
    obtain ⟨d, n, h1, h2, h3, h4⟩ := no_modulus_helps m hm w hw
    obtain ⟨i, hi⟩ := h d h1 h2 n h3
    exact h4 i hi
  · intro hw d hd _ n hn
    exact forced_of_mem w hw d n hd hn

end Journey.NoModulus

#print axioms Journey.NoModulus.no_modulus_helps
#print axioms Journey.NoModulus.forced_modulo
