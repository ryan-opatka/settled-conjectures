import Mathlib
import SevenWords.Elsewhere

/-!
# Why three conjectures are hard

Yolcu, Aaronson and Heule ("An Automated Approach to the Collatz Conjecture", 2021 and
2023) asked, for each remainder `k` modulo 8: must every walk that never comes home stand
at some moment on a number that is `k` modulo 8? Their program proved it for 2, 3, 4 and
6. For 1, 5 and 7 it could not, and they state those three as Conjectures 4.11, 4.12 and
4.13. (I first worked from search results quoting the paper, and afterwards read Section 4.5
of its arXiv version 3 directly. The reading below held. The authors remark there that the
proved cases are not difficult to prove by hand, and their own proof of the case 6 is a
descent argument.)

A remainder modulo 8 is the same as the next three steps. So in the language of steps:

* 4.11 says every walk away from home sometimes takes climb, fall, climb.
* 4.12 says it sometimes takes climb, fall, fall.
* 4.13 says it sometimes takes three climbs in a row.

This file proves three things.

1. In every 3n + d world, a walk that stays above home must sometimes climb twice in a
   row. The reason is plain descent: a climb followed by a fall takes `n` to
   `(3 n + d) / 4`, which is smaller than `n` whenever `n` is above home. In our world
   this gives the proven case of remainder 3. It is a proof that does not care which
   world it is in.

2. In the world of 5, all three open conjectures are false, and false above home. The
   walk of 19 goes climb, climb, climb, fall, fall for ever and never takes climb, fall,
   climb. The walk of 23 goes climb, climb, fall, climb, fall for ever. It never takes
   climb, fall, fall and never climbs three times in a row.

3. Conjecture 4.12 would settle the case I left open: if it holds, then a walk that
   eventually looks like home modulo 5 is home.

For single classes modulo 8, then, what their program proved is what holds in every world
above home, and what it could not prove fails in the world next door. (Remainders 2 and 4
say that every walk sometimes turns. Remainders 3 and 6 are the descent above.)

A correction. I first read more into this than it holds, and a second reader set me right.
That a statement fails next door, even above home, does not show that it is hard for
3n + 1: `Caution` proves a statement of exactly that kind by plain descent. A proof of
4.11, 4.12 or 4.13 must use something that is false for 3n + 5, but nothing here shows
that the something must be deep. The reason these three resist descent lies inside 3n + 1
itself: a walk that avoids one of these classes may still take blocks that grow, mixed
freely with blocks that shrink. The paper's own proof of its Proposition 4.7 shows this,
and two 2026 preprints by H. Nashida make it exact: such a system is called entangled
there, and no certificate built from the logarithm, 2-adic valuations and finite-state
weights exists for it. `Caution` says more.

A computer search of every world with `d` below 400 agrees: no cycle above home avoids
the remainders 2, 3, 4 or 6, and cycles above home avoid each of 0, 1, 5 and 7.

The cycles of 3n + 5 are classical. The three conjectures are theirs. The question
behind them is older: Monks, Monks, Monks and Monks (2012) asked which sets of residues
every divergent orbit and every nontrivial cycle must meet, and the classes 3 and 6
modulo 8 are in their tables. That the cycles of 3n + 5 refute the analogues of the
conjectures is what I found. A search did not turn it up, though I cannot be sure nobody
has noticed it, and a specialist would see it at once.
-/

namespace Journey.Barrier

open Function Journey.Collatz Journey.Room Journey.Thread Journey.Elsewhere

/-! ## Three steps -/

/-- Standing on `v` in the world of `d`: the next three steps are climb, fall, climb. -/
abbrev ClimbFallClimb (d v : ℕ) : Prop :=
  v % 2 = 1 ∧ Td d v % 2 = 0 ∧ Td d (Td d v) % 2 = 1

/-- The next three steps are climb, fall, fall. -/
abbrev ClimbFallFall (d v : ℕ) : Prop :=
  v % 2 = 1 ∧ Td d v % 2 = 0 ∧ Td d (Td d v) % 2 = 0

/-- The next three steps are all climbs. -/
abbrev ThreeClimbs (d v : ℕ) : Prop :=
  v % 2 = 1 ∧ Td d v % 2 = 1 ∧ Td d (Td d v) % 2 = 1

/-- The next three steps are climb, climb, fall. -/
abbrev ClimbClimbFall (d v : ℕ) : Prop :=
  v % 2 = 1 ∧ Td d v % 2 = 1 ∧ Td d (Td d v) % 2 = 0

theorem steps_of_odd (v : ℕ) (hv : v % 2 = 1) :
    2 * Td 1 v = 3 * v + 1 ∧
      ((Td 1 v % 2 = 0 ∧ 2 * Td 1 (Td 1 v) = Td 1 v) ∨
        (Td 1 v % 2 = 1 ∧ 2 * Td 1 (Td 1 v) = 3 * Td 1 v + 1)) := by
  have h1 := two_Td 1 v (by norm_num)
  have h2 := two_Td 1 (Td 1 v) (by norm_num)
  omega

/-- In our world, climb, fall, climb is remainder 1 modulo 8. -/
theorem class_one (v : ℕ) : ClimbFallClimb 1 v ↔ v % 8 = 1 := by
  constructor
  · rintro ⟨h0, h1, h2⟩
    have := steps_of_odd v h0
    omega
  · intro h
    have := steps_of_odd v (by omega)
    refine ⟨by omega, by omega, by omega⟩

/-- Climb, fall, fall is remainder 5. -/
theorem class_five (v : ℕ) : ClimbFallFall 1 v ↔ v % 8 = 5 := by
  constructor
  · rintro ⟨h0, h1, h2⟩
    have := steps_of_odd v h0
    omega
  · intro h
    have := steps_of_odd v (by omega)
    refine ⟨by omega, by omega, by omega⟩

/-- Three climbs is remainder 7. -/
theorem class_seven (v : ℕ) : ThreeClimbs 1 v ↔ v % 8 = 7 := by
  constructor
  · rintro ⟨h0, h1, h2⟩
    have := steps_of_odd v h0
    omega
  · intro h
    have := steps_of_odd v (by omega)
    refine ⟨by omega, by omega, by omega⟩

/-- Climb, climb, fall is remainder 3. -/
theorem class_three (v : ℕ) : ClimbClimbFall 1 v ↔ v % 8 = 3 := by
  constructor
  · rintro ⟨h0, h1, h2⟩
    have := steps_of_odd v h0
    omega
  · intro h
    have := steps_of_odd v (by omega)
    refine ⟨by omega, by omega, by omega⟩

/-! ## The conjectures -/

/-- Every walk that never comes home stands at some moment on a number that is `k`
modulo 8. For `k = 1, 5, 7` these are Conjectures 4.11, 4.12 and 4.13. (Theirs are about
the walk with the values `3 n + 1` left in. For odd `k` that makes no difference.) -/
def MustVisit (k : ℕ) : Prop :=
  ∀ n, 1 ≤ n → (∀ i, T^[i] n ≠ 1) → ∃ i, T^[i] n % 8 = k

/-- The same kind of statement in any world, said in steps: every walk that never comes
home sometimes stands where the next three steps are the given ones. -/
def Sometimes (P : ℕ → ℕ → Prop) (d : ℕ) : Prop :=
  ∀ n, 1 ≤ n → (∀ i, (Td d)^[i] n ≠ d) → ∃ i, P d ((Td d)^[i] n)

theorem Td_one_eq : Td 1 = T := funext Td_one

theorem in_steps (P : ℕ → ℕ → Prop) (k : ℕ) (hP : ∀ v, P 1 v ↔ v % 8 = k) :
    MustVisit k ↔ Sometimes P 1 := by
  unfold MustVisit Sometimes
  rw [Td_one_eq]
  simp only [hP]

/-- Conjecture 4.11, in steps. -/
theorem conjecture_411_in_steps : MustVisit 1 ↔ Sometimes ClimbFallClimb 1 :=
  in_steps _ 1 class_one

/-- Conjecture 4.12, in steps. -/
theorem conjecture_412_in_steps : MustVisit 5 ↔ Sometimes ClimbFallFall 1 :=
  in_steps _ 5 class_five

/-- Conjecture 4.13, in steps. -/
theorem conjecture_413_in_steps : MustVisit 7 ↔ Sometimes ThreeClimbs 1 :=
  in_steps _ 7 class_seven

/-! ## What is true in every world: descent -/

/-- In every world, a walker that never climbs twice in a row comes down to home or
below. A fall halves it. A climb followed by a fall takes `n` to `(3 n + d) / 4`, which is
less than `n` as long as `n` is above `d`. -/
theorem comes_down (d : ℕ) (hd : d % 2 = 1) :
    ∀ n, 1 ≤ n → (∀ i, ¬ ((Td d)^[i] n % 2 = 1 ∧ (Td d)^[i + 1] n % 2 = 1)) →
      ∃ i, (Td d)^[i] n ≤ d := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn h
    by_cases hle : n ≤ d
    · exact ⟨0, hle⟩
    · rcases two_Td d n hd with ⟨hp, h2⟩ | ⟨hp, h2⟩
      · -- a fall
        have e : ∀ j, (Td d)^[j] (Td d n) = (Td d)^[j + 1] n := fun j =>
          (Function.iterate_succ_apply (Td d) j n).symm
        obtain ⟨i, hi⟩ := ih (Td d n) (by omega) (by omega) (fun i => by
          rw [e i, e (i + 1)]
          exact h (i + 1))
        exact ⟨i + 1, by rw [← e i]; exact hi⟩
      · -- a climb, which must be followed by a fall
        have h0 : ¬ (n % 2 = 1 ∧ Td d n % 2 = 1) := h 0
        have hev : Td d n % 2 = 0 := by
          by_contra hne
          exact h0 ⟨hp, by omega⟩
        rcases two_Td d (Td d n) hd with ⟨_, h3⟩ | ⟨hp', _⟩
        · have e : ∀ j, (Td d)^[j] (Td d (Td d n)) = (Td d)^[j + 2] n := fun j =>
            (Function.iterate_add_apply (Td d) j 2 n).symm
          obtain ⟨i, hi⟩ := ih (Td d (Td d n)) (by omega) (by omega) (fun i => by
            rw [e i, e (i + 1)]
            have h' := h (i + 2)
            rw [show i + 2 + 1 = i + 1 + 2 by ring] at h'
            exact h')
          exact ⟨i + 2, by rw [← e i]; exact hi⟩
        · omega

/-- So in every world, a walk that stays above home must sometimes climb twice in a
row. -/
theorem above_home_climbs_twice (d n : ℕ) (hd : d % 2 = 1) (hn : 1 ≤ n)
    (h : ∀ i, d < (Td d)^[i] n) :
    ∃ i, (Td d)^[i] n % 2 = 1 ∧ (Td d)^[i + 1] n % 2 = 1 := by
  by_contra hno
  obtain ⟨i, hi⟩ := comes_down d hd n hn (fun i hc => hno ⟨i, hc⟩)
  have := h i
  omega

/-- In our world this gives one of the cases their program proved: every walk that never
comes home stands at some moment on a number that is 3 modulo 8. If it never did, two
climbs in a row would always be followed by a third, and nobody climbs for ever. -/
theorem must_visit_three : MustVisit 3 := by
  intro n hn hnever
  by_contra hno
  have hno' : ∀ i, T^[i] n % 8 ≠ 3 := fun i hi => hno ⟨i, hi⟩
  have hs : ∀ i, T^[i + 1] n = T (T^[i] n) := fun i => Function.iterate_succ_apply' T i n
  -- two climbs in a row are always followed by a third
  have third : ∀ i, T^[i] n % 2 = 1 → T^[i + 1] n % 2 = 1 → T^[i + 2] n % 2 = 1 := by
    intro i h0 h1
    by_contra h2
    apply hno' i
    apply (class_three _).mp
    refine ⟨h0, ?_, ?_⟩
    · rw [Td_one_eq, ← hs i]
      exact h1
    · have hs2 : T^[i + 2] n = T (T^[i + 1] n) := hs (i + 1)
      rw [Td_one_eq, ← hs i, ← hs2]
      omega
  -- so there are never two climbs in a row
  have never_two : ∀ i, ¬ (T^[i] n % 2 = 1 ∧ T^[i + 1] n % 2 = 1) := by
    rintro i ⟨h0, h1⟩
    have all : ∀ j, T^[i + j] n % 2 = 1 ∧ T^[i + j + 1] n % 2 = 1 := by
      intro j
      induction j with
      | zero => exact ⟨h0, h1⟩
      | succ j ih => exact ⟨ih.2, third (i + j) ih.1 ih.2⟩
    apply never_climbs_forever n
    refine ⟨i, fun k hk => ?_⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    unfold flipAt
    simp [(all j).1]
  have hdown := comes_down 1 (by norm_num) n hn (by
    rw [Td_one_eq]
    exact never_two)
  rw [Td_one_eq] at hdown
  obtain ⟨i, hi⟩ := hdown
  have hpos := iterate_pos i n hn
  exact hnever i (by omega)

/-! ## The world of 5 -/

theorem on_cycle (d p s : ℕ) (hp : 0 < p) (hc : (Td d)^[p] s = s) (Q : ℕ → Prop)
    (hQ : ∀ r < p, Q ((Td d)^[r] s)) (i : ℕ) : Q ((Td d)^[i] s) := by
  have h := Function.IsPeriodicPt.iterate_mod_apply (f := Td d) (n := p) (x := s) hc i
  rw [← h]
  exact hQ (i % p) (Nat.mod_lt _ hp)

/-- In the world of 5, the walk of 19: 19, 31, 49, 76, 38, and 19 again.
Climb, climb, climb, fall, fall. -/
theorem walk_of_19 : (Td 5)^[5] 19 = 19 := by decide

/-- In the world of 5, the walk of 23: 23, 37, 58, 29, 46, and 23 again.
Climb, climb, fall, climb, fall. -/
theorem walk_of_23 : (Td 5)^[5] 23 = 23 := by decide

/-- The walk of 19 stays above home, never comes home, and never takes climb, fall,
climb. -/
theorem nineteen (i : ℕ) :
    10 < (Td 5)^[i] 19 ∧ (Td 5)^[i] 19 ≠ 5 ∧ ¬ ClimbFallClimb 5 ((Td 5)^[i] 19) := by
  have key : ∀ r < 5, 10 < (Td 5)^[r] 19 ∧ (Td 5)^[r] 19 ≠ 5 ∧
      ¬ ClimbFallClimb 5 ((Td 5)^[r] 19) := by decide
  exact on_cycle 5 5 19 (by norm_num) walk_of_19
    (fun v => 10 < v ∧ v ≠ 5 ∧ ¬ ClimbFallClimb 5 v) key i

/-- The walk of 23 stays above home, never comes home, never takes climb, fall, fall, and
never climbs three times in a row. -/
theorem twenty_three (i : ℕ) :
    10 < (Td 5)^[i] 23 ∧ (Td 5)^[i] 23 ≠ 5 ∧ ¬ ClimbFallFall 5 ((Td 5)^[i] 23) ∧
      ¬ ThreeClimbs 5 ((Td 5)^[i] 23) := by
  have key : ∀ r < 5, 10 < (Td 5)^[r] 23 ∧ (Td 5)^[r] 23 ≠ 5 ∧
      ¬ ClimbFallFall 5 ((Td 5)^[r] 23) ∧ ¬ ThreeClimbs 5 ((Td 5)^[r] 23) := by decide
  exact on_cycle 5 5 23 (by norm_num) walk_of_23
    (fun v => 10 < v ∧ v ≠ 5 ∧ ¬ ClimbFallFall 5 v ∧ ¬ ThreeClimbs 5 v) key i

/-- In the world of 5, the analogues of Conjectures 4.11, 4.12 and 4.13 are all false. -/
theorem all_three_fail_in_the_world_of_five :
    ¬ Sometimes ClimbFallClimb 5 ∧ ¬ Sometimes ClimbFallFall 5 ∧ ¬ Sometimes ThreeClimbs 5 := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · obtain ⟨i, hi⟩ := h 19 (by norm_num) (fun i => (nineteen i).2.1)
    exact (nineteen i).2.2 hi
  · obtain ⟨i, hi⟩ := h 23 (by norm_num) (fun i => (twenty_three i).2.1)
    exact (twenty_three i).2.2.1 hi
  · obtain ⟨i, hi⟩ := h 23 (by norm_num) (fun i => (twenty_three i).2.1)
    exact (twenty_three i).2.2.2 hi

/-- And they fail above home, where descent has nothing to say: both walks stay above
home for ever, and each does climb twice in a row, as every walk above home must. -/
theorem they_fail_above_home :
    (∀ i, 10 < (Td 5)^[i] 19) ∧ (∀ i, 10 < (Td 5)^[i] 23) :=
  ⟨fun i => (nineteen i).1, fun i => (twenty_three i).1⟩

/-! ## The case I left open -/

/-- A walk that looks like home modulo 5 never stands on a number that is 5 modulo 8.
After such a number come two falls in a row, and a walk that looks like home modulo 5
climbs at every second step. -/
theorem never_five_mod_eight (x : ℕ) (h1 : T x % 5 = 1 ∨ T x % 5 = 2)
    (h2 : T (T x) % 5 = 1 ∨ T (T x) % 5 = 2)
    (h3 : T (T (T x)) % 5 = 1 ∨ T (T (T x)) % 5 = 2) : x % 8 ≠ 5 := by
  intro hx
  have f1 := Bases.what_five_does_force (T x) h1 h2
  have f2 := Bases.what_five_does_force (T (T x)) h2 h3
  have t1 := Bases.two_T x
  have t2 := Bases.two_T (T x)
  omega

/-- Conjecture 4.12 would settle the case of 5: if every walk that never comes home
stands somewhere on a number that is 5 modulo 8, then a walk that eventually looks like
home modulo 5 is home. -/
theorem conjecture_412_would_settle_five (h : MustVisit 5) (n : ℕ) (hn : 1 ≤ n)
    (hl : Bases.LooksHome 5 n) : ∃ i, T^[i] n = 1 := by
  obtain ⟨N, hN⟩ := hl
  by_contra hno
  have hm : 1 ≤ T^[N] n := iterate_pos N n hn
  have hnever : ∀ i, T^[i] (T^[N] n) ≠ 1 := fun i hi =>
    hno ⟨i + N, by rw [Function.iterate_add_apply]; exact hi⟩
  obtain ⟨i, hi⟩ := h (T^[N] n) hm hnever
  have key : ∀ j, T^[j] (T^[N] n) % 5 = 1 ∨ T^[j] (T^[N] n) % 5 = 2 := fun j => by
    rw [← Function.iterate_add_apply]
    exact hN (j + N) (by omega)
  have s : ∀ j, T^[j + 1] (T^[N] n) = T (T^[j] (T^[N] n)) := fun j =>
    Function.iterate_succ_apply' T j _
  have k1 := key (i + 1)
  have k2 := key (i + 2)
  have k3 := key (i + 3)
  rw [s (i + 2), s (i + 1), s i] at k3
  rw [s (i + 1), s i] at k2
  rw [s i] at k1
  exact never_five_mod_eight _ k1 k2 k3 hi

/-- And in the world of 13, where the case of 5 fails, so does the analogue of 4.12: the
walk of 283 never takes climb, fall, fall. The two failures are the same failure. -/
theorem two_eighty_three (i : ℕ) : ¬ ClimbFallFall 13 ((Td 13)^[i] 283) := by
  have key : ∀ r < 8, ¬ ClimbFallFall 13 ((Td 13)^[r] 283) := by decide
  exact on_cycle 13 8 283 (by norm_num) walk_of_283 (fun v => ¬ ClimbFallFall 13 v) key i

end Journey.Barrier

#print axioms Journey.Barrier.above_home_climbs_twice
#print axioms Journey.Barrier.must_visit_three
#print axioms Journey.Barrier.all_three_fail_in_the_world_of_five
#print axioms Journey.Barrier.conjecture_412_would_settle_five
#print axioms Journey.Barrier.conjecture_412_in_steps
