import Mathlib
import SevenWords.Targets

/-!
# A caution: refuted next door, and still easy

In `Barrier`, `Seven` and `NoModulus` I drew a conclusion from the theorems that the
theorems do not support. I said that when the analogue of a statement fails in another
3n + d world, above home, a proof of the statement for 3n + 1 must be hard, or at least
must reach beyond descent. A second reader, checking the note, gave a counterexample. This
file proves it.

**The statement.** Every walk that never comes home stands somewhere on a number that is
1 modulo 8 or 15 modulo 64. In steps: it takes climb, fall, climb, or it takes four climbs
and then two falls.

**It is true for 3n + 1, by plain descent.** A walk that avoids both can only move in
blocks of at most three climbs followed by at least two falls. Each such block makes the
number smaller. The last case needs `(27 n + 19) / 32 < n`, which holds once `n` is above
19/5, and every odd number whose next steps are climb, climb, climb, fall, fall is at
least 23.

**It is false next door, above home.** In the world of 5, the walk of 19 goes climb,
climb, climb, fall, fall for ever. It takes neither word, and it never comes near home.
And 19/5 is exactly the fixed point of `x ↦ (27 x + 19) / 32`.

So being refuted in another world, even above home, says nothing by itself about how hard
a statement is for 3n + 1. The fact about 3n + 1 that the proof uses here is only that no
whole number with those five steps ahead of it is as small as 3.8.

What does make the three open conjectures resist descent is visible inside 3n + 1 alone:
a walk that avoids one of those classes may still take blocks that grow (climb, climb,
fall grows by 9/8), mixed freely with blocks that shrink. That criterion is not mine. It
is in the paper's own proof of its Proposition 4.7, and two 2026 preprints by H. Nashida
make it exact. I have now read them. There a map is called *entangled* when a growing
cycle of its graph on residues shares a strongly connected component with a branching.
The main theorem says that a terminating map of this kind has a certificate built from
the logarithm, 2-adic valuations and finite-state weights exactly when it is not
entangled. The Collatz map halted on any one of the classes 1, 5, 7 modulo 8 is entangled.

**The statement proved here is not new.** It is the first half of Theorem 8.2(a) of
Nashida's second preprint. It is proved there in Lean, and shown there to be best
possible in a precise sense: among single classes that such certificates can add to
1 modulo 8, the class 15 modulo 64 is maximal. The credit for the theorem is Nashida's.
What this file adds is only the comparison with the world of 5.

The question is older than the 2021 paper. Monks, Monks, Monks and Monks (2012) call a
set of residues *forward sufficient* when every divergent orbit meets it and *cycle
sufficient* when every nontrivial cycle does, and their tables hold many such sets,
among them {1, 5} and {1, 7} modulo 8 and {9, 15} modulo 16. Their criterion for cycles
rests on a computed fact about 3n + 1, that it has no short nontrivial cycle. That is
exactly the fact the world of 5 lacks.

The theorems of the earlier files stand. Their interpretation is corrected here.
-/

namespace Journey.Caution

open Function Journey.Collatz Journey.Room Journey.Thread Journey.Elsewhere Journey.Barrier
  Journey.Seven

-- The step map is only ever used here through its two defining equations. Unfolding it
-- inside nested expressions makes the elaborator do exponential work, so it is sealed.
attribute [local irreducible] Journey.Collatz.T

/-- A walk never stands on a number that is 1 modulo 8 or 15 modulo 64. -/
def Avoids (n : ℕ) : Prop := ∀ i, T^[i] n % 8 ≠ 1 ∧ T^[i] n % 64 ≠ 15

theorem avoids_tail (n j : ℕ) (h : Avoids n) : Avoids (T^[j] n) := fun i => by
  rw [← Function.iterate_add_apply]
  exact h (i + j)

theorem odd_step (x : ℕ) (h : x % 2 = 1) : 2 * T x = 3 * x + 1 := by
  rcases Bases.two_T x with ⟨hp, _⟩ | ⟨_, e⟩
  · omega
  · exact e

theorem even_step (x : ℕ) (h : x % 2 = 0) : 2 * T x = x := by
  rcases Bases.two_T x with ⟨_, e⟩ | ⟨hp, _⟩
  · exact e
  · omega

theorem back1 (a b : ℕ) (e : 2 * b = a) (h : b % 2 = 0) : a % 4 = 0 := by omega

theorem back2 (a b : ℕ) (e : 2 * b = 3 * a + 1) (h : b % 4 = 0) : a % 8 = 5 := by omega

theorem back3 (a b : ℕ) (e : 2 * b = 3 * a + 1) (h : b % 8 = 5) : a % 16 = 3 := by omega

theorem back4 (a b : ℕ) (e : 2 * b = 3 * a + 1) (h : b % 16 = 3) : a % 32 = 23 := by omega

theorem back5 (a b : ℕ) (e : 2 * b = 3 * a + 1) (h : b % 32 = 23) : a % 64 = 15 := by omega

/-- Four climbs and then two falls: the number is 15 modulo 64. Read backwards from the
second fall, each step fixes one more binary digit. -/
theorem six_steps (y : ℕ) (h0 : y % 2 = 1) (h1 : T y % 2 = 1) (h2 : T (T y) % 2 = 1)
    (h3 : T (T (T y)) % 2 = 1) (h4 : T (T (T (T y))) % 2 = 0)
    (h5 : T (T (T (T (T y)))) % 2 = 0) : y % 64 = 15 :=
  back5 _ _ (odd_step y h0)
    (back4 _ _ (odd_step (T y) h1)
      (back3 _ _ (odd_step (T (T y)) h2)
        (back2 _ _ (odd_step (T (T (T y))) h3)
          (back1 _ _ (even_step (T (T (T (T y)))) h4) h5))))

/-- Climb, fall, climb: the number is 1 modulo 8. -/
theorem cfc (x : ℕ) (h0 : x % 2 = 1) (h1 : T x % 2 = 0) (h2 : T (T x) % 2 = 1) :
    x % 8 = 1 := by
  have e0 := odd_step x h0
  generalize T x = z1 at e0 h1 h2
  have e1 := even_step z1 h1
  generalize T z1 = z2 at e1 h2
  omega

/-- One climb and two falls end lower. -/
theorem block1 (n : ℕ) (h : n % 8 = 5) : T (T (T n)) < n := by
  have e0 := odd_step n (by omega)
  generalize T n = z1 at e0 ⊢
  have e1 := even_step z1 (by omega)
  generalize T z1 = z2 at e1 ⊢
  have e2 := even_step z2 (by omega)
  generalize T z2 = z3 at e2 ⊢
  omega

/-- Two climbs and two falls end lower. -/
theorem block2 (n : ℕ) (h : n % 8 = 3) (h1 : T n % 8 ≠ 1) : T (T (T (T n))) < n := by
  have e0 := odd_step n (by omega)
  generalize T n = z1 at e0 h1 ⊢
  have e1 := odd_step z1 (by omega)
  generalize T z1 = z2 at e1 ⊢
  have e2 := even_step z2 (by omega)
  generalize T z2 = z3 at e2 ⊢
  have e3 := even_step z3 (by omega)
  generalize T z3 = z4 at e3 ⊢
  omega

/-- Three climbs and two falls end lower. This is the step that uses a fact about whole
numbers: `(27 n + 19) / 32 < n` needs `n > 19/5`, and here `n` is at least 7. -/
theorem block3 (n : ℕ) (h : n % 16 = 7) (h2 : T (T n) % 8 ≠ 1) :
    T (T (T (T (T n)))) < n := by
  have e0 := odd_step n (by omega)
  generalize T n = z1 at e0 h2 ⊢
  have e1 := odd_step z1 (by omega)
  generalize T z1 = z2 at e1 h2 ⊢
  have e2 := odd_step z2 (by omega)
  generalize T z2 = z3 at e2 ⊢
  have e3 := even_step z3 (by omega)
  generalize T z3 = z4 at e3 ⊢
  have e4 := even_step z4 (by omega)
  generalize T z4 = z5 at e4 ⊢
  omega

/-- A number that is 15 modulo 16 climbs at least four times. -/
theorem four_climbs (n : ℕ) (h : n % 16 = 15) :
    n % 2 = 1 ∧ T n % 2 = 1 ∧ T (T n) % 2 = 1 ∧ T (T (T n)) % 2 = 1 := by
  have e0 := odd_step n (by omega)
  generalize T n = z1 at e0 ⊢
  have e1 := odd_step z1 (by omega)
  generalize T z1 = z2 at e1 ⊢
  have e2 := odd_step z2 (by omega)
  generalize T z2 = z3 at e2 ⊢
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- Every walk falls at some step, and before its first fall it only climbs. -/
theorem first_fall (n : ℕ) : ∃ i0, T^[i0] n % 2 = 0 ∧ ∀ k, k < i0 → T^[k] n % 2 = 1 := by
  have hex : ∃ i, T^[i] n % 2 = 0 := by
    by_contra hno
    apply never_climbs_forever n
    refine ⟨0, fun i _ => ?_⟩
    have h0 : ¬ T^[i] n % 2 = 0 := fun hh => hno ⟨i, hh⟩
    have h1 : T^[i] n % 2 = 1 := by omega
    simp [flipAt, h1]
  exact ⟨Nat.find hex, Nat.find_spec hex, fun k hk => by
    have := Nat.find_min hex hk
    omega⟩

/-- When four climbs end, either the last of them is 1 modulo 8 or the first is 15
modulo 64. -/
theorem end_of_climb (y : ℕ) (y0 : y % 2 = 1) (y1 : T y % 2 = 1) (y2 : T (T y) % 2 = 1)
    (y3 : T (T (T y)) % 2 = 1) (y4 : T (T (T (T y))) % 2 = 0) :
    T (T (T y)) % 8 = 1 ∨ y % 64 = 15 := by
  rcases Nat.mod_two_eq_zero_or_one (T (T (T (T (T y))))) with p5 | p5
  · exact Or.inr (six_steps y y0 y1 y2 y3 y4 p5)
  · exact Or.inl (cfc (T (T (T y))) y3 y4 p5)

/-- Four climbs or more: when the climbing stops, one of the two classes is met. -/
theorem long_climb_meets (n : ℕ) (h15 : n % 16 = 15) (h : Avoids n) : False := by
  obtain ⟨c0, c1, c2, c3⟩ := four_climbs n h15
  obtain ⟨i0, hspec, hmin⟩ := first_fall n
  rcases Nat.lt_or_ge i0 4 with hlt | h4
  · -- the first fall cannot come within the first four steps
    interval_cases i0
    · have e : n % 2 = 0 := hspec
      rw [c0] at e
      exact absurd e (by norm_num)
    · have e : T n % 2 = 0 := hspec
      rw [c1] at e
      exact absurd e (by norm_num)
    · have e : T (T n) % 2 = 0 := hspec
      rw [c2] at e
      exact absurd e (by norm_num)
    · have e : T (T (T n)) % 2 = 0 := hspec
      rw [c3] at e
      exact absurd e (by norm_num)
  · obtain ⟨q, rfl⟩ : ∃ q, i0 = q + 4 := ⟨i0 - 4, (Nat.sub_add_cancel h4).symm⟩
    have v1 : T^[q + 1] n = T (T^[q] n) := Function.iterate_succ_apply' T q n
    have v2 : T^[q + 2] n = T (T (T^[q] n)) := by
      rw [← v1]
      exact Function.iterate_succ_apply' T (q + 1) n
    have v3 : T^[q + 3] n = T (T (T (T^[q] n))) := by
      rw [← v2]
      exact Function.iterate_succ_apply' T (q + 2) n
    have v4 : T^[q + 4] n = T (T (T (T (T^[q] n)))) := by
      rw [← v3]
      exact Function.iterate_succ_apply' T (q + 3) n
    have y0 : T^[q] n % 2 = 1 := hmin q (Nat.lt_add_of_pos_right (by norm_num))
    have y1 : T (T^[q] n) % 2 = 1 := by
      rw [← v1]
      exact hmin (q + 1) (Nat.add_lt_add_left (by norm_num) q)
    have y2 : T (T (T^[q] n)) % 2 = 1 := by
      rw [← v2]
      exact hmin (q + 2) (Nat.add_lt_add_left (by norm_num) q)
    have y3 : T (T (T (T^[q] n))) % 2 = 1 := by
      rw [← v3]
      exact hmin (q + 3) (Nat.add_lt_add_left (by norm_num) q)
    have y4 : T (T (T (T (T^[q] n)))) % 2 = 0 := by
      rw [← v4]
      exact hspec
    rcases end_of_climb (T^[q] n) y0 y1 y2 y3 y4 with e | e
    · rw [← v3] at e
      exact (h (q + 3)).1 e
    · exact (h q).2 e

/-- A walk that avoids both classes reaches a smaller number. -/
theorem drops (n : ℕ) (hn : 2 ≤ n) (h : Avoids n) : ∃ j, T^[j] n < n := by
  have a0 : n % 8 ≠ 1 ∧ n % 64 ≠ 15 := h 0
  have a1 : T n % 8 ≠ 1 ∧ T n % 64 ≠ 15 := h 1
  have a2 : T (T n) % 8 ≠ 1 ∧ T (T n) % 64 ≠ 15 := h 2
  rcases Nat.mod_two_eq_zero_or_one n with hp | hp
  · have e := even_step n hp
    refine ⟨1, ?_⟩
    change T n < n
    generalize T n = z at e ⊢
    omega
  · by_cases h5 : n % 8 = 5
    · exact ⟨3, block1 n h5⟩
    · by_cases h3 : n % 8 = 3
      · exact ⟨4, block2 n h3 a1.1⟩
      · by_cases h7 : n % 16 = 7
        · exact ⟨5, block3 n h7 a2.1⟩
        · have h15 : n % 16 = 15 := by
            have := a0.1
            clear a1 a2 h
            omega
          exact (long_climb_meets n h15 h).elim

/-- So a walk that avoids both classes comes home. -/
theorem reaches (n : ℕ) : 1 ≤ n → Avoids n → ∃ i, T^[i] n = 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn h
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · exact ⟨0, by
        change n = 1
        omega⟩
    · obtain ⟨j, hj⟩ := drops n h2 h
      obtain ⟨i, hi⟩ := ih (T^[j] n) hj (iterate_pos j n hn) (avoids_tail n j h)
      exact ⟨i + j, by
        rw [Function.iterate_add_apply]
        exact hi⟩

/-- True for 3n + 1: every walk that never comes home stands somewhere on a number that is
1 modulo 8 or 15 modulo 64. -/
theorem one_or_fifteen (n : ℕ) (hn : 1 ≤ n) (hne : ∀ i, T^[i] n ≠ 1) :
    ∃ i, T^[i] n % 8 = 1 ∨ T^[i] n % 64 = 15 := by
  by_contra hno
  have hav : Avoids n := fun i =>
    ⟨fun h => hno ⟨i, Or.inl h⟩, fun h => hno ⟨i, Or.inr h⟩⟩
  obtain ⟨i, hi⟩ := reaches n hn hav
  exact hne i hi

/-- False next door: in the world of 5 the walk of 19 stays above home, never takes climb,
fall, climb, and never takes four climbs and two falls. -/
theorem next_door :
    (∀ i, 10 < (Td 5)^[i] 19) ∧ (∀ i, ¬ occAt (pat 5 19) i [true, false, true]) ∧
      (∀ i, ¬ occAt (pat 5 19) i [true, true, true, true, false, false]) :=
  ⟨fun i => (nineteen i).1,
    never_on_cycle 5 5 19 (by norm_num) walk_of_19 _ (by decide),
    never_on_cycle 5 5 19 (by norm_num) walk_of_19 _ (by decide)⟩

/-- The caution, in one statement. A claim about 3n + 1 can be true by plain descent while
its analogue is false in another world, above home. -/
theorem refuted_next_door_and_still_true :
    (∀ n, 1 ≤ n → (∀ i, T^[i] n ≠ 1) → ∃ i, T^[i] n % 8 = 1 ∨ T^[i] n % 64 = 15) ∧
      ((∀ i, 10 < (Td 5)^[i] 19) ∧ (∀ i, ¬ occAt (pat 5 19) i [true, false, true]) ∧
        (∀ i, ¬ occAt (pat 5 19) i [true, true, true, true, false, false])) :=
  ⟨one_or_fifteen, next_door⟩

/-- The analogue of Conjecture 4.14 fails in the world of 5 as well: the walk of 23 never
takes climb, fall, fall and never climbs three times running. -/
theorem analogue_of_4_14_fails :
    ¬ Sometimes (fun d v => ClimbFallFall d v ∨ ThreeClimbs d v) 5 := by
  intro h
  obtain ⟨i, hi⟩ := h 23 (by norm_num) (fun i => (twenty_three i).2.1)
  rcases hi with hi | hi
  · exact (twenty_three i).2.2.1 hi
  · exact (twenty_three i).2.2.2 hi

/-- The same failure in the paper's own terms. Its Proposition 4.15 turns Conjecture 4.14
into the statement that the map `H`, which sends `n` to `3 n / 4` when `n` is 0 modulo 4
and to `(9 n + 1) / 8` when `n` is 7 modulo 8, has no endless walk. Among fractions it has
one: 4/5 goes to 3/5, and 3/5 goes back to 4/5. -/
theorem cycle_of_H : 3 * (4 / 5 : ℚ) / 4 = 3 / 5 ∧ (9 * (3 / 5 : ℚ) + 1) / 8 = 4 / 5 := by
  norm_num

end Journey.Caution

#print axioms Journey.Caution.refuted_next_door_and_still_true
#print axioms Journey.Caution.analogue_of_4_14_fails
