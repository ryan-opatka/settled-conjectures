import Mathlib
import SevenWords.Basics

/-!
# The exception at five is real, elsewhere

The last file left one modulus open. A walk that eventually leaves only the remainders of
1 and 2 must be home, for modulus 4 and for every modulus from 6 up. For modulus 5 the
argument failed and I did not know whether the exception was real.

Here is where I looked. Our walkers have cousins. For any odd `d`, the world of `d` has the
step `n ↦ n / 2` for even `n` and `n ↦ (3 n + d) / 2` for odd `n`. Home there is the cycle
of `d` and `2 d`. A walker `n` in the world of `d` is the same as the rational walker
`n / d` in our own world, so these are not strangers. They are our own walk, continued to
the fractions with odd denominator.

Two things are proved.

* In every world `d`, and for every modulus prime to `d` that is 4 or at least 6, a walk
  that eventually looks like home is home. The list of exceptions is the same everywhere.
* In the world of 13, modulus 5 is a real exception. The walk of 283 returns to itself
  after eight steps, never reaches home, and at every step looks like home modulo 5.

So a proof that looking like home modulo 5 means being home, in our world, must use
something that is false in the world of 13. I first wrote that this is a statement about
how hard the question is. It is not. `Caution` shows that such a something can be as small
as a fact about a few small whole numbers. All I can say is that I know no proof.

In our own world, said with fractions: the number 986/13 walks a cycle of eight steps,
fall, climb, fall, climb, fall, climb, climb, climb. It is positive. It never comes home.
And modulo 5 it looks like home forever.

In our own world the case of 5 stays open. The next file shows it would follow from an
open conjecture of Yolcu, Aaronson and Heule.

The cycles of the 3n + d worlds are classical: Lagarias studied them as the rational
cycles of the 3x + 1 problem. That one of them hides behind home modulo 5 is what I found.
A search of every world with `d` below 400 found this cycle and its multiples, and nothing
at all for the moduli 4, 6, 7, 8, 9 and 11, as the theorem says.
-/

namespace Journey.Elsewhere

open Function

/-- One step in the world of `d`. -/
def Td (d n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else (3 * n + d) / 2

/-- The world of 1 is our own. -/
theorem Td_one (n : ℕ) : Td 1 n = Journey.Collatz.T n := rfl

theorem two_Td (d x : ℕ) (hd : d % 2 = 1) :
    (x % 2 = 0 ∧ 2 * Td d x = x) ∨ (x % 2 = 1 ∧ 2 * Td d x = 3 * x + d) := by
  unfold Td
  split_ifs with h
  · left
    omega
  · right
    omega

/-- Home in the world of `d`: from `d` a climb to `2 d`, from `2 d` a fall to `d`. -/
theorem home_step (d : ℕ) (hd : d % 2 = 1) : Td d d = 2 * d ∧ Td d (2 * d) = d := by
  constructor
  · unfold Td
    split_ifs <;> omega
  · unfold Td
    split_ifs <;> omega

/-- From some moment on, the walk stands only on numbers that look like `d` or `2 d`
modulo `M`. -/
def LooksHome (d M n : ℕ) : Prop :=
  ∃ N, ∀ i, N ≤ i → (Td d)^[i] n ≡ d [MOD M] ∨ (Td d)^[i] n ≡ 2 * d [MOD M]

/-! ## The same exceptions in every world -/

theorem not_dvd_small (M d k : ℕ) (hc : Nat.Coprime M d) (hM : M = 4 ∨ 6 ≤ M)
    (hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 5) (h : M ∣ k * d) : False := by
  have h1 : M ∣ k := hc.dvd_of_dvd_mul_right h
  rcases hk with rfl | rfl | rfl | rfl
  · have := Nat.le_of_dvd (by norm_num) h1
    omega
  · have := Nat.le_of_dvd (by norm_num) h1
    omega
  · have := Nat.le_of_dvd (by norm_num) h1
    omega
  · rcases (Nat.dvd_prime Nat.prime_five).mp h1 with e | e <;> omega

/-- One number cannot look like two things that differ by 1, 2, 3 or 5 times `d`. -/
theorem clash (M d k A B x : ℕ) (hc : Nat.Coprime M d) (hM : M = 4 ∨ 6 ≤ M)
    (hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 5) (hA : x ≡ A [MOD M]) (hB : x ≡ B [MOD M])
    (hAB : B = A + k * d) : False := by
  have h : A ≡ B [MOD M] := hA.symm.trans hB
  have h1 : M ∣ B - A := (Nat.modEq_iff_dvd' (by omega)).mp h
  rw [show B - A = k * d by omega] at h1
  exact not_dvd_small M d k hc hM hk h1

/-- In any world, modulo anything prime to `d` that is 4 or at least 6: a number that
looks like home, and whose next step looks like home, steps the way home steps. -/
theorem steps_like_home (d M x : ℕ) (hd : d % 2 = 1) (hc : Nat.Coprime M d)
    (hM : M = 4 ∨ 6 ≤ M)
    (hx : x ≡ d [MOD M] ∨ x ≡ 2 * d [MOD M])
    (hT : Td d x ≡ d [MOD M] ∨ Td d x ≡ 2 * d [MOD M]) :
    (x % 2 = 1 ∧ x ≡ d [MOD M] ∧ Td d x ≡ 2 * d [MOD M]) ∨
      (x % 2 = 0 ∧ x ≡ 2 * d [MOD M] ∧ Td d x ≡ d [MOD M]) := by
  rcases two_Td d x hd with ⟨hp, h2⟩ | ⟨hp, h2⟩
  · -- a fall: `x = 2 * Td d x`
    have e : ∀ r, Td d x ≡ r [MOD M] → x ≡ 2 * r [MOD M] := by
      intro r hr
      have h3 := hr.mul_left 2
      rwa [h2] at h3
    rcases hx with hx | hx
    · rcases hT with hT | hT
      · exact (clash M d 1 d (2 * d) x hc hM (by simp) hx (e d hT) (by omega)).elim
      · exact (clash M d 3 d (2 * (2 * d)) x hc hM (by simp) hx (e _ hT) (by omega)).elim
    · rcases hT with hT | hT
      · exact Or.inr ⟨hp, hx, hT⟩
      · exact (clash M d 2 (2 * d) (2 * (2 * d)) x hc hM (by simp) hx (e _ hT)
          (by omega)).elim
  · -- a climb: `2 * Td d x = 3 * x + d`
    have e : ∀ r, Td d x ≡ r [MOD M] → 2 * Td d x ≡ 2 * r [MOD M] := fun r hr =>
      hr.mul_left 2
    have f : ∀ s, x ≡ s [MOD M] → 2 * Td d x ≡ 3 * s + d [MOD M] := by
      intro s hs
      have h3 := (hs.mul_left 3).add_right d
      rwa [← h2] at h3
    rcases hx with hx | hx
    · rcases hT with hT | hT
      · exact (clash M d 2 (2 * d) (3 * d + d) _ hc hM (by simp) (e d hT) (f d hx)
          (by omega)).elim
      · exact Or.inl ⟨hp, hx, hT⟩
    · rcases hT with hT | hT
      · exact (clash M d 5 (2 * d) (3 * (2 * d) + d) _ hc hM (by simp) (e d hT) (f _ hx)
          (by omega)).elim
      · exact (clash M d 3 (2 * (2 * d)) (3 * (2 * d) + d) _ hc hM (by simp) (e _ hT)
          (f _ hx) (by omega)).elim

/-- In every world, for every modulus prime to `d` that is 4 or at least 6, looking like
home is being home.

From an odd moment on, every two steps send `x` to `(3 x + d) / 4`, so the distance from
`d` is multiplied by `3 / 4` each time and stays a whole number. Only zero can do that. -/
theorem looks_home_is_home (d M n : ℕ) (hd : d % 2 = 1) (hc : Nat.Coprime M d)
    (hM : M = 4 ∨ 6 ≤ M) (h : LooksHome d M n) : ∃ i, (Td d)^[i] n = d := by
  obtain ⟨N, hN⟩ := h
  have hs : ∀ i, (Td d)^[i + 1] n = Td d ((Td d)^[i] n) := fun i =>
    Function.iterate_succ_apply' (Td d) i n
  -- the state of the walk at every moment from `N` on
  have st : ∀ i, N ≤ i →
      ((Td d)^[i] n % 2 = 1 ∧ (Td d)^[i] n ≡ d [MOD M] ∧ (Td d)^[i + 1] n ≡ 2 * d [MOD M]) ∨
      ((Td d)^[i] n % 2 = 0 ∧ (Td d)^[i] n ≡ 2 * d [MOD M] ∧ (Td d)^[i + 1] n ≡ d [MOD M]) := by
    intro i hi
    have h1 := hN (i + 1) (by omega)
    rw [hs i] at h1 ⊢
    exact steps_like_home d M _ hd hc hM (hN i hi) h1
  -- looking like `d` means being odd
  have odd_of : ∀ i, N ≤ i → (Td d)^[i] n ≡ d [MOD M] → (Td d)^[i] n % 2 = 1 := by
    intro i hi hx
    rcases st i hi with ⟨hp, _, _⟩ | ⟨_, hx', _⟩
    · exact hp
    · exact (clash M d 1 d (2 * d) _ hc hM (by simp) hx hx' (by omega)).elim
  have even_of : ∀ i, N ≤ i → (Td d)^[i] n ≡ 2 * d [MOD M] → (Td d)^[i] n % 2 = 0 := by
    intro i hi hx
    rcases st i hi with ⟨_, hx', _⟩ | ⟨hp, _, _⟩
    · exact (clash M d 1 d (2 * d) _ hc hM (by simp) hx' hx (by omega)).elim
    · exact hp
  -- two steps from an odd moment
  have two : ∀ i, N ≤ i → (Td d)^[i] n % 2 = 1 →
      (Td d)^[i + 2] n % 2 = 1 ∧ 4 * (Td d)^[i + 2] n = 3 * (Td d)^[i] n + d := by
    intro i hi hodd
    rcases st i hi with ⟨_, _, hnext⟩ | ⟨hp, _, _⟩
    · have hev := even_of (i + 1) (by omega) hnext
      rcases st (i + 1) (by omega) with ⟨hp, _, _⟩ | ⟨_, _, hnn⟩
      · omega
      · have hodd2 := odd_of (i + 2) (by omega) hnn
        refine ⟨hodd2, ?_⟩
        have hs2 : (Td d)^[i + 2] n = Td d ((Td d)^[i + 1] n) := hs (i + 1)
        have a1 := two_Td d ((Td d)^[i] n) hd
        have a2 := two_Td d ((Td d)^[i + 1] n) hd
        rw [← hs i] at a1
        rw [← hs2] at a2
        omega
    · omega
  -- an odd moment at or after `N`
  obtain ⟨i0, hi0, hodd0⟩ : ∃ i0, N ≤ i0 ∧ (Td d)^[i0] n % 2 = 1 := by
    rcases st N le_rfl with ⟨hp, _, _⟩ | ⟨_, _, hnext⟩
    · exact ⟨N, le_rfl, hp⟩
    · exact ⟨N + 1, by omega, odd_of (N + 1) (by omega) hnext⟩
  -- the distance from `d` is multiplied by 3/4 every two steps
  have chain : ∀ j, (Td d)^[i0 + 2 * j] n % 2 = 1 ∧
      (4 : ℤ) ^ j * (((Td d)^[i0 + 2 * j] n : ℤ) - d) = 3 ^ j * (((Td d)^[i0] n : ℤ) - d) := by
    intro j
    induction j with
    | zero => exact ⟨hodd0, by simp⟩
    | succ j ih =>
      obtain ⟨ho, he⟩ := ih
      obtain ⟨ho2, h4⟩ := two (i0 + 2 * j) (by omega) ho
      have h4' : (4 : ℤ) * ((Td d)^[i0 + 2 * j + 2] n : ℤ) =
          3 * ((Td d)^[i0 + 2 * j] n : ℤ) + d := by exact_mod_cast h4
      refine ⟨ho2, ?_⟩
      change (4 : ℤ) ^ (j + 1) * (((Td d)^[i0 + 2 * j + 2] n : ℤ) - d) = _
      calc (4 : ℤ) ^ (j + 1) * (((Td d)^[i0 + 2 * j + 2] n : ℤ) - d)
          = 4 ^ j * (4 * ((Td d)^[i0 + 2 * j + 2] n : ℤ) - 4 * d) := by ring
        _ = 4 ^ j * (3 * (((Td d)^[i0 + 2 * j] n : ℤ) - d)) := by rw [h4']; ring
        _ = 3 * (4 ^ j * (((Td d)^[i0 + 2 * j] n : ℤ) - d)) := by ring
        _ = 3 ^ (j + 1) * (((Td d)^[i0] n : ℤ) - d) := by rw [he]; ring
  -- so every power of 4 divides it, and it is zero
  refine ⟨i0, ?_⟩
  set x := (Td d)^[i0] n with hx
  have hdiv : ∀ j, (4 : ℤ) ^ j ∣ (x : ℤ) - d := by
    intro j
    have hcop : IsCoprime ((4 : ℤ) ^ j) ((3 : ℤ) ^ j) :=
      IsCoprime.pow ⟨1, -1, by norm_num⟩
    exact hcop.dvd_of_dvd_mul_left ⟨_, (chain j).2.symm⟩
  have hlt : x + d < 4 ^ (x + d) := Nat.lt_pow_self (by norm_num)
  have hlt' : ((x : ℤ) + d) < 4 ^ (x + d) := by exact_mod_cast hlt
  have hx0 : (0 : ℤ) ≤ x := Int.natCast_nonneg x
  have hd0 : (0 : ℤ) ≤ d := Int.natCast_nonneg d
  have habs : |(x : ℤ) - d| < 4 ^ (x + d) := abs_lt.mpr ⟨by linarith, by linarith⟩
  have hzero := Int.eq_zero_of_abs_lt_dvd (hdiv (x + d)) habs
  omega

/-- The conjecture of each world, modulo `M`: there, everyone comes home exactly when
everyone eventually looks like home. -/
theorem the_conjecture_of_each_world (d M : ℕ) (hd : d % 2 = 1) (hc : Nat.Coprime M d)
    (hM : M = 4 ∨ 6 ≤ M) :
    (∀ n, 1 ≤ n → ∃ i, (Td d)^[i] n = d) ↔ (∀ n, 1 ≤ n → LooksHome d M n) := by
  constructor
  · intro h n hn
    obtain ⟨N, hN⟩ := h n hn
    have hh := home_step d hd
    have after : ∀ j, (Td d)^[N + j] n = d ∨ (Td d)^[N + j] n = 2 * d := by
      intro j
      induction j with
      | zero => exact Or.inl hN
      | succ j ih =>
        change (Td d)^[(N + j) + 1] n = d ∨ (Td d)^[(N + j) + 1] n = 2 * d
        rw [Function.iterate_succ_apply']
        rcases ih with e | e
        · right
          rw [e, hh.1]
        · left
          rw [e, hh.2]
    refine ⟨N, fun i hi => ?_⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
    rcases after j with e | e
    · left
      rw [e]
    · right
      rw [e]
  · intro h n hn
    exact looks_home_is_home d M n hd hc hM (h n hn)

/-! ## The world of 13 -/

/-- In the world of 13, the walk of 283 returns to itself after eight steps:
283, 431, 653, 986, 493, 746, 373, 566, and 283 again. -/
theorem walk_of_283 : (Td 13)^[8] 283 = 283 := by decide

theorem walk_of_283_mod (i : ℕ) : (Td 13)^[i] 283 = (Td 13)^[i % 8] 283 :=
  (Function.IsPeriodicPt.iterate_mod_apply (f := Td 13) (n := 8) (x := 283) walk_of_283 i).symm

/-- At every step it looks like home modulo 5. -/
theorem looks_home_at_five : LooksHome 13 5 283 := by
  refine ⟨0, fun i _ => ?_⟩
  rw [walk_of_283_mod]
  have key : ∀ r < 8, (Td 13)^[r] 283 ≡ 13 [MOD 5] ∨ (Td 13)^[r] 283 ≡ 2 * 13 [MOD 5] := by
    decide
  exact key (i % 8) (Nat.mod_lt _ (by norm_num))

/-- And it is never home. -/
theorem never_home (i : ℕ) : (Td 13)^[i] 283 ≠ 13 := by
  rw [walk_of_283_mod]
  have key : ∀ r < 8, (Td 13)^[r] 283 ≠ 13 := by decide
  exact key (i % 8) (Nat.mod_lt _ (by norm_num))

/-- The exception at five is real. There is a world, and a positive walker in it, who
looks like home modulo 5 forever and never comes home. -/
theorem five_is_a_real_exception :
    ∃ d n, d % 2 = 1 ∧ Nat.Coprime 5 d ∧ 1 ≤ n ∧ LooksHome d 5 n ∧ ∀ i, (Td d)^[i] n ≠ d :=
  ⟨13, 283, by norm_num, by norm_num, by norm_num, looks_home_at_five, never_home⟩

/-- And five is the only one. In that same world, every other modulus from 4 up that is
prime to 13 tells the walk of 283 from home. -/
theorem and_only_five (M : ℕ) (hc : Nat.Coprime M 13) (hM : M = 4 ∨ 6 ≤ M) :
    ¬ LooksHome 13 M 283 := by
  intro h
  obtain ⟨i, hi⟩ := looks_home_is_home 13 M 283 (by norm_num) hc hM h
  exact never_home i hi

/-! ## The same walker, in our own world -/

/-- A walker in the world of `d` is the rational walker `n / d` in ours: one step there is
one step here, taken according to the parity of the numerator. -/
theorem same_walk (d n : ℕ) (hd : d % 2 = 1) :
    Fate.step (n % 2 == 1) ((n : ℚ) / d) = (Td d n : ℚ) / d := by
  obtain ⟨b, rfl⟩ : ∃ b, d = 2 * b + 1 := ⟨d / 2, by omega⟩
  have hb : (2 * (b : ℚ) + 1) ≠ 0 := by positivity
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · obtain ⟨a, rfl⟩ : ∃ a, n = 2 * a := ⟨n / 2, by omega⟩
    have hT : Td (2 * b + 1) (2 * a) = a := by
      unfold Td
      split_ifs
      omega
    rw [hT, show ((2 * a) % 2 == 1) = false by simp]
    simp only [Fate.step]
    push_cast
    field_simp
  · obtain ⟨a, rfl⟩ : ∃ a, n = 2 * a + 1 := ⟨n / 2, by omega⟩
    have hT : Td (2 * b + 1) (2 * a + 1) = 3 * a + b + 2 := by
      unfold Td
      split_ifs <;> omega
    have hpar : ((2 * a + 1) % 2 == 1) = true := by
      have : (2 * a + 1) % 2 = 1 := by omega
      simp [this]
    rw [hT, hpar]
    simp only [Fate.step]
    push_cast
    field_simp
    ring

/-- In our own world: the fate of the pattern fall, climb, fall, climb, fall, climb,
climb, climb is the positive number 986/13. It walks that pattern forever, never comes
home, and modulo 5 it looks like home at every step. -/
theorem the_one_who_looks_like_home :
    Fate.fate [false, true, false, true, false, true, true, true] = 986 / 13 := by
  norm_num [Fate.fate, Fate.cOf]

end Journey.Elsewhere

#print axioms Journey.Elsewhere.looks_home_is_home
#print axioms Journey.Elsewhere.five_is_a_real_exception
#print axioms Journey.Elsewhere.and_only_five
#print axioms Journey.Elsewhere.same_walk
#print axioms Journey.Elsewhere.the_one_who_looks_like_home
