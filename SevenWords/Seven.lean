import Mathlib
import SevenWords.Barrier

/-!
# Seven words

The last file asked a question about three steps at a time. This one asks it about words
of steps of any length, and answers it completely.

Call a word of climbs and falls *forced* if, in every 3n + d world, every walk that stays
above home takes that word somewhere. A forced word is one whose appearance can be proved
without knowing which world you are in.

**Exactly seven words are forced** (eight with the empty word):

    climb            fall
    climb climb      climb fall      fall climb
    climb climb fall                 fall climb climb

The first five say that a walk turns, and that it must sometimes climb twice running or
it would sink. The last two put those together. Every other word, of any length, is
avoided by one of two walks in the world of 5: the walk of 19, which goes climb, climb,
climb, fall, fall for ever, or the walk of 23, which goes climb, climb, fall, climb, fall
for ever. Those two walks share no stretch of four steps.

So nothing of four steps or more is forced. In remainders of the shortcut walk: no single
class modulo 16, or modulo any higher power of two, is met by every walk above home in
every world. Modulo 8 the forced classes are 3 and 6, and with the values 3n + 1 left in,
as Yolcu, Aaronson and Heule count them, 2, 3, 4 and 6: the four their program proved.
(Counted their way, two classes modulo 16 are still forced, 6 and 12, because they are
climb, climb, fall and fall, climb, climb seen one step late. That remark is by hand.)

The answer does not lean on the world of 5. The worlds of 13, 47 and 59 each force
exactly the same seven on their own, and 5, 13, 47 and 59 share no factor.

A correction. I first wrote that an unforced word cannot be settled by an argument that
works in every world, and took that as a measure of difficulty. It is not one. `Caution`
proves, by plain descent, a statement about 3n + 1 whose analogue fails in the world of 5.
Forced means provable without knowing the world. Unforced does not mean hard.

The cycles are classical. For 3n + 1 alone the seven are not new either. The classes
they name (0 and 1 modulo 2; 1, 2 and 3 modulo 4; 3 and 6 modulo 8) all stand in the
tables of Monks, Monks, Monks and Monks (2012), who call such sets strongly sufficient
or forward sufficient. What I found is that these seven hold in every world at once, and
that nothing else does, together with the four worlds. I cannot be sure nobody has done
this, and a search did not turn it up. Two 2026 preprints by H. Nashida settle, inside
3n + 1, which further classes a descent with 2-adic valuations can add and why the rest
resist it. I have read them. Their question is a different one, and a deeper one.
-/

namespace Journey.Seven

open Function Journey.Collatz Journey.Elsewhere Journey.Barrier

/-- The steps of a walk in the world of `d`: `true` where it climbs. -/
def pat (d n i : ℕ) : Bool := (Td d)^[i] n % 2 == 1

/-- The word `w` is taken starting at moment `i`. -/
def occAt (s : ℕ → Bool) : ℕ → List Bool → Prop
  | _, [] => True
  | i, b :: w => s i = b ∧ occAt s (i + 1) w

instance decOcc (s : ℕ → Bool) : (i : ℕ) → (w : List Bool) → Decidable (occAt s i w)
  | _, [] => instDecidableTrue
  | i, b :: w =>
    have : Decidable (occAt s (i + 1) w) := decOcc s (i + 1) w
    inferInstanceAs (Decidable (s i = b ∧ occAt s (i + 1) w))

/-- A word is forced if, in every world, every walk that stays above home takes it. -/
def Forced (w : List Bool) : Prop :=
  ∀ d n, d % 2 = 1 → (∀ i, d < (Td d)^[i] n) → ∃ i, occAt (pat d n) i w

/-- The seven words, and the empty one. -/
def forcedWords : List (List Bool) :=
  [[], [true], [false], [true, true], [true, false], [false, true],
    [true, true, false], [false, true, true]]

/-! ## Sequences that turn -/

/-- After a `true`, the first `false`. -/
theorem first_false (s : ℕ → Bool) (i j : ℕ) (hij : i < j) (hi : s i = true)
    (hj : s j = false) :
    ∃ m, i < m ∧ m ≤ j ∧ s m = false ∧ ∀ k, i ≤ k → k < m → s k = true := by
  have hex : ∃ m, i < m ∧ s m = false := ⟨j, hij, hj⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, Nat.find_min' hex ⟨hij, hj⟩,
    (Nat.find_spec hex).2, ?_⟩
  intro k hik hkm
  rcases Nat.eq_or_lt_of_le hik with rfl | hlt
  · exact hi
  · by_contra hne
    have hf : s k = false := by simpa using hne
    exact Nat.find_min hex hkm ⟨hlt, hf⟩

/-- Before a `true`, the last `false`. -/
theorem last_false (s : ℕ → Bool) (i j : ℕ) (hij : i < j) (hi : s i = false)
    (hj : s j = true) :
    ∃ m, i ≤ m ∧ m < j ∧ s m = false ∧ ∀ k, m < k → k ≤ j → s k = true := by
  induction j, hij using Nat.le_induction with
  | base =>
    refine ⟨i, le_rfl, Nat.lt_succ_self i, hi, fun k hk hk' => ?_⟩
    have e : k = i + 1 := by omega
    rw [e]
    exact hj
  | succ j hj' ih =>
    cases hsj : s j with
    | false =>
      refine ⟨j, by omega, Nat.lt_succ_self j, hsj, fun k hk hk' => ?_⟩
      have e : k = j + 1 := by omega
      rw [e]
      exact hj
    | true =>
      obtain ⟨m, hm1, hm2, hm3, hm4⟩ := ih hsj
      refine ⟨m, hm1, by omega, hm3, fun k hk hk' => ?_⟩
      rcases Nat.eq_or_lt_of_le hk' with rfl | hlt
      · exact hj
      · exact hm4 k hk (by omega)

/-- A sequence that turns: it climbs again and again, falls again and again, and again
and again climbs twice running. -/
structure Turns (s : ℕ → Bool) : Prop where
  climbs : ∀ N, ∃ i, N ≤ i ∧ s i = true
  falls : ∀ N, ∃ i, N ≤ i ∧ s i = false
  twice : ∀ N, ∃ i, N ≤ i ∧ s i = true ∧ s (i + 1) = true

/-- A sequence that turns takes each of the seven words. -/
theorem Turns.takes {s : ℕ → Bool} (h : Turns s) (w : List Bool) (hw : w ∈ forcedWords) :
    ∃ i, occAt s i w := by
  simp only [forcedWords, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, trivial⟩
  · obtain ⟨i, _, hi⟩ := h.climbs 0
    exact ⟨i, hi, trivial⟩
  · obtain ⟨i, _, hi⟩ := h.falls 0
    exact ⟨i, hi, trivial⟩
  · obtain ⟨i, _, h1, h2⟩ := h.twice 0
    exact ⟨i, h1, h2, trivial⟩
  · -- climb, fall: after a climb, the first fall
    obtain ⟨i, _, hi⟩ := h.climbs 0
    obtain ⟨j, hj, hj'⟩ := h.falls (i + 1)
    obtain ⟨m, hm1, hm2, hm3, hm4⟩ := first_false s i j (by omega) hi hj'
    obtain ⟨q, rfl⟩ : ∃ q, m = q + 1 := ⟨m - 1, by omega⟩
    exact ⟨q, hm4 q (by omega) (by omega), hm3, trivial⟩
  · -- fall, climb: before a climb, the last fall
    obtain ⟨i, _, hi⟩ := h.falls 0
    obtain ⟨j, hj, hj'⟩ := h.climbs (i + 1)
    obtain ⟨m, hm1, hm2, hm3, hm4⟩ := last_false s i j (by omega) hi hj'
    exact ⟨m, hm3, hm4 (m + 1) (by omega) (by omega), trivial⟩
  · -- climb, climb, fall: after two climbs, the first fall
    obtain ⟨i, _, h1, h2⟩ := h.twice 0
    obtain ⟨j, hj, hj'⟩ := h.falls (i + 2)
    obtain ⟨m, hm1, hm2, hm3, hm4⟩ := first_false s (i + 1) j (by omega) h2 hj'
    obtain ⟨q, rfl⟩ : ∃ q, m = q + 2 := ⟨m - 2, by omega⟩
    refine ⟨q, ?_, hm4 (q + 1) (by omega) (by omega), hm3, trivial⟩
    rcases Nat.eq_or_lt_of_le (show i ≤ q by omega) with rfl | hlt
    · exact h1
    · exact hm4 q (by omega) (by omega)
  · -- fall, climb, climb: before two climbs, the last fall
    obtain ⟨i, _, hi⟩ := h.falls 0
    obtain ⟨j, hj, h1, h2⟩ := h.twice (i + 1)
    obtain ⟨m, hm1, hm2, hm3, hm4⟩ := last_false s i j (by omega) hi h1
    refine ⟨m, hm3, hm4 (m + 1) (by omega) (by omega), ?_, trivial⟩
    rcases Nat.eq_or_lt_of_le (show m + 1 + 1 ≤ j + 1 by omega) with e | hlt
    · rw [e]
      exact h2
    · exact hm4 (m + 1 + 1) (by omega) (by omega)

/-! ## Every walk above home turns -/

/-- `k` falls in a row need `k` twos. -/
theorem falls_dvd (d : ℕ) : ∀ k v, (∀ j < k, (Td d)^[j] v % 2 = 0) → 2 ^ k ∣ v := by
  intro k
  induction k with
  | zero => intro v _; simp
  | succ k ih =>
    intro v h
    have h0 : v % 2 = 0 := h 0 (by omega)
    have hT : Td d v = v / 2 := by simp [Td, h0]
    obtain ⟨c, hc⟩ := ih (Td d v) (fun j hj => by
      have h1 := h (j + 1) (by omega)
      rwa [Function.iterate_succ_apply] at h1)
    rw [hT] at hc
    refine ⟨c, ?_⟩
    calc v = 2 * (v / 2) := by omega
      _ = 2 * (2 ^ k * c) := by rw [hc]
      _ = 2 ^ (k + 1) * c := by ring

/-- `k` climbs in a row need `k` twos in `v + d`. -/
theorem climbs_dvd (d : ℕ) (hd : d % 2 = 1) :
    ∀ k v, (∀ j < k, (Td d)^[j] v % 2 = 1) → 2 ^ k ∣ v + d := by
  intro k
  induction k with
  | zero => intro v _; simp
  | succ k ih =>
    intro v h
    have h0 : v % 2 = 1 := h 0 (by omega)
    have h2 : 2 * Td d v = 3 * v + d := by
      rcases two_Td d v hd with ⟨hp, _⟩ | ⟨_, e⟩
      · omega
      · exact e
    obtain ⟨c, hc⟩ := ih (Td d v) (fun j hj => by
      have h1 := h (j + 1) (by omega)
      rwa [Function.iterate_succ_apply] at h1)
    have h3 : 2 ^ (k + 1) ∣ 3 * (v + d) := ⟨c, by
      calc 3 * (v + d) = 2 * (Td d v + d) := by omega
        _ = 2 * (2 ^ k * c) := by rw [hc]
        _ = 2 ^ (k + 1) * c := by ring⟩
    have hcop : Nat.Coprime (2 ^ (k + 1)) 3 := Nat.Coprime.pow_left _ (by norm_num)
    exact hcop.dvd_of_dvd_mul_left h3

/-- In every world, a walk that stays above home turns. -/
theorem walk_turns (d n : ℕ) (hd : d % 2 = 1) (h : ∀ i, d < (Td d)^[i] n) :
    Turns (pat d n) := by
  have hadd : ∀ N j, (Td d)^[j] ((Td d)^[N] n) = (Td d)^[N + j] n := fun N j => by
    rw [add_comm, Function.iterate_add_apply]
  refine ⟨fun N => ?_, fun N => ?_, fun N => ?_⟩
  · -- it climbs at or after `N`, or else it falls for ever
    by_contra hno
    have hall : ∀ j, (Td d)^[N + j] n % 2 = 0 := by
      intro j
      by_contra hne
      have h1 : (Td d)^[N + j] n % 2 = 1 := by omega
      exact hno ⟨N + j, by omega, by simp [pat, h1]⟩
    have hdv := falls_dvd d ((Td d)^[N] n) ((Td d)^[N] n) (fun j _ => by
      rw [hadd]
      exact hall j)
    have hpos : 0 < (Td d)^[N] n := by
      have := h N
      omega
    have h1 := Nat.le_of_dvd hpos hdv
    have h2 : (Td d)^[N] n < 2 ^ (Td d)^[N] n := Nat.lt_two_pow_self
    omega
  · -- it falls at or after `N`, or else it climbs for ever
    by_contra hno
    have hall : ∀ j, (Td d)^[N + j] n % 2 = 1 := by
      intro j
      by_contra hne
      have h1 : (Td d)^[N + j] n % 2 = 0 := by omega
      exact hno ⟨N + j, by omega, by simp [pat, h1]⟩
    have hdv := climbs_dvd d hd ((Td d)^[N] n + d) ((Td d)^[N] n) (fun j _ => by
      rw [hadd]
      exact hall j)
    have hpos : 0 < (Td d)^[N] n + d := by omega
    have h1 := Nat.le_of_dvd hpos hdv
    have h2 : (Td d)^[N] n + d < 2 ^ ((Td d)^[N] n + d) := Nat.lt_two_pow_self
    omega
  · -- it climbs twice running at or after `N`, or else it sinks
    obtain ⟨i, h1, h2⟩ := above_home_climbs_twice d ((Td d)^[N] n) hd
      (by have := h N; omega) (fun i => by rw [hadd]; exact h (N + i))
    rw [hadd] at h1
    rw [hadd] at h2
    have h2' : (Td d)^[N + i + 1] n % 2 = 1 := h2
    refine ⟨N + i, by omega, by simp [pat, h1], ?_⟩
    unfold pat
    rw [h2']
    rfl

/-- So each of the seven words is forced. -/
theorem forced_of_mem (w : List Bool) (hw : w ∈ forcedWords) : Forced w :=
  fun d n hd h => (walk_turns d n hd h).takes w hw

/-! ## Everything else is avoided by some cycle -/

theorem pat_add (d n i k : ℕ) : pat d n (i + k) = pat d ((Td d)^[i] n) k := by
  unfold pat
  rw [add_comm i k, Function.iterate_add_apply]

theorem occAt_shift (d n i : ℕ) (w : List Bool) :
    ∀ j, occAt (pat d n) (i + j) w ↔ occAt (pat d ((Td d)^[i] n)) j w := by
  induction w with
  | nil => intro j; exact Iff.rfl
  | cons b w ih =>
    intro j
    change (pat d n (i + j) = b ∧ occAt (pat d n) (i + j + 1) w) ↔
      (pat d ((Td d)^[i] n) j = b ∧ occAt (pat d ((Td d)^[i] n)) (j + 1) w)
    rw [pat_add, show i + j + 1 = i + (j + 1) by ring, ih (j + 1)]

/-- A word that a cycle takes from none of its places is never taken by the walk. -/
theorem never_on_cycle (d p s : ℕ) (hp : 0 < p) (hc : (Td d)^[p] s = s) (w : List Bool)
    (hQ : ∀ r < p, ¬ occAt (pat d ((Td d)^[r] s)) 0 w) (i : ℕ) : ¬ occAt (pat d s) i w := by
  intro h
  have h' := (occAt_shift d s i w 0).mp h
  exact on_cycle d p s hp hc (fun v => ¬ occAt (pat d v) 0 w) hQ i h'

/-- A word is forced in the world of `d` if every walk there that stays above home takes
it. -/
def ForcedIn (d : ℕ) (w : List Bool) : Prop :=
  ∀ n, (∀ i, d < (Td d)^[i] n) → ∃ i, occAt (pat d n) i w

/-- A cycle, given by its length and a starting place, takes the word from none of its
places. -/
abbrev AvC (d : ℕ) (ps : ℕ × ℕ) (w : List Bool) : Prop :=
  ∀ r < ps.1, ¬ occAt (pat d ((Td d)^[r] ps.2)) 0 w

/-- Some cycle in the list avoids the word. -/
abbrev AvL (d : ℕ) (ws : List (ℕ × ℕ)) (w : List Bool) : Prop := ∃ ps ∈ ws, AvC d ps w

/-- Every entry of the list is a cycle lying wholly above home. -/
abbrev Valid (d : ℕ) (ws : List (ℕ × ℕ)) : Prop :=
  ∀ ps ∈ ws, 0 < ps.1 ∧ (Td d)^[ps.1] ps.2 = ps.2 ∧ ∀ r < ps.1, d < (Td d)^[r] ps.2

theorem avoided (d : ℕ) (ws : List (ℕ × ℕ)) (hv : Valid d ws)
    (k2 : ∀ a b : Bool, [a, b] ∈ forcedWords ∨ AvL d ws [a, b])
    (k3 : ∀ a b c : Bool, [a, b, c] ∈ forcedWords ∨ AvL d ws [a, b, c])
    (k4 : ∀ a b c e : Bool, AvL d ws [a, b, c, e]) :
    ∀ w : List Bool, w ∉ forcedWords → ∃ ps ∈ ws, ∀ i, ¬ occAt (pat d ps.2) i w
  | [], h => absurd (by decide) h
  | [a], h => absurd (by cases a <;> decide) h
  | [a, b], h => by
    rcases k2 a b with h1 | ⟨ps, hps, h1⟩
    · exact absurd h1 h
    · exact ⟨ps, hps, never_on_cycle d ps.1 ps.2 (hv ps hps).1 (hv ps hps).2.1 _ h1⟩
  | [a, b, c], h => by
    rcases k3 a b c with h1 | ⟨ps, hps, h1⟩
    · exact absurd h1 h
    · exact ⟨ps, hps, never_on_cycle d ps.1 ps.2 (hv ps hps).1 (hv ps hps).2.1 _ h1⟩
  | a :: b :: c :: e :: rest, _ => by
    have pre : ∀ (s : ℕ → Bool) (i : ℕ), occAt s i (a :: b :: c :: e :: rest) →
        occAt s i [a, b, c, e] := fun s i ⟨h1, h2, h3, h4, _⟩ => ⟨h1, h2, h3, h4, trivial⟩
    obtain ⟨ps, hps, h1⟩ := k4 a b c e
    exact ⟨ps, hps, fun i hi =>
      never_on_cycle d ps.1 ps.2 (hv ps hps).1 (hv ps hps).2.1 _ h1 i (pre _ i hi)⟩

/-- If a world has cycles above home that between them avoid every word of two, three and
four steps outside the list, then in that world alone exactly the seven are forced. -/
theorem classify (d : ℕ) (hd : d % 2 = 1) (ws : List (ℕ × ℕ)) (hv : Valid d ws)
    (k2 : ∀ a b : Bool, [a, b] ∈ forcedWords ∨ AvL d ws [a, b])
    (k3 : ∀ a b c : Bool, [a, b, c] ∈ forcedWords ∨ AvL d ws [a, b, c])
    (k4 : ∀ a b c e : Bool, AvL d ws [a, b, c, e]) (w : List Bool) :
    ForcedIn d w ↔ w ∈ forcedWords := by
  constructor
  · intro h
    by_contra hw
    obtain ⟨ps, hps, hav⟩ := avoided d ws hv k2 k3 k4 w hw
    obtain ⟨hp, hc, habove⟩ := hv ps hps
    obtain ⟨i, hi⟩ := h ps.2 (on_cycle d ps.1 ps.2 hp hc (fun v => d < v) habove)
    exact hav i hi
  · intro hw n hn
    exact forced_of_mem w hw d n hd hn

/-! ## Four worlds -/

/-- In the world of 5 alone, exactly the seven are forced. The witnesses are the walk of
19 (climb, climb, climb, fall, fall) and the walk of 23 (climb, climb, fall, climb, fall).
They share no stretch of four steps. -/
theorem in_the_world_of_5 (w : List Bool) : ForcedIn 5 w ↔ w ∈ forcedWords :=
  classify 5 (by norm_num) [(5, 19), (5, 23)] (by decide) (by decide) (by decide)
    (by decide) w

/-- In the world of 13 alone, exactly the seven are forced. Witnesses: the walks of 211
and 319, of eight steps each. -/
theorem in_the_world_of_13 (w : List Bool) : ForcedIn 13 w ↔ w ∈ forcedWords :=
  classify 13 (by norm_num) [(8, 211), (8, 319)] (by decide) (by decide) (by decide)
    (by decide) w

/-- In the world of 47 alone, exactly the seven are forced. Witnesses: the walks of 65
and 101, of seven steps each. -/
theorem in_the_world_of_47 (w : List Bool) : ForcedIn 47 w ↔ w ∈ forcedWords :=
  classify 47 (by norm_num) [(7, 65), (7, 101)] (by decide) (by decide) (by decide)
    (by decide) w

/-- In the world of 59 alone, exactly the seven are forced. Witnesses: the walks of 133,
217 and 221, of ten steps each. -/
theorem in_the_world_of_59 (w : List Bool) : ForcedIn 59 w ↔ w ∈ forcedWords :=
  classify 59 (by norm_num) [(10, 133), (10, 217), (10, 221)] (by decide) (by decide)
    (by decide) (by decide) w

/-! ## The classification -/

/-- Exactly seven words are forced. A word of climbs and falls is taken by every walk
above home in every world exactly when it is one of: climb; fall; climb, climb; climb,
fall; fall, climb; climb, climb, fall; fall, climb, climb (or it is empty). -/
theorem forced_iff (w : List Bool) : Forced w ↔ w ∈ forcedWords :=
  ⟨fun h => (in_the_world_of_5 w).mp (fun n hn => h 5 n (by norm_num) hn), forced_of_mem w⟩

/-- And the answer does not lean on any one world. The worlds of 5, 13, 47 and 59 share no
factor, and each of them alone forces exactly what all worlds together force. -/
theorem four_worlds (w : List Bool) :
    (ForcedIn 5 w ↔ Forced w) ∧ (ForcedIn 13 w ↔ Forced w) ∧
      (ForcedIn 47 w ↔ Forced w) ∧ (ForcedIn 59 w ↔ Forced w) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [in_the_world_of_5, forced_iff]
  · rw [in_the_world_of_13, forced_iff]
  · rw [in_the_world_of_47, forced_iff]
  · rw [in_the_world_of_59, forced_iff]

theorem forced_short : ∀ w ∈ forcedWords, w.length ≤ 3 := by decide

/-- Nothing of four steps or more is forced: no word of four or more steps is taken by
every walk above home in every world. -/
theorem nothing_longer_is_forced (w : List Bool) (h : 4 ≤ w.length) : ¬ Forced w := by
  rw [forced_iff]
  intro hw
  have := forced_short w hw
  omega

/-- In our own world, a forced word is taken by every walk that never comes home. -/
theorem in_our_world (w : List Bool) (hw : Forced w) (n : ℕ) (hn : 1 ≤ n)
    (hne : ∀ i, T^[i] n ≠ 1) : ∃ i, occAt (pat 1 n) i w := by
  apply hw 1 n (by norm_num)
  intro i
  rw [Td_one_eq]
  have h1 := iterate_pos i n hn
  have h2 := hne i
  omega

end Journey.Seven

#print axioms Journey.Seven.forced_iff
#print axioms Journey.Seven.four_worlds
#print axioms Journey.Seven.nothing_longer_is_forced
