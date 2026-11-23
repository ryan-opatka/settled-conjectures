import Mathlib
import SevenWords.Seven

/-!
# Every pattern is walked somewhere

Take any pattern of climbs and falls that contracts: more twos taken out than threes put
in, so that `3 ^ o < 2 ^ k` for `k` steps of which `o` are climbs. Then there is a world,
the world of `d = 2 ^ k - 3 ^ o`, and a whole number in it, that walks exactly this
pattern round and round for ever.

The number is the numerator that `Fate` already computed: the fate of a pattern is the
fraction `c / (2 ^ k - 3 ^ o)`, and a walker `c` in the world of `d` is the fraction
`c / d` in ours. This file makes that exact, for every pattern at once, and adds a test
for when the whole cycle lies above home: send a shadow walker from 1 along the pattern,
by the prescribed steps. If the shadow never drops below 1 and ends above 1, the real
cycle lies above home throughout.

The correspondence between patterns and cycles of the 3n + d worlds is classical (Böhm
and Sontacchi 1978, Lagarias 1990). The shadow test is a convenience of mine.
-/

namespace Journey.Realize

open Function Journey.Elsewhere Journey.Seven
open Journey.Fate (step run cOf fate)

/-- A pattern contracts: more twos than threes. -/
def Contracts (p : List Bool) : Prop := 3 ^ p.count true < 2 ^ p.length

/-- The world of a pattern. -/
def world (p : List Bool) : ℕ := 2 ^ p.length - 3 ^ p.count true

theorem world_pos (p : List Bool) (hc : Contracts p) : 0 < world p := Nat.sub_pos_of_lt hc

theorem world_odd (p : List Bool) (hp : p ≠ []) (hc : Contracts p) : world p % 2 = 1 := by
  unfold world
  obtain ⟨k, hk⟩ : ∃ k, p.length = k + 1 :=
    ⟨p.length - 1, by have := List.length_pos_iff.mpr hp; omega⟩
  have h3 : 3 ^ p.count true % 2 = 1 := by
    rw [Nat.pow_mod]
    simp
  have hc' : 3 ^ p.count true < 2 ^ p.length := hc
  rw [hk, pow_succ] at hc' ⊢
  omega

theorem world_cast (p : List Bool) (hc : Contracts p) :
    ((world p : ℕ) : ℚ) = 2 ^ p.length - 3 ^ p.count true := by
  unfold world
  rw [Nat.cast_sub (le_of_lt hc), Nat.cast_pow, Nat.cast_pow]
  norm_num

theorem fate_eq (p : List Bool) (hc : Contracts p) :
    fate p = (cOf p : ℚ) / (world p : ℚ) := by
  rw [world_cast p hc]
  rfl

theorem perm_world {p q : List Bool} (h : p.Perm q) : world p = world q := by
  unfold world
  rw [h.length_eq, h.count_eq true]

theorem perm_contracts {p q : List Bool} (h : p.Perm q) (hc : Contracts p) : Contracts q := by
  unfold Contracts at *
  rwa [← h.length_eq, ← h.count_eq true]

/-- The numerator is odd exactly when the pattern begins with a climb. -/
theorem cOf_parity (b : Bool) (v : List Bool) : (cOf (b :: v) % 2 == 1) = b := by
  have h := Fate.fate_first_step b v
  cases b with
  | false =>
    have h0 : cOf (false :: v) % 2 = 0 := h
    rw [h0]
    rfl
  | true =>
    have h1 : cOf (true :: v) % 2 = 1 := h
    rw [h1]
    rfl

theorem cOf_head (q : List Bool) (h : 0 < q.length) : (cOf q % 2 == 1) = q[0] := by
  match q, h with
  | b :: v, _ => exact cOf_parity b v

/-- One step in the world of the pattern: the numerator of a pattern steps to the
numerator of the pattern turned by one place. -/
theorem step_cOf (b : Bool) (v : List Bool) (hc : Contracts (b :: v)) :
    Td (world (b :: v)) (cOf (b :: v)) = cOf (v ++ [b]) := by
  have hperm : (v ++ [b]).Perm (b :: v) := List.perm_append_singleton b v
  have hd := world_odd (b :: v) (by simp) hc
  have hpos := world_pos (b :: v) hc
  have h1 := same_walk (world (b :: v)) (cOf (b :: v)) hd
  rw [cOf_parity] at h1
  have h2 := Fate.fate_rotates b v
  rw [fate_eq (b :: v) hc, fate_eq (v ++ [b]) (perm_contracts hperm.symm hc),
    perm_world hperm] at h2
  rw [h2] at h1
  have hne : ((world (b :: v) : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
  have h3 := (div_left_inj' hne).mp h1
  exact_mod_cast h3.symm

/-- So after `i` steps the walker stands on the numerator of the pattern turned by `i`
places. -/
theorem iterate_cOf : ∀ (i : ℕ) (p : List Bool), p ≠ [] → Contracts p →
    (Td (world p))^[i] (cOf p) = cOf (p.rotate i) := by
  intro i
  induction i with
  | zero =>
    intro p _ _
    simp
  | succ i ih =>
    intro p hp hc
    match p, hp, hc with
    | b :: v, _, hc =>
      have hperm : (v ++ [b]).Perm (b :: v) := List.perm_append_singleton b v
      rw [Function.iterate_succ_apply, step_cOf b v hc, List.rotate_cons_succ,
        ← perm_world hperm]
      exact ih (v ++ [b]) (by simp) (perm_contracts hperm.symm hc)

/-- The walker takes exactly the steps of its pattern, round and round. -/
theorem pat_cOf (p : List Bool) (hp : p ≠ []) (hc : Contracts p) (i : ℕ) :
    pat (world p) (cOf p) i =
      p[i % p.length]'(Nat.mod_lt _ (List.length_pos_iff.mpr hp)) := by
  have hlen : 0 < (p.rotate i).length := by
    rw [List.length_rotate]
    exact List.length_pos_iff.mpr hp
  unfold pat
  rw [iterate_cOf i p hp hc, cOf_head _ hlen, List.getElem_rotate]
  simp

/-! ## When the cycle lies above home -/

theorem step_lt (b : Bool) {x y : ℚ} (h : x < y) : step b x < step b y := by
  cases b <;> simp only [step] <;> linarith

theorem run_lt (q : List Bool) : ∀ {x y : ℚ}, x < y → run q x < run q y := by
  induction q with
  | nil =>
    intro x y h
    exact h
  | cons b v ih =>
    intro x y h
    exact ih (step_lt b h)

/-- Walk part of the way round a cycle and you stand on the fate of the pattern turned
that far. -/
theorem fate_split (u v : List Bool) (h : v ++ u ≠ []) :
    run u (fate (u ++ v)) = fate (v ++ u) := by
  have huv : u ++ v ≠ [] := by
    intro e
    apply h
    rw [List.append_eq_nil_iff] at e ⊢
    exact ⟨e.2, e.1⟩
  have hfix : run (u ++ v) (fate (u ++ v)) = fate (u ++ v) :=
    (Fate.fate_unique (u ++ v) huv _).mpr rfl
  apply (Fate.fate_unique (v ++ u) h _).mp
  rw [Fate.run_append, ← Fate.run_append u v, hfix]

/-- The shadow test. Send a walker from 1 along the pattern by the prescribed steps. If it
never drops below 1 and ends above 1, then the true cycle of the pattern lies above home
at every place. -/
theorem above_home (p : List Bool) (hp : p ≠ []) (hc : Contracts p)
    (hs : ∀ j, j ≤ p.length → 1 ≤ run (p.take j) 1) (h1 : 1 < run p 1) :
    ∀ i, world p < (Td (world p))^[i] (cOf p) := by
  intro i
  have hk : 0 < p.length := List.length_pos_iff.mpr hp
  rw [iterate_cOf i p hp hc, ← List.rotate_mod]
  have hjk : i % p.length ≤ p.length := (Nat.mod_lt i hk).le
  have hrot : p.rotate (i % p.length) = p.drop (i % p.length) ++ p.take (i % p.length) :=
    List.rotate_eq_drop_append_take hjk
  have hperm : (p.rotate (i % p.length)).Perm p := List.rotate_perm p _
  have hcr : Contracts (p.rotate (i % p.length)) := perm_contracts hperm.symm hc
  have hne : p.rotate (i % p.length) ≠ [] := by
    intro e
    have h := List.length_rotate p (i % p.length)
    rw [e] at h
    simp at h
    omega
  have hpos : (0 : ℚ) < (world p : ℚ) := by exact_mod_cast world_pos p hc
  -- the fate of the pattern is above 1
  have hfate : 1 < fate p := by
    have haff := Fate.run_affine p 1
    have h2 : (0 : ℚ) < 2 ^ p.length := by positivity
    rw [fate_eq p hc, lt_div_iff₀ hpos, one_mul, world_cast p hc]
    nlinarith [mul_pos (sub_pos.mpr h1) h2, haff]
  -- and so is the place reached part of the way round
  have hel : fate (p.rotate (i % p.length)) = run (p.take (i % p.length)) (fate p) := by
    have h := fate_split (p.take (i % p.length)) (p.drop (i % p.length))
      (by rw [← hrot]; exact hne)
    rw [List.take_append_drop] at h
    rw [hrot]
    exact h.symm
  have hgt : 1 < fate (p.rotate (i % p.length)) := by
    rw [hel]
    exact lt_of_le_of_lt (hs _ hjk) (run_lt _ hfate)
  rw [fate_eq _ hcr, perm_world hperm, lt_div_iff₀ hpos, one_mul] at hgt
  exact_mod_cast hgt

/-! ## Patterns given by a rule -/

/-- The first `k` steps of a rule. -/
def word (f : ℕ → Bool) (k : ℕ) : List Bool := (List.range k).map f

@[simp] theorem word_length (f : ℕ → Bool) (k : ℕ) : (word f k).length = k := by
  simp [word]

theorem word_succ (f : ℕ → Bool) (k : ℕ) : word f (k + 1) = word f k ++ [f k] := by
  simp [word, List.range_succ]

theorem take_word (f : ℕ → Bool) (k j : ℕ) (h : j ≤ k) : (word f k).take j = word f j := by
  unfold word
  rw [← List.map_take, List.take_range, Nat.min_eq_left h]

/-- How many of the first `k` steps are climbs. -/
def climbs (f : ℕ → Bool) (k : ℕ) : ℕ := (word f k).count true

theorem climbs_zero (f : ℕ → Bool) : climbs f 0 = 0 := by simp [climbs, word]

theorem climbs_succ (f : ℕ → Bool) (k : ℕ) :
    climbs f (k + 1) = climbs f k + if f k then 1 else 0 := by
  unfold climbs
  rw [word_succ, List.count_append]
  cases f k <;> simp

/-- The shadow: a walker sent from 1 along the rule, by the prescribed steps. -/
def shadow (f : ℕ → Bool) (i : ℕ) : ℚ := run (word f i) 1

theorem shadow_zero (f : ℕ → Bool) : shadow f 0 = 1 := by simp [shadow, word, run]

theorem shadow_succ (f : ℕ → Bool) (i : ℕ) :
    shadow f (i + 1) = step (f i) (shadow f i) := by
  unfold shadow
  rw [word_succ, Fate.run_append]
  rfl

/-- The world of the first `k` steps of a rule, and the walker in it. -/
def worldOf (f : ℕ → Bool) (k : ℕ) : ℕ := world (word f k)

/-- The walker. -/
def walker (f : ℕ → Bool) (k : ℕ) : ℕ := cOf (word f k)

theorem worldOf_eq (f : ℕ → Bool) (k : ℕ) : worldOf f k = 2 ^ k - 3 ^ climbs f k := by
  simp [worldOf, world, climbs]

/-- Every pattern is walked somewhere. If the first `k` steps of a rule contract, and the
shadow from 1 stays at or above 1 and ends above 1, then in the world of
`2 ^ k - 3 ^ o` there is a walker who stays above home for ever and whose steps are the
rule repeated with period `k`. -/
theorem realize (f : ℕ → Bool) (k : ℕ) (hk : 0 < k) (hc : 3 ^ climbs f k < 2 ^ k)
    (hs : ∀ j, j ≤ k → 1 ≤ shadow f j) (h1 : 1 < shadow f k) :
    worldOf f k % 2 = 1 ∧ (∀ i, worldOf f k < (Td (worldOf f k))^[i] (walker f k)) ∧
      (∀ i, pat (worldOf f k) (walker f k) i = f (i % k)) := by
  have hp : word f k ≠ [] := by
    intro e
    have h := congrArg List.length e
    simp at h
    omega
  have hcon : Contracts (word f k) := by
    unfold Contracts
    rw [word_length]
    exact hc
  refine ⟨world_odd _ hp hcon, above_home _ hp hcon ?_ h1, fun i => ?_⟩
  · intro j hj
    rw [word_length] at hj
    rw [take_word f k j hj]
    exact hs j hj
  · change pat (world (word f k)) (cOf (word f k)) i = f (i % k)
    rw [pat_cOf _ hp hcon]
    simp [word]

end Journey.Realize

#print axioms Journey.Realize.realize
#print axioms Journey.Realize.iterate_cOf
