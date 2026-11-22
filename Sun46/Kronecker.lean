import Sun46.Recurrence

/-!
# The recurrence, evaluated at a large power of two

Let `B` be a power of two and `β` its image in `ZMod (B ^ (N + 1))`. Evaluating the recurrence of
`Sun46/Recurrence.lean` at `x = β` gives one identity between three numbers:

  `(∑_{a ≤ N} q a * β ^ a) * Φ(β) = Φ(β ^ 2)`,

where `Φ(γ) = ∑_j (-1) ^ j * (γ ^ gNeg j - γ ^ gPos j)` is the pentagonal series, a sum of a few
hundred powers of `γ`. Since `Φ(β)` is invertible, the identity determines the first factor,
whose base `B` digits are the numbers `q a`.
-/

namespace Sun46

open Finset PowerSeries Filter
open scoped PowerSeries.WithPiTopology

/-- The pentagonal number `k (3 k - 1) / 2` at `k = -j`. -/
def gNeg (j : ℕ) : ℕ := j * (3 * j + 1) / 2

/-- The pentagonal number `k (3 k - 1) / 2` at `k = j + 1`. -/
def gPos (j : ℕ) : ℕ := (j + 1) * (3 * j + 2) / 2

theorem pentagonal_neg_nat (j : ℕ) : pentagonal (-(j : ℤ)) = gNeg j := by
  have h := two_mul_natCast_pentagonal_neg (j : ℤ)
  have h' : 2 * pentagonal (-(j : ℤ)) = j * (3 * j + 1) := by exact_mod_cast h
  unfold gNeg
  generalize j * (3 * j + 1) = t at h' ⊢
  omega

theorem pentagonal_succ_nat (j : ℕ) : pentagonal ((j : ℤ) + 1) = gPos j := by
  have h := two_mul_natCast_pentagonal ((j : ℤ) + 1)
  have h' : 2 * pentagonal ((j : ℤ) + 1) = (j + 1) * (3 * j + 2) := by
    have e : ((j : ℤ) + 1) * (3 * ((j : ℤ) + 1) - 1) = (((j + 1) * (3 * j + 2) : ℕ) : ℤ) := by
      push_cast; ring
    rw [e] at h
    exact_mod_cast h
  unfold gPos
  generalize (j + 1) * (3 * j + 2) = t at h' ⊢
  omega

theorem gNeg_mono {i j : ℕ} (h : i ≤ j) : gNeg i ≤ gNeg j :=
  Nat.div_le_div_right (Nat.mul_le_mul h (by omega))

theorem gNeg_le_gPos (j : ℕ) : gNeg j ≤ gPos j :=
  Nat.div_le_div_right (Nat.mul_le_mul (by omega) (by omega))

/-- The first `J` pairs of terms of the pentagonal series, as a polynomial. -/
noncomputable def pentPoly (J : ℕ) : Polynomial ℤ :=
  ∑ j ∈ range J, (-1) ^ j * (Polynomial.X ^ gNeg j - Polynomial.X ^ gPos j)

theorem coe_pentPoly (J : ℕ) : ((pentPoly J : Polynomial ℤ) : ℤ⟦X⟧) =
    ∑ j ∈ range J, (-1) ^ j * (X ^ gNeg j - X ^ gPos j) := by
  rw [pentPoly, ← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_pow, map_neg, map_one, map_sub, map_pow, map_pow,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]

/-- Below `gNeg J` the pentagonal series agrees with its first `J` pairs of terms. -/
theorem pc_eq_coeff_pentPoly {L J d : ℕ} (hJ : L < gNeg J) (hd : d ≤ L) :
    pc d = (pentPoly J).coeff d := by
  have h := PowerSeries.WithPiTopology.hasSum_pow_pentagonal_sub_pentagonalSeries ℤ
  simp only [pentagonal_neg_nat, pentagonal_succ_nat] at h
  rw [HasSum, PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto] at h
  have hd' := h d
  rw [nhds_discrete, tendsto_pure] at hd'
  obtain ⟨s0, hs0⟩ := Filter.eventually_atTop.mp hd'
  have hs := hs0 (s0 ∪ range J) Finset.subset_union_left
  rw [← Polynomial.coeff_coe, coe_pentPoly, pc, ← hs, map_sum, map_sum]
  refine (Finset.sum_subset Finset.subset_union_right fun j _ hj => ?_).symm
  have hjJ : J ≤ j := by simpa using hj
  have h1 : d ≠ gNeg j := by have := gNeg_mono hjJ; omega
  have h2 : d ≠ gPos j := by have := gNeg_mono hjJ; have := gNeg_le_gPos j; omega
  rcases neg_one_pow_eq_or ℤ⟦X⟧ j with hsgn | hsgn <;>
    simp [hsgn, PowerSeries.coeff_X_pow, h1, h2]

section Eval

variable {R : Type*} [CommRing R]

/-- The pentagonal series evaluated at `γ`, when the powers of `γ` above `L` vanish. -/
theorem sum_pc_eq {L J : ℕ} (hJ : L < gNeg J) (γ : R) (hγ : ∀ g, L < g → γ ^ g = 0) :
    ∑ d ∈ range (L + 1), ((pc d : ℤ) : R) * γ ^ d =
      ∑ j ∈ range J, (-1) ^ j * (γ ^ gNeg j - γ ^ gPos j) := by
  have hev : (pentPoly J).eval₂ (Int.castRingHom R) γ =
      ∑ j ∈ range J, (-1) ^ j * (γ ^ gNeg j - γ ^ gPos j) := by
    rw [pentPoly, ← Polynomial.coe_eval₂RingHom, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_pow, map_neg, map_one, map_sub, map_pow, map_pow,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  have hsub : range (L + 1) ⊆ range (max (L + 1) ((pentPoly J).natDegree + 1)) := by
    intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  rw [← hev, Polynomial.eval₂_eq_sum_range' (Int.castRingHom R)
    (n := max (L + 1) ((pentPoly J).natDegree + 1)) (by omega) γ,
    ← Finset.sum_subset hsub
      (f := fun i => (Int.castRingHom R) ((pentPoly J).coeff i) * γ ^ i) (fun i _ hi' => by
        have hLi : L < i := by simpa using hi'
        rw [hγ i hLi, mul_zero])]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdL : d ≤ L := by simpa [Nat.lt_succ_iff] using hd
  rw [pc_eq_coeff_pentPoly hJ hdL]
  simp

/-- Only even exponents: substitute `β ^ 2`. -/
theorem sum_even_reindex (N : ℕ) (f : ℕ → R) (β : R) :
    ∑ n ∈ range (N + 1), (if 2 ∣ n then f (n / 2) else 0) * β ^ n =
      ∑ b ∈ range (N / 2 + 1), f b * (β ^ 2) ^ b := by
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun n => n / 2) (fun b => 2 * b) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
    omega
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_range] at hb ⊢
    exact ⟨by omega, Dvd.intro _ rfl⟩
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    exact Nat.mul_div_cancel' hn.2
  · intro b _
    simp
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    rw [← pow_mul, Nat.mul_div_cancel' hn.2]

end Eval

/-- The recurrence at `x = B` in `ZMod (B ^ (N + 1))`. -/
theorem star (B N M : ℕ) (hM : M = B ^ (N + 1)) :
    (∑ a ∈ range (N + 1), ((q a : ℤ) : ZMod M) * (B : ZMod M) ^ a) *
      (∑ b ∈ range (N + 1), ((pc b : ℤ) : ZMod M) * (B : ZMod M) ^ b) =
    ∑ n ∈ range (N + 1),
      (((if 2 ∣ n then pc (n / 2) else 0 : ℤ) : ℤ) : ZMod M) * (B : ZMod M) ^ n := by
  have hdvd : (Polynomial.X : Polynomial ℤ) ^ (N + 1) ∣
      PowerSeries.trunc (N + 1) (PowerSeries.mk fun n => (q n : ℤ)) *
        PowerSeries.trunc (N + 1) (PowerSeries.pentagonalSeries ℤ) -
      PowerSeries.trunc (N + 1)
        (PowerSeries.mk fun n => if 2 ∣ n then pc (n / 2) else 0) := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    rw [Polynomial.coeff_sub, Polynomial.coeff_mul, sub_eq_zero, PowerSeries.coeff_trunc,
      ite_eq_left hd, PowerSeries.coeff_mk, ← conv d]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc, ite_eq_left (by omega),
      ite_eq_left (by omega), PowerSeries.coeff_mk]
    rfl
  obtain ⟨R', hR⟩ := hdvd
  have hev := congrArg (Polynomial.eval₂ (Int.castRingHom (ZMod M)) (B : ZMod M)) hR
  have hB : (B : ZMod M) ^ (N + 1) = 0 := by
    rw [← Nat.cast_pow, ← hM]
    exact ZMod.natCast_self M
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, hB, zero_mul, sub_eq_zero, PowerSeries.eval₂_trunc_eq_sum_range,
    PowerSeries.eval₂_trunc_eq_sum_range, PowerSeries.eval₂_trunc_eq_sum_range] at hev
  simpa [pc] using hev

/-- The identity between three numbers described at the top of this file. -/
theorem kron_identity (B N M J J2 : ℕ) (hM : M = B ^ (N + 1)) (hJ : N < gNeg J)
    (hJ2 : N / 2 < gNeg J2) :
    (∑ a ∈ range (N + 1), ((q a : ℕ) : ZMod M) * (B : ZMod M) ^ a) *
      (∑ j ∈ range J, (-1) ^ j * ((B : ZMod M) ^ gNeg j - (B : ZMod M) ^ gPos j)) =
    ∑ j ∈ range J2, (-1) ^ j *
      (((B : ZMod M) ^ 2) ^ gNeg j - ((B : ZMod M) ^ 2) ^ gPos j) := by
  have hB : (B : ZMod M) ^ (N + 1) = 0 := by
    rw [← Nat.cast_pow, ← hM]
    exact ZMod.natCast_self M
  have h1 : ∀ g, N < g → (B : ZMod M) ^ g = 0 := fun g hg => by
    have : g = (N + 1) + (g - (N + 1)) := by omega
    rw [this, pow_add, hB, zero_mul]
  have h2 : ∀ g, N / 2 < g → ((B : ZMod M) ^ 2) ^ g = 0 := fun g hg => by
    rw [← pow_mul]
    exact h1 _ (by omega)
  have hs := star B N M hM
  rw [sum_pc_eq hJ _ h1] at hs
  have he : ∑ n ∈ range (N + 1),
      (((if 2 ∣ n then pc (n / 2) else 0 : ℤ) : ℤ) : ZMod M) * (B : ZMod M) ^ n =
      ∑ n ∈ range (N + 1),
        (if 2 ∣ n then ((pc (n / 2) : ℤ) : ZMod M) else 0) * (B : ZMod M) ^ n := by
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs <;> simp
  rw [he, sum_even_reindex N (fun b => ((pc b : ℤ) : ZMod M)), sum_pc_eq hJ2 _ h2] at hs
  simpa using hs

end Sun46
