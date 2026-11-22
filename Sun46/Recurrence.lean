import Sun46.Statement

/-!
# A recurrence for the strict partition function

Write `c n` for the coefficient of `x ^ n` in Euler's product `∏ (1 - x ^ i)`, which by the
pentagonal number theorem is `(-1) ^ k` if `n = k (3 k - 1) / 2` and `0` otherwise. From

  `∏ (1 + x ^ i) * ∏ (1 - x ^ i) = ∏ (1 - x ^ (2 i))`

we get, for every `n`,

  `∑_{a + b = n} q a * c b = c (n / 2)` if `n` is even, and `0` if `n` is odd.

Both infinite products are in Mathlib (`Nat.Partition.hasProd_powerSeriesMk_card_countRestricted`
and `PowerSeries.coeff_prod_one_sub_X_pow_eventually_eq`); here they are only combined.
-/

namespace Sun46

open Finset PowerSeries Filter
open scoped PowerSeries.WithPiTopology

/-- The coefficients of Euler's product `∏ (1 - x ^ i)`. -/
noncomputable def pc (n : ℕ) : ℤ := (PowerSeries.pentagonalSeries ℤ).coeff n

/-- Finite stages of `∏ (1 + x ^ i)` eventually have the right coefficients. -/
theorem eventually_coeff_distinct (d : ℕ) :
    ∀ᶠ s : Finset ℕ in atTop, (∏ i ∈ s, (1 + X ^ (i + 1) : ℤ⟦X⟧)).coeff d = (q d : ℤ) := by
  have h := Nat.Partition.hasProd_powerSeriesMk_card_countRestricted ℤ (m := 2) (by norm_num)
  rw [HasProd, PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto] at h
  have hd := h d
  rw [nhds_discrete, tendsto_pure] at hd
  filter_upwards [hd] with s hs
  have hf : ∀ i : ℕ, (∑ j ∈ range 2, (X : ℤ⟦X⟧) ^ ((i + 1) * j)) = 1 + X ^ (i + 1) := by
    intro i
    simp [Finset.sum_range_succ]
  simp only [hf] at hs
  rw [hs, PowerSeries.coeff_mk, Nat.Partition.countRestricted_two, q]

/-- Finite stages of `∏ (1 - x ^ i)` eventually have the right coefficients. -/
theorem eventually_coeff_euler (d : ℕ) :
    ∀ᶠ s : Finset ℕ in atTop, (∏ i ∈ s, (1 - X ^ (i + 1) : ℤ⟦X⟧)).coeff d = pc d :=
  PowerSeries.coeff_prod_one_sub_X_pow_eventually_eq ℤ d

/-- A finite product of polynomials `1 - x ^ e`, read as a power series. -/
theorem coe_prod_one_sub (s : Finset ℕ) (e : ℕ → ℕ) :
    ((∏ i ∈ s, (1 - Polynomial.X ^ e i : Polynomial ℤ) : Polynomial ℤ) : ℤ⟦X⟧) =
      ∏ i ∈ s, (1 - X ^ e i : ℤ⟦X⟧) := by
  rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_sub, map_one, map_pow, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]

/-- Substituting `x ^ 2` for `x` in a finite stage of Euler's product. -/
theorem coeff_prod_sq (s : Finset ℕ) (n : ℕ) :
    (∏ i ∈ s, (1 - X ^ (2 * (i + 1)) : ℤ⟦X⟧)).coeff n =
      if 2 ∣ n then (∏ i ∈ s, (1 - X ^ (i + 1) : ℤ⟦X⟧)).coeff (n / 2) else 0 := by
  have hexp : Polynomial.expand ℤ 2 (∏ i ∈ s, (1 - Polynomial.X ^ (i + 1) : Polynomial ℤ)) =
      ∏ i ∈ s, (1 - Polynomial.X ^ (2 * (i + 1)) : Polynomial ℤ) := by
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_sub, map_one, map_pow, Polynomial.expand_X, ← pow_mul]
  rw [← coe_prod_one_sub s fun i => 2 * (i + 1), ← coe_prod_one_sub s fun i => i + 1,
    Polynomial.coeff_coe, Polynomial.coeff_coe, ← hexp, Polynomial.coeff_expand (by norm_num)]

/-- The recurrence. -/
theorem conv (n : ℕ) :
    ∑ p ∈ antidiagonal n, (q p.1 : ℤ) * pc p.2 = if 2 ∣ n then pc (n / 2) else 0 := by
  have hA : ∀ᶠ s : Finset ℕ in atTop, ∀ d ∈ range (n + 1),
      (∏ i ∈ s, (1 + X ^ (i + 1) : ℤ⟦X⟧)).coeff d = (q d : ℤ) :=
    (Filter.eventually_all_finset _).mpr fun d _ => eventually_coeff_distinct d
  have hB : ∀ᶠ s : Finset ℕ in atTop, ∀ d ∈ range (n + 1),
      (∏ i ∈ s, (1 - X ^ (i + 1) : ℤ⟦X⟧)).coeff d = pc d :=
    (Filter.eventually_all_finset _).mpr fun d _ => eventually_coeff_euler d
  obtain ⟨s, hsA, hsB⟩ := (hA.and hB).exists
  have hprod : (∏ i ∈ s, (1 + X ^ (i + 1) : ℤ⟦X⟧)) * (∏ i ∈ s, (1 - X ^ (i + 1) : ℤ⟦X⟧)) =
      ∏ i ∈ s, (1 - X ^ (2 * (i + 1)) : ℤ⟦X⟧) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    ring
  have hc := congrArg (PowerSeries.coeff n) hprod
  rw [PowerSeries.coeff_mul, coeff_prod_sq] at hc
  have hlhs : ∑ p ∈ antidiagonal n, (q p.1 : ℤ) * pc p.2 =
      ∑ p ∈ antidiagonal n, (∏ i ∈ s, (1 + X ^ (i + 1) : ℤ⟦X⟧)).coeff p.1 *
        (∏ i ∈ s, (1 - X ^ (i + 1) : ℤ⟦X⟧)).coeff p.2 := by
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    rw [hsA p.1 (Finset.mem_range.mpr (by omega)), hsB p.2 (Finset.mem_range.mpr (by omega))]
  rw [hlhs, hc]
  split_ifs with h2
  · exact hsB (n / 2) (Finset.mem_range.mpr (by omega))
  · rfl

end Sun46
