import Sun46.Recurrence

/-!
# A size bound for the strict partition function

For `0 ≤ x`, `q n * x ^ n ≤ ∏ (1 + x ^ i) ≤ exp (∑ x ^ i)`. With `x = 516 / 517` the sum is at
most `516`, which gives `q n ≤ exp 516 * (517 / 516) ^ n`, and so `q n < 2 ^ 1504` for
`n ≤ 267228`. (The truth is about `2 ^ 1338` at the top of that range.)
-/

namespace Sun46

open Finset PowerSeries Filter

/-- Some finite stage of `∏ (1 + x ^ i)`, as a polynomial with natural coefficients, has
`q d` as its coefficient of `x ^ d`. -/
theorem exists_stage (d : ℕ) : ∃ s : Finset ℕ,
    (∏ i ∈ s, (1 + Polynomial.X ^ (i + 1) : Polynomial ℕ)).coeff d = q d := by
  obtain ⟨s, hs⟩ := (eventually_coeff_distinct d).exists
  refine ⟨s, ?_⟩
  have hmap : ((∏ i ∈ s, (1 + Polynomial.X ^ (i + 1) : Polynomial ℕ)).map (Nat.castRingHom ℤ) :
      Polynomial ℤ) = ∏ i ∈ s, (1 + Polynomial.X ^ (i + 1) : Polynomial ℤ) := by
    rw [Polynomial.map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp
  have hcoe : ((∏ i ∈ s, (1 + Polynomial.X ^ (i + 1) : Polynomial ℤ) : Polynomial ℤ) : ℤ⟦X⟧) =
      ∏ i ∈ s, (1 + X ^ (i + 1) : ℤ⟦X⟧) := by
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_add, map_one, map_pow, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]
  rw [← hcoe, Polynomial.coeff_coe, ← hmap, Polynomial.coeff_map] at hs
  have hs' : (((∏ i ∈ s, (1 + Polynomial.X ^ (i + 1) : Polynomial ℕ)).coeff d : ℕ) : ℤ) =
      (q d : ℤ) := by simpa using hs
  exact_mod_cast hs'

/-- `q n * x ^ n ≤ exp (∑ x ^ i)` over some finite set of exponents. -/
theorem q_mul_pow_le (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    ∃ s : Finset ℕ, (q n : ℝ) * x ^ n ≤ Real.exp (∑ i ∈ s, x ^ (i + 1)) := by
  obtain ⟨s, hs⟩ := exists_stage n
  refine ⟨s, ?_⟩
  set p : Polynomial ℕ := ∏ i ∈ s, (1 + Polynomial.X ^ (i + 1) : Polynomial ℕ) with hp
  have heval : p.eval₂ (Nat.castRingHom ℝ) x = ∏ i ∈ s, (1 + x ^ (i + 1)) := by
    rw [hp, ← Polynomial.coe_eval₂RingHom, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_add, map_one, map_pow, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  have hterm : ∀ i, 0 ≤ (Nat.castRingHom ℝ) (p.coeff i) * x ^ i := fun i =>
    mul_nonneg (by simp) (pow_nonneg hx i)
  have h1 : (q n : ℝ) * x ^ n ≤ p.eval₂ (Nat.castRingHom ℝ) x := by
    rw [Polynomial.eval₂_eq_sum_range]
    by_cases hn : n ≤ p.natDegree
    · have := Finset.single_le_sum (f := fun i => (Nat.castRingHom ℝ) (p.coeff i) * x ^ i)
        (fun i _ => hterm i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
      simpa [hs] using this
    · have h0 : p.coeff n = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      have hq : q n = 0 := by rw [← hs, h0]
      rw [hq]
      simpa using Finset.sum_nonneg fun i _ => hterm i
  have h2 : ∏ i ∈ s, (1 + x ^ (i + 1)) ≤ Real.exp (∑ i ∈ s, x ^ (i + 1)) := by
    rw [Real.exp_sum]
    refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => ?_
    have := Real.add_one_le_exp (x ^ (i + 1))
    linarith
  exact h1.trans (heval ▸ h2)

theorem geom_bound (M : ℕ) : ∑ i ∈ range M, ((516 : ℝ) / 517) ^ (i + 1) ≤ 516 := by
  have key : ∀ M : ℕ, ∑ i ∈ range M, ((516 : ℝ) / 517) ^ (i + 1) =
      516 * (1 - ((516 : ℝ) / 517) ^ M) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih => rw [Finset.sum_range_succ, ih]; ring
  rw [key]
  have : (0 : ℝ) ≤ ((516 : ℝ) / 517) ^ M := by positivity
  linarith

theorem pow_bound : (517 : ℕ) ^ 267228 ≤ 2 ^ 747 * 516 ^ 267228 := by decide +kernel

/-- Every `q n` with `n ≤ 267228` fits in `1504` bits. -/
theorem q_lt (n : ℕ) (hn : n ≤ 267228) : q n < 2 ^ 1504 := by
  obtain ⟨s, hs⟩ := q_mul_pow_le n ((516 : ℝ) / 517) (by norm_num)
  have hsum : ∑ i ∈ s, ((516 : ℝ) / 517) ^ (i + 1) ≤ 516 := by
    refine le_trans ?_ (geom_bound (s.sup id + 1))
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => ?_) fun i _ _ => by positivity
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))
  have hexp : Real.exp 516 < 2 ^ 745 := by
    have h1 : Real.exp 516 = Real.exp 1 ^ 516 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h1]
    calc Real.exp 1 ^ 516 < (2.7182818286 : ℝ) ^ 516 :=
          pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
      _ ≤ 2 ^ 745 := by
          have hnat : (13591409143 : ℕ) ^ 516 ≤ 2 ^ 745 * 5000000000 ^ 516 := by decide +kernel
          have he : (2.7182818286 : ℝ) = 13591409143 / 5000000000 := by norm_num
          rw [he, div_pow, div_le_iff₀ (by positivity)]
          exact_mod_cast hnat
  have hq : (q n : ℝ) * ((516 : ℝ) / 517) ^ n < 2 ^ 745 :=
    lt_of_le_of_lt (hs.trans (Real.exp_le_exp.mpr hsum)) hexp
  have hpowR : ((517 : ℝ) / 516) ^ n ≤ 2 ^ 747 := by
    have h1 : ((517 : ℝ) / 516) ^ n ≤ ((517 : ℝ) / 516) ^ 267228 :=
      pow_le_pow_right₀ (by norm_num) hn
    have h2 : ((517 : ℝ) / 516) ^ 267228 ≤ 2 ^ 747 := by
      rw [div_pow, div_le_iff₀ (by positivity)]
      exact_mod_cast pow_bound
    exact h1.trans h2
  have hinv : (q n : ℝ) = (q n : ℝ) * ((516 : ℝ) / 517) ^ n * ((517 : ℝ) / 516) ^ n := by
    rw [mul_assoc, ← mul_pow]; norm_num
  have hfin : (q n : ℝ) < 2 ^ 1504 := by
    have hnn : (0 : ℝ) ≤ (q n : ℝ) * ((516 : ℝ) / 517) ^ n := by positivity
    calc (q n : ℝ) = (q n : ℝ) * ((516 : ℝ) / 517) ^ n * ((517 : ℝ) / 516) ^ n := hinv
      _ ≤ (q n : ℝ) * ((516 : ℝ) / 517) ^ n * 2 ^ 747 := mul_le_mul_of_nonneg_left hpowR hnn
      _ < 2 ^ 745 * 2 ^ 747 := by
          apply mul_lt_mul_of_pos_right hq (by positivity)
      _ ≤ 2 ^ 1504 := by
          rw [← pow_add]
          exact pow_le_pow_right₀ (by norm_num) (by norm_num)
  exact_mod_cast hfin

end Sun46
