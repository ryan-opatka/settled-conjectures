import Sun46.Table

/-!
# `q(m) + 1` is composite for every `m` in the table

For each triple `(m, v, f)` the kernel checks that `v + 1` is not prime: either `f` is a proper
divisor of `v + 1`, or (`f = 0`) `2 ^ v` is not `1` modulo `v + 1`.
-/

namespace Sun46

open Nat

/-- The certificate `f` shows that `v + 1` is composite. -/
def compOK (v f : ℕ) : Bool :=
  bif Nat.beq f 0 then Nat.ble 2 v && !(Nat.beq (powMod 2 (v + 1) 1504 v) 1)
  else Nat.ble 2 f && (Nat.ble (f + 1) (v + 1) && Nat.beq ((v + 1) % f) 0)

theorem compOK_sound {v f : ℕ} (hv : v < 2 ^ 1504) (h : compOK v f = true) : ¬ (v + 1).Prime := by
  unfold compOK at h
  by_cases hf : f = 0
  · rw [beq_true_of_eq hf] at h
    simp only [Bool.cond_true, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨h2, hne⟩ := h
    have hv2 : 2 ≤ v := Nat.le_of_ble_eq_true h2
    have hpm := powMod_eq 2 (v + 1) 1504 v hv
    refine not_prime_of_fermat (N := v + 1) (by omega) ?_
    rw [Nat.add_sub_cancel, ← hpm]
    intro h1
    rw [h1] at hne
    exact absurd hne (by decide)
  · rw [beq_false_of_ne hf] at h
    simp only [Bool.cond_false, Bool.and_eq_true] at h
    obtain ⟨h2, h3, h4⟩ := h
    have hf2 : 2 ≤ f := Nat.le_of_ble_eq_true h2
    have hfv : f + 1 ≤ v + 1 := Nat.le_of_ble_eq_true h3
    have hd : f ∣ v + 1 := Nat.dvd_of_mod_eq_zero (Nat.eq_of_beq_eq_true h4)
    exact Nat.not_prime_of_dvd_of_lt hd hf2 (by omega)

/-- All certificates in a list are valid. -/
def compAll (L : List (ℕ × ℕ × ℕ)) : Bool := L.all fun t => compOK t.2.1 t.2.2

theorem compPart0 : compAll certPart0 = true := by decide +kernel
theorem compPart1 : compAll certPart1 = true := by decide +kernel
theorem compPart2 : compAll certPart2 = true := by decide +kernel
theorem compPart3 : compAll certPart3 = true := by decide +kernel
theorem compPart4 : compAll certPart4 = true := by decide +kernel
theorem compPart5 : compAll certPart5 = true := by decide +kernel
theorem compPart6 : compAll certPart6 = true := by decide +kernel
theorem compPart7 : compAll certPart7 = true := by decide +kernel
theorem compPart8 : compAll certPart8 = true := by decide +kernel
theorem compPart9 : compAll certPart9 = true := by decide +kernel
theorem compPart10 : compAll certPart10 = true := by decide +kernel
theorem compPart11 : compAll certPart11 = true := by decide +kernel

theorem compAll_append {A B : List (ℕ × ℕ × ℕ)} (ha : compAll A = true) (hb : compAll B = true) :
    compAll (A ++ B) = true := by
  unfold compAll at *
  rw [List.all_append, ha, hb]
  rfl

theorem compAll_certAll : ∀ t ∈ certAll, compOK t.2.1 t.2.2 = true := by
  have h : compAll certAll = true := by
    rw [certAll]
    have h1 := compAll_append compPart0 compPart1
    have h2 := compAll_append h1 compPart2
    have h3 := compAll_append h2 compPart3
    have h4 := compAll_append h3 compPart4
    have h5 := compAll_append h4 compPart5
    have h6 := compAll_append h5 compPart6
    have h7 := compAll_append h6 compPart7
    have h8 := compAll_append h7 compPart8
    have h9 := compAll_append h8 compPart9
    have h10 := compAll_append h9 compPart10
    have h11 := compAll_append h10 compPart11
    exact h11
  intro t ht
  exact List.all_eq_true.mp h t ht

end Sun46
