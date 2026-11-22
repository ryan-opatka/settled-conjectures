import Sun46.Check3

/-!
# The strict partition numbers, checked by the kernel

`Kq` (`Number.lean`) is a single number of about `4 * 10 ^ 8` bits. The kernel has computed it,
checked the identity of `Sun46/Kronecker.lean` with two multiplications (`Check1.lean`,
`Check2.lean`), and compared `1752` of its base `2 ^ 1504` digits with the table (`Check3.lean`).
Together with the size bound of `Bound.lean` this proves that the digit of `Kq` in position `a` is
`q a` for every `a ≤ 267228`, and so that every value in the table is right.
-/

namespace Sun46

open Finset

/-- The algebra: if `K` satisfies the identity modulo `2 ^ L` and the pentagonal number is
invertible, then `K` is the packed table of `q`. -/
theorem kron_solve (W N L J J2 PhiP PhiN EP EN INV K : ℕ) (hL : L = W * (N + 1))
    (hJ : N < gNeg J) (hJ2 : N / 2 < gNeg J2)
    (hPhiP : PhiP = ∑ j ∈ range J, (2 ^ W) ^ expP j)
    (hPhiN : PhiN = ∑ j ∈ range J, (2 ^ W) ^ expN j)
    (hEP : EP = ∑ j ∈ range J2, ((2 ^ W) ^ 2) ^ expP j)
    (hEN : EN = ∑ j ∈ range J2, ((2 ^ W) ^ 2) ^ expN j)
    (h1 : (INV * PhiP) % 2 ^ L = (INV * PhiN + 1) % 2 ^ L)
    (h2 : (K * PhiP + EN) % 2 ^ L = (K * PhiN + EP) % 2 ^ L)
    (hK : K < 2 ^ L) (hq : ∀ a, a ≤ N → q a < 2 ^ W) :
    K = ∑ a ∈ range (N + 1), q a * (2 ^ W) ^ a := by
  have hM : 2 ^ L = (2 ^ W) ^ (N + 1) := by rw [hL, pow_mul]
  generalize 2 ^ L = M at hM h1 h2 hK
  generalize 2 ^ W = B at hM hPhiP hPhiN hEP hEN hq ⊢
  have c1 : (INV : ZMod M) * ((PhiP : ZMod M) - (PhiN : ZMod M)) = 1 := by
    have e : ((INV * PhiP : ℕ) : ZMod M) = ((INV * PhiN + 1 : ℕ) : ZMod M) :=
      (ZMod.natCast_eq_natCast_iff' _ _ _).mpr h1
    push_cast at e
    linear_combination e
  have c2 : (K : ZMod M) * ((PhiP : ZMod M) - (PhiN : ZMod M)) = (EP : ZMod M) - (EN : ZMod M) := by
    have e : ((K * PhiP + EN : ℕ) : ZMod M) = ((K * PhiN + EP : ℕ) : ZMod M) :=
      (ZMod.natCast_eq_natCast_iff' _ _ _).mpr h2
    push_cast at e
    linear_combination e
  have c3 : ((∑ a ∈ range (N + 1), q a * B ^ a : ℕ) : ZMod M) *
      ((PhiP : ZMod M) - (PhiN : ZMod M)) = (EP : ZMod M) - (EN : ZMod M) := by
    have k := kron_identity B N M J J2 hM hJ hJ2
    have k2 := pent_sum_cast M (B ^ 2) J2
    rw [Nat.cast_pow] at k2
    rw [pent_sum_cast M B J, k2, ← hPhiP, ← hPhiN, ← hEP, ← hEN] at k
    rw [← k]
    push_cast
    rfl
  have c4 : (K : ZMod M) = ((∑ a ∈ range (N + 1), q a * B ^ a : ℕ) : ZMod M) := by
    calc (K : ZMod M) = (K : ZMod M) * ((INV : ZMod M) * ((PhiP : ZMod M) - (PhiN : ZMod M))) := by
          rw [c1, mul_one]
      _ = (INV : ZMod M) * ((K : ZMod M) * ((PhiP : ZMod M) - (PhiN : ZMod M))) := by ring
      _ = (INV : ZMod M) * (((∑ a ∈ range (N + 1), q a * B ^ a : ℕ) : ZMod M) *
            ((PhiP : ZMod M) - (PhiN : ZMod M))) := by rw [c2, c3]
      _ = ((∑ a ∈ range (N + 1), q a * B ^ a : ℕ) : ZMod M) *
            ((INV : ZMod M) * ((PhiP : ZMod M) - (PhiN : ZMod M))) := by ring
      _ = ((∑ a ∈ range (N + 1), q a * B ^ a : ℕ) : ZMod M) := by rw [c1, mul_one]
  have hmod := (ZMod.natCast_eq_natCast_iff' _ _ _).mp c4
  have hS : ∑ a ∈ range (N + 1), q a * B ^ a < M := by
    rw [hM]
    exact sum_lt_pow B q (N + 1) fun a ha => hq a (by omega)
  rwa [Nat.mod_eq_of_lt hK, Nat.mod_eq_of_lt hS] at hmod

/-! ### Small generic facts

They are stated with variables so that, later, nothing has to be unfolded when the variables are
replaced by the large concrete numbers. -/

theorem modP_lt (x L : ℕ) : modP x L < 2 ^ L := by
  rw [modP_eq]
  exact Nat.mod_lt _ (Nat.pow_pos (by norm_num))

/-- `pk_eq` from position `0` when `g 0 = 0`. -/
theorem pk_eq_zero (g : ℕ → ℕ) (hg : Monotone g) (w f cnt : ℕ) (h0 : g 0 = 0)
    (hc : cnt ≤ 2 ^ f) : pk g w f 0 cnt = ∑ i ∈ range cnt, 2 ^ (w * g i) := by
  have h := pk_eq g hg w f 0 cnt hc
  rw [h0, Nat.mul_zero, pow_zero, Nat.mul_one] at h
  rw [h]
  exact Finset.sum_congr rfl fun i _ => by rw [Nat.zero_add]

/-- `pk_eq` from position `0`, with the shift. -/
theorem pk_shl_eq (g : ℕ → ℕ) (hg : Monotone g) (w f cnt : ℕ) (hc : cnt ≤ 2 ^ f) :
    shl (pk g w f 0 cnt) (w * g 0) = ∑ i ∈ range cnt, 2 ^ (w * g i) := by
  rw [shl_eq, pk_eq g hg w f 0 cnt hc]
  exact Finset.sum_congr rfl fun i _ => by rw [Nat.zero_add]

theorem two_pow_mul_le (w a b : ℕ) (h : a ≤ b) : 2 ^ (w * a) ≤ 2 ^ (w * b) :=
  Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left w h)

theorem one_lt_two_pow' (w : ℕ) (h : w ≠ 0) : 1 < 2 ^ w := Nat.one_lt_two_pow h

/-! ### What the checks give -/

theorem qTable_le : (qTable.all fun c => Nat.ble c.1 Nq) = true := by decide +kernel

theorem expP_zero : expP 0 = 0 := by decide

theorem PhiP_eq : PhiP = ∑ j ∈ range 422, (2 ^ Wd) ^ expP j := by
  rw [PhiP, pk_eq_zero expP expP_mono Wd 9 422 expP_zero (by norm_num)]
  exact Finset.sum_congr rfl fun j _ => by rw [pow_mul]

theorem PhiN_eq : PhiN = ∑ j ∈ range 422, (2 ^ Wd) ^ expN j := by
  rw [PhiN, pk_shl_eq expN expN_mono Wd 9 422 (by norm_num)]
  exact Finset.sum_congr rfl fun j _ => by rw [pow_mul]

theorem EP_eq : EP = ∑ j ∈ range 299, ((2 ^ Wd) ^ 2) ^ expP j := by
  rw [EP, pk_eq_zero expP expP_mono (2 * Wd) 9 299 expP_zero (by norm_num)]
  exact Finset.sum_congr rfl fun j _ => by rw [Nat.mul_comm 2 Wd, pow_mul, pow_mul]

theorem EN_eq : EN = ∑ j ∈ range 299, ((2 ^ Wd) ^ 2) ^ expN j := by
  rw [EN, pk_shl_eq expN expN_mono (2 * Wd) 9 299 (by norm_num)]
  exact Finset.sum_congr rfl fun j _ => by rw [Nat.mul_comm 2 Wd, pow_mul, pow_mul]

theorem Kq_lt : Kq < 2 ^ (Wd * (Nq + 1)) := by
  rw [Kq]
  exact modP_lt _ _

theorem q_lt_Wd (a : ℕ) (ha : a ≤ Nq) : q a < 2 ^ Wd := by
  rw [Nq_eq] at ha
  rw [Wd_eq]
  exact q_lt a ha

/-- `Kq` is the packed table of `q`. -/
theorem Kq_eq : Kq = ∑ a ∈ range (Nq + 1), q a * (2 ^ Wd) ^ a := by
  have e1 := chk1
  have e2 := chk2
  rw [modP_eq, modP_eq] at e1 e2
  exact kron_solve Wd Nq (Wd * (Nq + 1)) 422 299 PhiP PhiN EP EN INVq Kq rfl (by decide)
    (by decide) PhiP_eq PhiN_eq EP_eq EN_eq e1 e2 Kq_lt q_lt_Wd

/-- Every value in the table is right. -/
theorem q_table : ∀ t ∈ certAll, q t.1 = t.2.1 := by
  intro t ht
  have h3 := chk3
  have hmem : (t.1, t.2.1) ∈ qTable := List.mem_map.mpr ⟨t, ht, rfl⟩
  have hle : t.1 ≤ Nq := Nat.le_of_ble_eq_true (List.all_eq_true.mp qTable_le _ hmem)
  have hNq : Nq + 1 ≤ 2 ^ 19 := by decide
  have hK' : Kq < 2 ^ (Wd * 2 ^ 19) := lt_of_lt_of_le Kq_lt (two_pow_mul_le Wd _ _ hNq)
  have hd := tableOK_sound Wd 19 Kq 0 qTable hK' h3 (t.1, t.2.1) hmem (Nat.zero_le _)
    (by simp only [Nat.zero_add]; omega)
  simp only [Nat.sub_zero] at hd
  rw [← hd, pow_mul, Kq_eq]
  exact (digit_sum (2 ^ Wd) (one_lt_two_pow' Wd (by decide)) q (Nq + 1) t.1
    (fun a ha => q_lt_Wd a (by omega)) (by omega)).symm

end Sun46
