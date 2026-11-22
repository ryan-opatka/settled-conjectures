import Sun46.Statement

/-!
# Fast arithmetic for the kernel

Everything here is about numbers below `521 ^ 2 = 271441`.

* `P` is the product of the primes below `521`, so a number `x` in `(509, 271441)` is prime
  exactly when `Nat.gcd x P = 1`. The kernel computes that `gcd` in one step.
* `phiF` computes Euler's totient by splitting off one small prime factor at a time.
* `powMod` is square-and-multiply, used for Fermat's test.

The functions are written with `Nat.beq`, `Nat.ble` and `cond`, which the kernel evaluates
quickly, and each is proved equal to what it is meant to compute.
-/

namespace Sun46

open Nat

/-- The primes below `521`. -/
def smallPrimes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79,
   83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167,
   173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263,
   269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367,
   373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463,
   467, 479, 487, 491, 499, 503, 509]

set_option linter.style.longLine false in
/-- The product of the primes below `521`. -/
def P : ℕ := 31964081287196888554640742530273949712805599189441373009521636182430667982828077742788853029807931798207106885718293402541861369758591699412090677759187666930105491469725350718941073722934985042092154205321144030

theorem P_eq : P = smallPrimes.prod := by decide +kernel

theorem smallPrimes_prime : ∀ p ∈ smallPrimes, p.Prime := by
  have key : ∀ p ∈ smallPrimes, 2 ≤ p ∧ ∀ m < p, m ∣ p → m = 1 := by decide +kernel
  intro p hp
  exact Nat.prime_def_lt.mpr (key p hp)

theorem mem_smallPrimes {p : ℕ} (hp : p.Prime) (h : p < 521) : p ∈ smallPrimes := by
  have key : ∀ p < 521, (2 ≤ p ∧ ∀ m < p, m ∣ p → m = 1) → p ∈ smallPrimes := by
    decide +kernel
  exact key p h (Nat.prime_def_lt.mp hp)

theorem smallPrimes_le : ∀ p ∈ smallPrimes, p ≤ 509 := by decide +kernel

theorem dvd_P {p : ℕ} (hp : p ∈ smallPrimes) : p ∣ P := by
  rw [P_eq]
  exact List.dvd_prod hp

/-- A number below `521 ^ 2` with no prime factor below `521` is prime. -/
theorem prime_of_no_small {x : ℕ} (h2 : 2 ≤ x) (hx : x < 271441)
    (h : ∀ p ∈ smallPrimes, ¬ p ∣ x) : x.Prime := by
  by_contra hnp
  have hmf : (x.minFac).Prime := Nat.minFac_prime (by omega)
  have hsq : x.minFac ^ 2 ≤ x := Nat.minFac_sq_le_self (by omega) hnp
  have hlt : x.minFac < 521 := by
    by_contra hge
    have h521 : 521 ^ 2 ≤ x.minFac ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  exact h _ (mem_smallPrimes hmf hlt) (Nat.minFac_dvd x)

theorem prime_of_gcd {x : ℕ} (h2 : 2 ≤ x) (hx : x < 271441) (h : Nat.gcd x P = 1) :
    x.Prime :=
  prime_of_no_small h2 hx fun p hp hpx => by
    have hd : p ∣ Nat.gcd x P := Nat.dvd_gcd hpx (dvd_P hp)
    rw [h] at hd
    exact (smallPrimes_prime p hp).one_lt.ne' (Nat.dvd_one.mp hd)

theorem gcd_of_prime {x : ℕ} (hx : 509 < x) (hp : x.Prime) : Nat.gcd x P = 1 := by
  refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hdvd => ?_
  rw [P_eq] at hdvd
  obtain ⟨a, ha, hxa⟩ := (Prime.dvd_prod_iff (Nat.prime_iff.mp hp)).mp hdvd
  have hEq := (Nat.prime_dvd_prime_iff_eq hp (smallPrimes_prime a ha)).mp hxa
  have hle := smallPrimes_le a ha
  omega

/-! ### Euler's totient -/

/-- The first element of the list that divides `k`, or `0` if there is none. -/
def firstDiv (k : ℕ) : List ℕ → ℕ
  | [] => 0
  | p :: ps => bif Nat.beq (k % p) 0 then p else firstDiv k ps

theorem firstDiv_spec (k : ℕ) : ∀ L : List ℕ, (∀ p ∈ L, p ≠ 0) →
    (firstDiv k L = 0 ∧ ∀ p ∈ L, ¬ p ∣ k) ∨ (firstDiv k L ∈ L ∧ firstDiv k L ∣ k)
  | [], _ => Or.inl ⟨rfl, by simp⟩
  | p :: ps, h => by
    by_cases hd : k % p = 0
    · right
      have hb : Nat.beq (k % p) 0 = true := by rw [hd]; rfl
      simp only [firstDiv, hb, Bool.cond_true]
      exact ⟨List.mem_cons_self, Nat.dvd_of_mod_eq_zero hd⟩
    · have hb : Nat.beq (k % p) 0 = false := by
        cases hbb : Nat.beq (k % p) 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true hbb) hd
      simp only [firstDiv, hb, Bool.cond_false]
      rcases firstDiv_spec k ps (fun x hx => h x (List.mem_cons_of_mem _ hx)) with
        ⟨h0, hn⟩ | ⟨hm, hdv⟩
      · left
        refine ⟨h0, fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact fun hx => hd (Nat.mod_eq_zero_of_dvd hx)
        · exact hn x hx'
      · right
        exact ⟨List.mem_cons_of_mem _ hm, hdv⟩

/-- Euler's totient, by splitting off one prime factor below `521` at a time. The first
argument bounds the number of steps. -/
def phiAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, k =>
    bif Nat.ble k 1 then 1
    else bif Nat.beq (Nat.gcd k P) 1 then k - 1
    else bif Nat.beq (firstDiv k smallPrimes) 0 then k - 1
    else bif Nat.beq ((k / firstDiv k smallPrimes) % firstDiv k smallPrimes) 0 then
      firstDiv k smallPrimes * phiAux f (k / firstDiv k smallPrimes)
    else (firstDiv k smallPrimes - 1) * phiAux f (k / firstDiv k smallPrimes)

theorem beq_false_of_ne {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem beq_true_of_eq {a b : ℕ} (h : a = b) : Nat.beq a b = true := by
  subst h; exact Nat.beq_refl a

theorem phiAux_eq : ∀ f k : ℕ, 1 ≤ k → k < 2 ^ f → k < 271441 → phiAux f k = φ k
  | 0, k, h1, hf, _ => by simp at hf; omega
  | f + 1, k, h1, hf, hk => by
    by_cases hk1 : k ≤ 1
    · have : k = 1 := by omega
      subst this
      simp [phiAux]
    have hble : Nat.ble k 1 = false := by
      cases hb : Nat.ble k 1
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true hb) hk1
    by_cases hg : Nat.gcd k P = 1
    · have hp : k.Prime := prime_of_gcd (by omega) hk hg
      simp only [phiAux, hble, Bool.cond_false, beq_true_of_eq hg, Bool.cond_true]
      exact (Nat.totient_prime hp).symm
    simp only [phiAux, hble, Bool.cond_false, beq_false_of_ne hg]
    have hpos : ∀ p ∈ smallPrimes, p ≠ 0 := fun p hp => (smallPrimes_prime p hp).pos.ne'
    rcases firstDiv_spec k smallPrimes hpos with ⟨h0, hn⟩ | ⟨hm, hdv⟩
    · have hp : k.Prime := prime_of_no_small (by omega) hk hn
      simp only [beq_true_of_eq h0, Bool.cond_true]
      exact (Nat.totient_prime hp).symm
    · generalize firstDiv k smallPrimes = p at hm hdv ⊢
      have hpp : p.Prime := smallPrimes_prime p hm
      have hp0 : p ≠ 0 := hpp.pos.ne'
      simp only [beq_false_of_ne hp0, Bool.cond_false]
      obtain ⟨r, rfl⟩ := hdv
      have hr : p * r / p = r := Nat.mul_div_cancel_left r hpp.pos
      rw [hr]
      have hr1 : 1 ≤ r := by
        rcases Nat.eq_zero_or_pos r with h | h
        · subst h; simp at h1
        · exact h
      have hrf : r < 2 ^ f := by
        have h2 : 2 * r ≤ p * r := Nat.mul_le_mul_right r hpp.two_le
        have : 2 ^ (f + 1) = 2 * 2 ^ f := by ring
        omega
      have hrk : r < 271441 := by
        have h2 : 2 * r ≤ p * r := Nat.mul_le_mul_right r hpp.two_le
        omega
      have ih := phiAux_eq f r hr1 hrf hrk
      by_cases hd : r % p = 0
      · simp only [beq_true_of_eq hd, Bool.cond_true, ih]
        exact (Nat.totient_mul_of_prime_of_dvd hpp (Nat.dvd_of_mod_eq_zero hd)).symm
      · simp only [beq_false_of_ne hd, Bool.cond_false, ih]
        exact (Nat.totient_mul_of_prime_of_not_dvd hpp
          (fun h => hd (Nat.mod_eq_zero_of_dvd h))).symm

/-- Euler's totient for arguments below `521 ^ 2`. -/
def phiF (k : ℕ) : ℕ := phiAux 19 k

theorem phiF_eq {k : ℕ} (h1 : 1 ≤ k) (hk : k < 271441) : phiF k = φ k :=
  phiAux_eq 19 k h1 (by omega) hk

/-! ### Modular powers and Fermat's test -/

/-- `a ^ e % N` by repeated squaring. The first argument bounds the number of bits of `e`. -/
def powMod (a N : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1 % N
  | f + 1, e =>
    bif Nat.beq e 0 then 1 % N
    else bif Nat.beq (e % 2) 0 then
      (powMod a N f (e / 2) * powMod a N f (e / 2)) % N
    else (powMod a N f (e / 2) * powMod a N f (e / 2) % N * a) % N

theorem powMod_eq (a N : ℕ) : ∀ f e : ℕ, e < 2 ^ f → powMod a N f e = a ^ e % N
  | 0, e, h => by
    have : e = 0 := by simpa using h
    subst this; simp [powMod]
  | f + 1, e, h => by
    by_cases he : e = 0
    · subst he; simp [powMod]
    have hhalf : e / 2 < 2 ^ f := by
      have : 2 ^ (f + 1) = 2 * 2 ^ f := by ring
      omega
    have ih := powMod_eq a N f (e / 2) hhalf
    simp only [powMod, beq_false_of_ne he, Bool.cond_false, ih]
    by_cases h2 : e % 2 = 0
    · simp only [beq_true_of_eq h2, Bool.cond_true]
      have he2 : e = e / 2 + e / 2 := by omega
      conv_rhs => rw [he2, pow_add]
      exact (Nat.mul_mod _ _ _).symm
    · simp only [beq_false_of_ne h2, Bool.cond_false]
      have he2 : e = e / 2 + e / 2 + 1 := by omega
      conv_rhs => rw [he2, pow_succ, pow_add]
      rw [Nat.mul_mod (a ^ (e / 2) * a ^ (e / 2)) a N, Nat.mul_mod (a ^ (e / 2)) (a ^ (e / 2)) N]
      simp [Nat.mul_mod]

/-- Fermat's test to base `2`. -/
theorem not_prime_of_fermat {N : ℕ} (hN : 2 < N) (h : 2 ^ (N - 1) % N ≠ 1) : ¬ N.Prime := by
  intro hp
  have hcop : Nat.Coprime 2 N := by
    rw [Nat.coprime_comm]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd => by
      have := Nat.le_of_dvd (by norm_num) hd
      omega
  have hmod := Nat.ModEq.pow_totient hcop
  rw [Nat.totient_prime hp] at hmod
  have h1 : 1 % N = 1 := Nat.mod_eq_of_lt (by omega)
  exact h (by rw [hmod, h1])

end Sun46
