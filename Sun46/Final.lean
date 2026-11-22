import Sun46.Chunks.All
import Sun46.Values
import Sun46.Composite

/-!
# Sun's Conjecture 4.6 is false

`Sun46.Conjecture` (see `Sun46/Statement.lean`) fails at `n = 267497`.

* `sweep_all` (`Sun46/Chunks/`): for every `k` from `1` to `267496`, if
  `m = φ(k) + φ(267497 - k)/4` is an integer with `m - 1` and `m + 1` prime, then `m` is one of the
  `1752` numbers in `mList`.
* `q_table` (`Sun46/Values.lean`): the table gives the right value of `q m` for each of
  them.
* `compAll_certAll` (`Sun46/Composite.lean`): `q m + 1` is composite for each of them.
-/

namespace Sun46

/-- The list of the sweep is the list of the table. -/
theorem mList_eq : mList = certAll.map fun t => t.1 := by decide +kernel

/-- `q m + 1` is not prime for any `m` in the table. -/
theorem not_prime_of_mem : ∀ t ∈ certAll, ¬ (q t.1 + 1).Prime := by
  intro t ht
  have hv := q_table t ht
  have hlt : t.2.1 < 2 ^ 1504 := by
    have hmem : (t.1, t.2.1) ∈ qTable := List.mem_map.mpr ⟨t, ht, rfl⟩
    have hle : t.1 ≤ Nq := Nat.le_of_ble_eq_true (List.all_eq_true.mp qTable_le _ hmem)
    rw [← hv]
    exact q_lt t.1 hle
  rw [hv]
  exact compOK_sound hlt (compAll_certAll t ht)

/-- No `k` works for `n = 267497`. -/
theorem no_works : ¬ ∃ k, Works 267497 k := by
  rintro ⟨k, hw⟩
  have hstep : ∀ k, 1 ≤ k → k < 267497 → stepOK 267497 (bitsOf mList) k = true :=
    fun k h1 h2 => rangeOK_sound 267497 Sbits 267496 1 sweep_all k h1 (by omega)
  obtain ⟨m, hm, hp⟩ := works_mem (by norm_num) hstep hw
  rw [mList_eq, List.mem_map] at hm
  obtain ⟨t, ht, rfl⟩ := hm
  exact not_prime_of_mem t ht hp

/-- **Sun's Conjecture 4.6 is false.** -/
theorem conjecture_false : ¬ Conjecture := fun h => no_works (h 267497 (by norm_num))

end Sun46

#print axioms Sun46.conjecture_false
