import Sun46.Pack
import Sun46.Digits
import Sun46.Table

/-!
# One number holding every strict partition number up to 267228

`Kq` is a single number of about `4 * 10 ^ 8` bits, defined by a computation the kernel can run:
the pentagonal number of `Sun46/Kronecker.lean` at `2 ^ 1504`, inverted modulo
`2 ^ (1504 * 267229)` by Newton's iteration, times the same pentagonal number at `2 ^ 3008`.

This file only defines it. The kernel evaluates three facts about it in `Check1.lean`,
`Check2.lean` and `Check3.lean`, and `Values.lean` draws the conclusion.
-/

namespace Sun46

/-- An inverse of the odd number `D` modulo `2 ^ L`, by Newton's iteration. Nothing is proved
about it: its output is checked. -/
def newton (D : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | f + 1, L =>
    bif Nat.ble L 1 then 1
    else modP (newton D f ((L + 1) / 2) *
      (Nat.shiftLeft 1 L + 2 - modP (modP D L * newton D f ((L + 1) / 2)) L)) L

/-! ### The concrete numbers -/

/-- Bits per table entry. -/
def Wd : ℕ := 1504

/-- The largest index in the table. -/
def Nq : ℕ := 267228

theorem Wd_eq : Wd = 1504 := rfl

theorem Nq_eq : Nq = 267228 := rfl

/-- The `+` terms of the pentagonal series at `2 ^ Wd`. -/
noncomputable def PhiP : ℕ := pk expP Wd 9 0 422

/-- The `-` terms of the pentagonal series at `2 ^ Wd`. -/
noncomputable def PhiN : ℕ := shl (pk expN Wd 9 0 422) (Wd * expN 0)

/-- The `+` terms of the pentagonal series at `2 ^ (2 * Wd)`. -/
noncomputable def EP : ℕ := pk expP (2 * Wd) 9 0 299

/-- The `-` terms of the pentagonal series at `2 ^ (2 * Wd)`. -/
noncomputable def EN : ℕ := shl (pk expN (2 * Wd) 9 0 299) (2 * Wd * expN 0)

/-- An inverse of the pentagonal number modulo `2 ^ (Wd * (Nq + 1))`. -/
noncomputable def INVq : ℕ :=
  newton (modP (PhiP + (Nat.shiftLeft 1 (Wd * (Nq + 1)) - modP PhiN (Wd * (Nq + 1))))
    (Wd * (Nq + 1))) 40 (Wd * (Nq + 1))

/-- The packed table of `q`. -/
noncomputable def Kq : ℕ :=
  modP (modP (EP + (Nat.shiftLeft 1 (Wd * (Nq + 1)) - modP EN (Wd * (Nq + 1))))
    (Wd * (Nq + 1)) * INVq) (Wd * (Nq + 1))

/-- The pairs `(m, v)` of the certificate list. -/
def qTable : List (ℕ × ℕ) := certAll.map fun t => (t.1, t.2.1)

end Sun46
