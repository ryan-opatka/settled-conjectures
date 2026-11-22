import Sun46.Check2

/-!
# Third kernel check: the table lists digits of `Kq`

About 7 GB of memory. See `Check1.lean` for why this is a file of its own.
-/

namespace Sun46

/-- Every pair `(m, v)` of the table has `v` equal to digit `m` of `Kq` in base `2 ^ Wd`. -/
theorem chk3 : tableOK Wd 19 Kq 0 qTable = true := by decide +kernel

end Sun46
