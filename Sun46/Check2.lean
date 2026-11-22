import Sun46.Check1

/-!
# Second kernel check: `Kq` satisfies the identity

About 6 GB of memory. See `Check1.lean` for why this is a file of its own.
-/

namespace Sun46

/-- `Kq` times the pentagonal number at `2 ^ Wd` is the pentagonal number at `2 ^ (2 * Wd)`. -/
theorem chk2 :
    modP (Kq * PhiP + EN) (Wd * (Nq + 1)) = modP (Kq * PhiN + EP) (Wd * (Nq + 1)) := by
  decide +kernel

end Sun46
