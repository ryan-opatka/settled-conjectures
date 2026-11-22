import Sun46.Number
import Sun46.Bound
import Sun46.Composite
import Sun46.Chunks.All

/-!
# First kernel check: the pentagonal number is invertible

About 4 GB of memory. The three checks are in three files because, as three theorems of one
file, they ran out of 15 GB: the memory of one was not given back before the next began.

The statements are equations between the numbers themselves, with no definition wrapped around
them. A later proof that had to unfold such a wrapper to reach `Nat.beq` would make the kernel
run the whole computation again.

The imports other than `Number` are not used. They are here so that `lake build` finishes the
other memory-heavy files before it starts this one. `Check2` and `Check3` import this file for
the same reason.
-/

namespace Sun46

/-- `INVq` is an inverse of the pentagonal number modulo `2 ^ (Wd * (Nq + 1))`. -/
theorem chk1 :
    modP (INVq * PhiP) (Wd * (Nq + 1)) = modP (INVq * PhiN + 1) (Wd * (Nq + 1)) := by
  decide +kernel

end Sun46
