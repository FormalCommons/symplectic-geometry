/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Notation.Pi.Basic

/-!
# Updating a function by a nonzero value

`Function.update_ne_zero`: changing one value of a function to a nonzero value gives a nonzero
function. It supplements Mathlib's `Mathlib.Algebra.Notation.Pi.Basic`.
-/

public section

/-- Updating a function at one point by a nonzero value gives a nonzero function. -/
theorem Function.update_ne_zero {ι : Type*} {M : ι → Type*} [DecidableEq ι] [∀ i, Zero (M i)]
    (f : ∀ i, M i) (i : ι) {b : M i} (hb : b ≠ 0) : Function.update f i b ≠ 0 :=
  ne_of_apply_ne (· i) (by simpa using hb)

end
