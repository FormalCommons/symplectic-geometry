/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Data.Matrix.Mul

/-!
# Matrices with a left inverse act injectively on vectors

* `Matrix.mulVec_injective_of_mul_eq_one`: a (possibly rectangular) matrix `A` with a left
  inverse, `B * A = 1`, acts injectively on vectors. Mathlib's
  `Matrix.mulVec_injective_of_isUnit`, in `Mathlib/Data/Matrix/Mul.lean`, is the case of a
  square invertible matrix.
-/

public section

open Function

namespace Matrix

variable {l m R : Type*} [Fintype l] [Fintype m]

/-- A matrix with a left inverse acts injectively on vectors: `A.mulVec` is injective. -/
theorem mulVec_injective_of_mul_eq_one [Semiring R] [DecidableEq m] {A : Matrix l m R}
    {B : Matrix m l R} (h : B * A = 1) : Injective A.mulVec := fun z w hzw ↦ by
  simpa [mulVec_mulVec, h] using congrArg (B *ᵥ ·) hzw

end Matrix

end
