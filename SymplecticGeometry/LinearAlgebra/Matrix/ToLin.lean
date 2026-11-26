/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
import SymplecticGeometry.Data.Matrix.Mul

/-!
# The linear map of a matrix with a left inverse is injective

* `Matrix.toLin'_injective_of_mul_eq_one`: if a (possibly rectangular) matrix `A` has a left
  inverse, `B * A = 1`, then the linear map `Matrix.toLin' A` is injective. This is
  `Matrix.mulVec_injective_of_mul_eq_one`, in `SymplecticGeometry/Data/Matrix/Mul.lean`, read
  through `Matrix.toLin'_apply'`; it sits here because `Matrix.toLin'` is defined in Mathlib's
  `Mathlib/LinearAlgebra/Matrix/ToLin.lean`.
-/

public section

namespace Matrix

variable {l m R : Type*} [Fintype l] [Fintype m] [CommSemiring R] [DecidableEq m]

/-- A matrix with a left inverse, `B * A = 1`, gives an injective linear map `Matrix.toLin' A`. -/
theorem toLin'_injective_of_mul_eq_one {A : Matrix l m R} {B : Matrix m l R} (h : B * A = 1) :
    Function.Injective (toLin' A) := by
  rw [toLin'_apply', coe_mulVecLin]
  exact mulVec_injective_of_mul_eq_one h

end Matrix

end
