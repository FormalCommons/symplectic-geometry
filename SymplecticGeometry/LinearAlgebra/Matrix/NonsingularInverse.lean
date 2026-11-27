/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import SymplecticGeometry.Algebra.GroupWithZero.Units.Basic

/-!
# The inverse of a matrix of square `-1`

A square matrix `A` over a commutative ring with `A * A = -1` has inverse `A⁻¹ = -A`. This is
the matrix case of `Ring.inverse_eq_neg_of_mul_self_eq_neg_one`, through Mathlib's
`Matrix.nonsing_inv_eq_ringInverse`; Mathlib's `Matrix.SpecialLinearGroup.S_inv` is the same
fact for one particular matrix.

## Main results

* `Matrix.inv_eq_neg_of_mul_self_eq_neg_one`: if `A * A = -1`, then `A⁻¹ = -A`.
-/

public section

namespace Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- A square matrix of square `-1` has inverse its negative. -/
theorem inv_eq_neg_of_mul_self_eq_neg_one {A : Matrix n n R} (hA : A * A = -1) : A⁻¹ = -A := by
  rw [nonsing_inv_eq_ringInverse, Ring.inverse_eq_neg_of_mul_self_eq_neg_one hA]

end Matrix

end
