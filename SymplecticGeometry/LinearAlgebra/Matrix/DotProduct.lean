/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Matrices with a left inverse, and the Hermitian dot product

* `Matrix.mulVec_injective_of_mul_eq_one`: a (possibly rectangular) matrix `A` with a left
  inverse, `B * A = 1`, acts injectively on vectors. Mathlib's
  `Matrix.mulVec_injective_of_isUnit` is the case of a square invertible matrix.
* `Matrix.star_mulVec_dotProduct_mulVec`: a matrix with orthonormal columns, `Aᴴ * A = 1`,
  preserves the Hermitian product `star z ⬝ᵥ v`.
-/

public section

open Function

namespace Matrix

variable {l m R : Type*} [Fintype l] [Fintype m]

/-- A matrix with a left inverse acts injectively on vectors: `A.mulVec` is injective. -/
theorem mulVec_injective_of_mul_eq_one [Semiring R] [DecidableEq m] {A : Matrix l m R}
    {B : Matrix m l R} (h : B * A = 1) : Injective A.mulVec := fun z w hzw ↦ by
  simpa [mulVec_mulVec, h] using congrArg (B *ᵥ ·) hzw

/-- A matrix with orthonormal columns, `Aᴴ * A = 1`, preserves the Hermitian product
`star z ⬝ᵥ v`. -/
theorem star_mulVec_dotProduct_mulVec [Semiring R] [StarRing R] [DecidableEq m]
    {A : Matrix l m R} (hA : Aᴴ * A = 1) (z v : m → R) :
    star (A *ᵥ z) ⬝ᵥ (A *ᵥ v) = star z ⬝ᵥ v := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hA, one_mulVec]

end Matrix

end
