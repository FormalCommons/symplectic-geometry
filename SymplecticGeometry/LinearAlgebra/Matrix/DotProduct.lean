/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.DotProduct

/-!
# Matrices with orthonormal columns preserve the Hermitian dot product

* `Matrix.star_mulVec_dotProduct_mulVec`: a matrix with orthonormal columns, `Aᴴ * A = 1`,
  preserves the Hermitian product `star z ⬝ᵥ v`. It is the case `M = 1` of Tau Ceti's
  `Matrix.star_dotProduct_conjTranspose_mul_mul_mulVec`, in
  `TauCeti/LinearAlgebra/Matrix/DotProduct.lean`.
-/

public section

namespace Matrix

variable {l m R : Type*} [Fintype l] [Fintype m]

/-- A matrix with orthonormal columns, `Aᴴ * A = 1`, preserves the Hermitian product
`star z ⬝ᵥ v`. This is the case `M = 1` of `Matrix.star_dotProduct_conjTranspose_mul_mul_mulVec`.
-/
theorem star_mulVec_dotProduct_mulVec [Semiring R] [StarRing R] [DecidableEq m]
    {A : Matrix l m R} (hA : Aᴴ * A = 1) (z v : m → R) :
    star (A *ᵥ z) ⬝ᵥ (A *ᵥ v) = star z ⬝ᵥ v := by
  classical
  simpa [hA] using (star_dotProduct_conjTranspose_mul_mul_mulVec A 1 z v).symm

end Matrix

end
