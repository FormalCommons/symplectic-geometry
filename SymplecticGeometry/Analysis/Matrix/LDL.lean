/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Matrix.LDL

/-!
# Orthonormal columns by an upper triangular change of basis

For a rectangular matrix `F : Matrix m n 𝕜` over `ℝ` or `ℂ` whose `mulVec` is injective, this file
gives an upper triangular `P`, with injective `mulVec`, such that the columns of `F * P` are
orthonormal: `(F * P)ᴴ * (F * P) = 1`. This is the thin `QR` factorization of `F`, with `F * P` as
`Q` and `P` as the inverse of `R`.

* `Matrix.exists_isUpperTriangular_conjTranspose_mul_mul_self_eq_one`: the statement above.

The proof normalizes the positive-definite Gram matrix `Fᴴ * F` by Tau Ceti's
`Matrix.PosDef.exists_isUpperTriangular_conjTranspose_mul_mul_eq_one`. It follows the proof of
Tau Ceti's `QR` factorization
`Matrix.GeneralLinearGroup.exists_mem_upperTriangularGroup_toUnits_mul_eq`, for a rectangular
matrix with injective `mulVec` in place of an invertible one.

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, 2nd ed., Cambridge University Press, 2013,
  Section 2.1 (the `QR` factorization), as Tau Ceti's `QR.lean` cites.
-/

public section

open scoped ComplexOrder Matrix

namespace Matrix

variable {m n 𝕜 : Type*} [RCLike 𝕜] [Fintype m] [Fintype n] [LinearOrder n]

/-- **Thin `QR` factorization.** If `F : Matrix m n 𝕜` has injective `mulVec`, there is an upper
triangular `P : Matrix n n 𝕜` with injective `mulVec` such that `F * P` has orthonormal columns,
`(F * P)ᴴ * (F * P) = 1`. -/
theorem exists_isUpperTriangular_conjTranspose_mul_mul_self_eq_one (F : Matrix m n 𝕜)
    (hF : Function.Injective F.mulVec) :
    ∃ P : Matrix n n 𝕜, P.IsUpperTriangular ∧ Function.Injective P.mulVec ∧
      (F * P)ᴴ * (F * P) = 1 := by
  classical
  obtain ⟨P, hPt, hP⟩ :=
    (PosDef.conjTranspose_mul_self F hF).exists_isUpperTriangular_conjTranspose_mul_mul_eq_one
  refine ⟨P, hPt, mulVec_injective_of_isUnit
    (IsUnit.of_mul_eq_one_right (Pᴴ * Fᴴ * F) ?_), ?_⟩ <;>
    simpa only [conjTranspose_mul, Matrix.mul_assoc] using hP

end Matrix

end
