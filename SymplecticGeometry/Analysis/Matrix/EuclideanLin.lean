/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Matrix.EuclideanLin

/-!
# Linear maps of invertible and of unitary matrices

Tau Ceti's `Matrix.toEuclideanCLE A hA` is the continuous linear automorphism of
`EuclideanSpace 𝕜 ι` given by a matrix `A` with `A.det ≠ 0`, and `Matrix.coe_toEuclideanCLE`
identifies its underlying continuous linear map. This file gives the same identification for the
underlying linear equivalence, read as a linear map. It also identifies the continuous linear
maps of Tau Ceti's `Matrix.UnitaryGroup.toLinearIsometryEquiv A`, for a unitary matrix `A`, and
of its inverse.

## Main results

* `Matrix.toLinearMap_toLinearEquiv_toEuclideanCLE`: the linear map underlying
  `(A.toEuclideanCLE hA).toLinearEquiv` is `Matrix.toEuclideanLin A`.
* `Matrix.UnitaryGroup.coe_toLinearIsometryEquiv`: the continuous linear map of
  `UnitaryGroup.toLinearIsometryEquiv A` is `Matrix.toEuclideanCLM A`;
  `Matrix.UnitaryGroup.coe_toLinearIsometryEquiv_symm`: that of its inverse is
  `Matrix.toEuclideanCLM (star A)`.
-/

public section

namespace Matrix

variable {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕜]

/-- The linear map underlying the linear equivalence of an invertible matrix `A` is the action
`Matrix.toEuclideanLin A` of `A` on `EuclideanSpace 𝕜 ι`. -/
@[simp]
theorem toLinearMap_toLinearEquiv_toEuclideanCLE (A : Matrix ι ι 𝕜) (hA : A.det ≠ 0) :
    ((A.toEuclideanCLE hA).toLinearEquiv : EuclideanSpace 𝕜 ι →ₗ[𝕜] EuclideanSpace 𝕜 ι) =
      A.toEuclideanLin :=
  LinearMap.ext (toEuclideanCLE_apply A hA)

/-- The continuous linear map of the linear isometry equivalence of a unitary matrix `A` is
`Matrix.toEuclideanCLM A`. -/
@[simp]
theorem UnitaryGroup.coe_toLinearIsometryEquiv (A : unitaryGroup ι 𝕜) :
    (UnitaryGroup.toLinearIsometryEquiv A : EuclideanSpace 𝕜 ι →L[𝕜] EuclideanSpace 𝕜 ι) =
      toEuclideanCLM (n := ι) (𝕜 := 𝕜) (A : Matrix ι ι 𝕜) := by
  ext x : 1
  simp [toLpLin_apply, UnitaryGroup.toLinearIsometryEquiv_apply]

/-- The continuous linear map of the inverse of the linear isometry equivalence of a unitary
matrix `A` is `Matrix.toEuclideanCLM (star A)`. -/
theorem UnitaryGroup.coe_toLinearIsometryEquiv_symm (A : unitaryGroup ι 𝕜) :
    ((UnitaryGroup.toLinearIsometryEquiv A).symm :
        EuclideanSpace 𝕜 ι →L[𝕜] EuclideanSpace 𝕜 ι) =
      toEuclideanCLM (n := ι) (𝕜 := 𝕜) (star (A : Matrix ι ι 𝕜)) := by
  ext x : 1
  simp only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rw [← UnitaryGroup.toLinearIsometryEquiv_inv_apply, UnitaryGroup.toLinearIsometryEquiv_apply,
    UnitaryGroup.inv_val, ← ofLp_toEuclideanCLM, WithLp.toLp_ofLp]

end Matrix

end
