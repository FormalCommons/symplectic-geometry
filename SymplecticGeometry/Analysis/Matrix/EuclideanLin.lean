/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Matrix.EuclideanLin

/-!
# The linear equivalence of an invertible matrix

Tau Ceti's `Matrix.toEuclideanCLE A hA` is the continuous linear automorphism of
`EuclideanSpace 𝕜 ι` given by a matrix `A` with `A.det ≠ 0`, and `Matrix.coe_toEuclideanCLE`
identifies its underlying continuous linear map. This file gives the same identification for the
underlying linear equivalence, read as a linear map.

## Main results

* `Matrix.coe_toLinearEquiv_toEuclideanCLE`: the linear map underlying
  `(A.toEuclideanCLE hA).toLinearEquiv` is `Matrix.toEuclideanLin A`.
-/

public section

namespace Matrix

variable {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕜]

/-- The linear map underlying the linear equivalence of an invertible matrix `A` is the action
`Matrix.toEuclideanLin A` of `A` on `EuclideanSpace 𝕜 ι`. -/
@[simp]
theorem coe_toLinearEquiv_toEuclideanCLE (A : Matrix ι ι 𝕜) (hA : A.det ≠ 0) :
    ((A.toEuclideanCLE hA).toLinearEquiv : EuclideanSpace 𝕜 ι →ₗ[𝕜] EuclideanSpace 𝕜 ι) =
      A.toEuclideanLin :=
  LinearMap.ext (toEuclideanCLE_apply A hA)

end Matrix

end
