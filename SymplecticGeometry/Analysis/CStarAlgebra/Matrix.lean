/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Matrices of continuous endomorphisms of a Euclidean space

Mathlib identifies the matrices over `𝕜` with the linear endomorphisms of
`EuclideanSpace 𝕜 n` by `Matrix.toEuclideanLin`, and with its continuous endomorphisms by
`Matrix.toEuclideanCLM`. This file shows that the two give the same matrix of a linear
endomorphism, made continuous by `LinearMap.toContinuousLinearMap`.

## Main results

* `Matrix.toEuclideanCLM_symm_toContinuousLinearMap`: the matrix of a linear endomorphism of
  `EuclideanSpace 𝕜 n` is the same through `Matrix.toEuclideanCLM` and `Matrix.toEuclideanLin`.
-/

public section

namespace Matrix

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- The matrix of a linear endomorphism of `EuclideanSpace 𝕜 n`, read through
`Matrix.toEuclideanCLM` after making it continuous, is its matrix through
`Matrix.toEuclideanLin`. -/
theorem toEuclideanCLM_symm_toContinuousLinearMap
    (f : EuclideanSpace 𝕜 n →ₗ[𝕜] EuclideanSpace 𝕜 n) :
    (toEuclideanCLM (n := n) (𝕜 := 𝕜)).symm (LinearMap.toContinuousLinearMap f) =
      toEuclideanLin.symm f := by
  rw [LinearEquiv.eq_symm_apply, ← coe_toEuclideanCLM_eq_toEuclideanLin,
    StarAlgEquiv.apply_symm_apply, LinearMap.coe_toContinuousLinearMap]

end Matrix

end
