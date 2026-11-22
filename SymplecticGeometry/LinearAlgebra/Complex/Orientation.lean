/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Complex.Orientation

/-!
# The standard orientation of `ℂ` and of `ℝ²`

The identification `Complex.orthonormalBasisOneI.repr : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)`,
`z ↦ (re z, im z)`, carries the standard orientation `Complex.orientation` of `ℂ` to the
orientation of the standard basis of `ℝ²`.

## Main results

* `Complex.orientation_map_orthonormalBasisOneI_repr`.
-/

public section

open Module

/-- The real basis `(1, i)` of `ℂ` goes to the standard basis of `ℝ²` under
`Complex.orthonormalBasisOneI.repr`, so this identification carries the standard orientation of
`ℂ` to that of `ℝ²`. -/
theorem Complex.orientation_map_orthonormalBasisOneI_repr :
    Complex.orientation.map (Fin 2) Complex.orthonormalBasisOneI.repr.toLinearEquiv =
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation := by
  rw [Complex.orientation, ← Basis.orientation_map]
  congr 1
  ext i : 1
  rw [← Complex.toBasis_orthonormalBasisOneI, Basis.map_apply, OrthonormalBasis.coe_toBasis]
  fin_cases i <;> ext j <;> fin_cases j <;> simp [Complex.orthonormalBasisOneI_repr_apply]

end
