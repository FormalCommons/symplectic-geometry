/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Determinant
public import TauCeti.Geometry.Symplectic.Complex.Line

/-!
# Real-linear maps and the area form of the complex line

Every real-linear endomorphism `A` of `ℂ` multiplies Tau Ceti's standard area form
`ω₀(z, w) = Re z Im w - Im z Re w` (`TauCeti.stdComplexSymplecticForm`) by its determinant:
`ω₀(A z, A w) = det A · ω₀(z, w)`. This generalizes Tau Ceti's
`TauCeti.stdComplexSymplecticForm_smul_sub_smul` and `TauCeti.stdComplexSymplecticForm_mul_mul`,
which treat particular maps.

## Main results

* `TauCeti.stdComplexSymplecticForm_apply_apply_eq_det_mul`: `ω₀(A z, A w) = det A · ω₀(z, w)`.
-/

public section

open Complex

namespace TauCeti

/-- A real-linear endomorphism `A` of `ℂ` multiplies the standard area form by its determinant:
`ω₀(A z, A w) = det A · ω₀(z, w)`. -/
theorem stdComplexSymplecticForm_apply_apply_eq_det_mul (A : ℂ →ₗ[ℝ] ℂ) (z w : ℂ) :
    stdComplexSymplecticForm (A z) (A w) = LinearMap.det A * stdComplexSymplecticForm z w := by
  have h (u : ℂ) : A u = u.re • A 1 + u.im • A I := by
    rw [← map_smul, ← map_smul, ← map_add]
    congr 1
    apply Complex.ext <;> simp
  rw [← LinearMap.det_toMatrix basisOneI, Matrix.det_fin_two, h z, h w]
  simp only [LinearMap.toMatrix_apply, coe_basisOneI, coe_basisOneI_repr,
    stdComplexSymplecticForm_apply]
  simp
  ring

end TauCeti

end
