/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import TauCeti.Geometry.Symplectic.Complex.Line
import TauCeti.LinearAlgebra.Complex.Determinant

/-!
# Real-linear maps and the area form of the complex line

A real-linear endomorphism `A` of `ℂ` multiplies Tau Ceti's standard area form
`ω₀(z, w) = Re z Im w - Im z Re w` (`TauCeti.stdComplexSymplecticForm`) by its determinant:
`ω₀(A z, A w) = det A · ω₀(z, w)`. Tau Ceti proves this for particular maps, in
`TauCeti.stdComplexSymplecticForm_smul_sub_smul`, `TauCeti.stdComplexSymplecticForm_mul_mul`
and `TauCeti.Beltrami.area_linearMap`. The proof expands `z` and `w` in the basis `1, I` and
uses Tau Ceti's formula `LinearMap.det_complex` for `det A`.

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
  rw [LinearMap.det_complex, h z, h w]
  simp [stdComplexSymplecticForm_apply]
  ring

end TauCeti

end
