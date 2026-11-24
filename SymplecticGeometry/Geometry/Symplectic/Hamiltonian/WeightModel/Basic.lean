/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Complex.Euclidean.Space
public import TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.Basic

/-!
# The weight rotation in complex coordinates

Tau Ceti's `TauCeti.weightRotation θ` rotates the `k`-th coordinate plane of
`EuclideanSpace ℝ ι × EuclideanSpace ℝ ι` by the angle `θₖ`. This file reads it in the complex
coordinates `u : ι → ℂ`, through `TauCeti.complexToRealEuclidean ι` (real and imaginary parts)
and `EuclideanSpace.sumEquivProd`: it is the coordinatewise multiplication
`uₖ ↦ exp (θₖ i) uₖ` (`TauCeti.weightRotation_sumEquivProd_complexToRealEuclidean`).
-/

public section

namespace TauCeti

/-- Read through `EuclideanSpace.sumEquivProd` and `complexToRealEuclidean`, the rotation
`weightRotation θ` of `ℂ^ι` is the multiplication `uₖ ↦ exp (θₖ i) uₖ`. -/
theorem weightRotation_sumEquivProd_complexToRealEuclidean {ι : Type*} [Fintype ι]
    (θ : ι → ℝ) (u : ι → ℂ) :
    weightRotation θ (EuclideanSpace.sumEquivProd (complexToRealEuclidean ι u)) =
      EuclideanSpace.sumEquivProd
        (complexToRealEuclidean ι fun k ↦ Complex.exp (θ k * Complex.I) * u k) := by
  ext k <;> simp [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  ring

end TauCeti

end
