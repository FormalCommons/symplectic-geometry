/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Complex.Euclidean.Space
public import TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.Basic
public import TauCeti.Geometry.Symplectic.StandardCompatible

/-!
# The weight rotation in complex coordinates

Tau Ceti's `TauCeti.weightRotation θ` rotates the `k`-th coordinate plane of
`EuclideanSpace ℝ ι × EuclideanSpace ℝ ι` by the angle `θₖ`. This file reads it in the complex
coordinates `u : ι → ℂ`, through `TauCeti.complexToRealEuclidean ι` (real and imaginary parts)
and `EuclideanSpace.sumEquivProd`: it is the coordinatewise multiplication
`uₖ ↦ exp (θₖ i) uₖ` (`TauCeti.weightRotation_sumEquivProd_complexToRealEuclidean`).

It also computes the standard symplectic form of these coordinates on vectors with disjoint
supports: `TauCeti.stdSymplecticForm_eq_zero_of_forall`.
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

/-- The standard symplectic form of `ℂ^ι = ℝ^ι × ℝ^ι` vanishes on two vectors that have, at each
index, one of them with both coordinates zero. -/
theorem stdSymplecticForm_eq_zero_of_forall {ι : Type*} [Fintype ι]
    {v w : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι}
    (h : ∀ k, v.1 k = 0 ∧ v.2 k = 0 ∨ w.1 k = 0 ∧ w.2 k = 0) : stdSymplecticForm v w = 0 := by
  rw [stdSymplecticForm_apply, PiLp.inner_apply, PiLp.inner_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  rcases h k with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]

end TauCeti

end
