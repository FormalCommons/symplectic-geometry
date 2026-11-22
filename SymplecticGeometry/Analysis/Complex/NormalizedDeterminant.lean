/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Complex.NormalizedDeterminant

/-!
# The normalized determinant of a scalar automorphism

A fact about Tau Ceti's `ContinuousLinearEquiv.normalizedDet`: an automorphism of a
finite-dimensional complex space that acts as multiplication by a point `z` of the unit circle
has normalized determinant `z ^ n`, where `n` is the dimension.

## Main results

* `ContinuousLinearEquiv.normalizedDet_eq_pow_of_apply_eq_smul`: if `A v = z • v` for all `v`,
  then `normalizedDet A = z ^ finrank ℂ E`.
-/

public section

namespace ContinuousLinearEquiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- An automorphism that is multiplication by a point `z` of the unit circle has normalized
determinant `z ^ n`, where `n` is the complex dimension. -/
theorem normalizedDet_eq_pow_of_apply_eq_smul [FiniteDimensional ℂ E] (A : E ≃L[ℂ] E)
    (z : Circle) (h : ∀ v, A v = (z : ℂ) • v) :
    A.normalizedDet = z ^ Module.finrank ℂ E := by
  have hA : (A.toLinearEquiv : E →ₗ[ℂ] E) = (z : ℂ) • LinearMap.id := LinearMap.ext h
  ext
  simp [hA, LinearMap.det_smul]

end ContinuousLinearEquiv

end
