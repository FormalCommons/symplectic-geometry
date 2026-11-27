/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothSingular.Integral

/-!
# Integrals over smooth simplices of forms vanishing on the image

Tau Ceti's integral `TauCeti.SmoothSimplex.integral σ φ` of a form `φ` over a smooth singular
simplex `σ` only sees the values of `φ` at points of the image of `σ`. This file records the
consequence that the integral vanishes when `φ` is zero at every point of that image
(`TauCeti.SmoothSimplex.integral_eq_zero_of_forall_eq_zero`).

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 18.
-/

public section

namespace TauCeti.SmoothSimplex

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℕ}

/-- The integral of a form over a smooth simplex vanishes if the form is zero at every point of
the image of the simplex. -/
theorem integral_eq_zero_of_forall_eq_zero (σ : SmoothSimplex I M p) {φ : RoughForm I M F p}
    (hφ : ∀ x, φ (σ.toContinuousMap x) = 0) : σ.integral φ = 0 := by
  rw [integral_def]
  refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun x hx ↦ ?_
  have h : σ.extension x = σ.toContinuousMap ⟨x, hx⟩ := σ.extension_coe ⟨x, hx⟩
  refine (mpullbackWithin_apply (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin p))) (I' := I)
    σ.extension _ φ x _).trans ?_
  rw [h, hφ, ContinuousAlternatingMap.coe_zero, Pi.zero_apply]

end TauCeti.SmoothSimplex

end
