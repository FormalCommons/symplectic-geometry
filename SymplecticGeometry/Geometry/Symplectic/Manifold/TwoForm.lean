/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.TwoForm

/-!
# Pull-back of a nondegenerate two-form by a map with symplectic differential

Let `ω₀` and `ω₁` be nondegenerate smooth two-forms on `M₀` and `M₁`, so that Tau Ceti's
`TauCeti.SmoothTwoForm.IsNondegenerate.symplecticFormAt` makes each tangent space a symplectic
vector space. If the differential at `x₀` of a smooth map `f : M₀ → M₁` is a linear
symplectomorphism `T_{x₀} M₀ ≃ T_{f x₀} M₁` for these forms, then `f^* ω₁` and `ω₀` have the
same value at `x₀` (`TauCeti.SmoothTwoForm.coe_mpullback_apply_eq_of_mfderiv_eq`). This is the
pointwise input of the relative Moser argument in the neighbourhood theorems: a diffeomorphism
whose derivative along a submanifold is symplectic pulls one form back to a form that agrees with
the other along the submanifold.

## Main results

* `TauCeti.SmoothTwoForm.coe_mpullback_apply_eq_of_mfderiv_eq`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.4.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm

variable {E₀ H₀ M₀ E₁ H₁ M₁ : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
  [TopologicalSpace H₀] {I₀ : ModelWithCorners ℝ E₀ H₀} [TopologicalSpace M₀]
  [ChartedSpace H₀ M₀] [IsManifold I₀ ∞ M₀] [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁} [TopologicalSpace M₁]
  [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁]

/-- Let `f : M₀ → M₁` be a smooth map with `f x₀ = x₁` whose differential at `x₀` is a linear
symplectomorphism `A : T_{x₀} M₀ ≃ T_{x₁} M₁` for the symplectic forms that nondegenerate
two-forms `ω₀` and `ω₁` give these tangent spaces. Then `f^* ω₁` and `ω₀` have the same value at
`x₀`. -/
theorem coe_mpullback_apply_eq_of_mfderiv_eq {f : M₀ → M₁} (hf : ContMDiff I₀ I₁ ∞ f)
    {ω₀ : SmoothTwoForm I₀ M₀} {ω₁ : SmoothTwoForm I₁ M₁} (hω₀ : ω₀.IsNondegenerate)
    (hω₁ : ω₁.IsNondegenerate) {x₀ : M₀} {x₁ : M₁}
    (A : TangentSpace I₀ x₀ ≃L[ℝ] TangentSpace I₁ x₁)
    (hA : (hω₀.symplecticFormAt x₀).IsSymplectomorphism (hω₁.symplecticFormAt x₁) A.toLinearEquiv)
    (hfx : f x₀ = x₁)
    (hfA : mfderiv I₀ I₁ f x₀ = (A : TangentSpace I₀ x₀ →L[ℝ] TangentSpace I₁ x₁)) :
    (SmoothForm.mpullback f hf ω₁).val x₀ = ω₀.val x₀ := by
  subst hfx
  refine SmoothBundleForm.apply_eq_of_eval₂_eq fun v w ↦ ?_
  rw [SmoothForm.eval₂_mpullback, hfA]
  simpa using hA.apply v w

end TauCeti.SmoothTwoForm

end
