/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.Opens

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

A linear symplectomorphism between ambient tangent spaces is also one between the tangent spaces
of open subsets `U₀ ⊆ M₀` and `U₁ ⊆ M₁` for the restricted forms
(`TauCeti.SmoothTwoForm.IsNondegenerate.isSymplectomorphism_mpullback_subtype_val`), since
restriction does not change the values of the forms. Together, these give the same conclusion
for maps between open subsets.

A map that pulls `ω₁` back to a form `ω₀` at a point where `ω₀` is nondegenerate, with no
assumption on `ω₁`, is an immersion there
(`TauCeti.SmoothTwoForm.injective_mfderiv_of_mpullback_apply_eq`): a vector in the kernel of its
differential pairs to zero under `ω₀` with every vector. The proof is that of Tau Ceti's
`TauCeti.SmoothTwoForm.IsNondegenerate.injective_mvfderiv`, for maps into a manifold rather than
a vector space.

## Main results

* `TauCeti.SmoothTwoForm.coe_mpullback_apply_eq_of_mfderiv_eq`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.isSymplectomorphism_mpullback_subtype_val`.
* `TauCeti.SmoothTwoForm.injective_mfderiv_of_mpullback_apply_eq`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.symplecticFormAt_mfderiv_mfderiv`: the symplectic form
  of `ω₁` at `f x₀` on two differentials of `f` is the pull-back `f^* ω₁` at `x₀`.
* `TauCeti.SmoothTwoForm.nondegenerate_bilinFormAt_mpullback_iff`: through a map whose
  differential at `x₀` is invertible, `f^* ω₁` is nondegenerate at `x₀` exactly when `ω₁` is
  nondegenerate at `f x₀`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.4.
-/

public section

open TopologicalSpace
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

/-- Let `U₀ ⊆ M₀` and `U₁ ⊆ M₁` be open, `x₀ ∈ U₀` and `x₁ ∈ U₁`. A linear map
`A : T_{x₀} M₀ ≃ T_{x₁} M₁` that is a symplectomorphism for the forms that nondegenerate two-forms
`ω₀` and `ω₁` give these tangent spaces is also a symplectomorphism `T_{x₀} U₀ ≃ T_{x₁} U₁` for
the restrictions of `ω₀` to `U₀` and of `ω₁` to `U₁`. The point `x₁` is given in `M₁` as `y₁`,
up to the equality `hx₁`. -/
theorem IsNondegenerate.isSymplectomorphism_mpullback_subtype_val
    {ω₀ : SmoothTwoForm I₀ M₀} {ω₁ : SmoothTwoForm I₁ M₁} (hω₀ : ω₀.IsNondegenerate)
    (hω₁ : ω₁.IsNondegenerate) {U₀ : Opens M₀} {U₁ : Opens M₁} {x₀ : U₀} {x₁ : U₁} {y₁ : M₁}
    (hx₁ : (x₁ : M₁) = y₁) (A : TangentSpace I₀ (x₀ : M₀) ≃L[ℝ] TangentSpace I₁ y₁)
    (hA : (hω₀.symplecticFormAt (x₀ : M₀)).IsSymplectomorphism (hω₁.symplecticFormAt y₁)
      A.toLinearEquiv) :
    ((hω₀.mpullback_subtype_val U₀).symplecticFormAt x₀).IsSymplectomorphism
      ((hω₁.mpullback_subtype_val U₁).symplecticFormAt x₁) A.toLinearEquiv := by
  subst hx₁
  have h := ((SymplecticForm.isSymplectomorphism_iff_transport_eq.2
    (hω₀.symplecticFormAt_mpullback_subtype_val_transport x₀)).trans hA).trans
    (SymplecticForm.isSymplectomorphism_iff_transport_eq.2
      (hω₁.symplecticFormAt_mpullback_subtype_val_transport x₁)).symm
  -- The identifications of the tangent spaces of `U₀` and `U₁` with those of `M₀` and `M₁`
  -- cancel around `A`.
  have e : (Manifold.tangentSpaceOpenEquiv (I := I₀) x₀).toLinearEquiv ≪≫ₗ A.toLinearEquiv ≪≫ₗ
      (Manifold.tangentSpaceOpenEquiv (I := I₁) x₁).toLinearEquiv.symm =
      (A.toLinearEquiv : TangentSpace I₀ x₀ ≃ₗ[ℝ] TangentSpace I₁ x₁) := by
    ext v
    simp only [LinearEquiv.trans_apply, ContinuousLinearEquiv.coe_toLinearEquiv,
      ContinuousLinearEquiv.coe_symm_toLinearEquiv, Manifold.tangentSpaceOpenEquiv_apply,
      Manifold.tangentSpaceOpenEquiv_symm_apply]
    -- Both sides apply `A` to `v`. The right side reads `A` between the tangent spaces of `U₀`
    -- and `U₁`, so `ContinuousLinearEquiv.coe_toLinearEquiv` does not match it syntactically.
    rfl
  rwa [e] at h

/-- A map `f : M₀ → M₁` that pulls `ω₁` back to `ω₀` at a point `x₀` where `ω₀` is nondegenerate
has injective differential at `x₀`. -/
theorem injective_mfderiv_of_mpullback_apply_eq {ω₀ : SmoothTwoForm I₀ M₀}
    {ω₁ : SmoothTwoForm I₁ M₁} {f : M₀ → M₁} {x₀ : M₀} (hω₀ : (ω₀.bilinFormAt x₀).Nondegenerate)
    (h : mpullback I₀ I₁ f ω₁.val x₀ = ω₀.val x₀) : Function.Injective (mfderiv I₀ I₁ f x₀) := by
  refine (injective_iff_map_eq_zero (mfderiv I₀ I₁ f x₀)).2 fun v hv ↦ hω₀.1 v fun w ↦ ?_
  rw [SmoothForm.bilinFormAt_apply, SmoothBundleForm.eval₂_apply, ← h, mpullback_apply]
  exact (ω₁.val (f x₀)).map_coord_zero 0 (by simp [hv])

/-- For a smooth map `f : M₀ → M₁` and a nondegenerate two-form `ω₁` on `M₁`, the symplectic
form of `ω₁` at `f x₀` on the differentials `df_{x₀} v` and `df_{x₀} w` is the pull-back
`(f^* ω₁)_{x₀}` on `v` and `w`. -/
theorem IsNondegenerate.symplecticFormAt_mfderiv_mfderiv {ω₁ : SmoothTwoForm I₁ M₁}
    (hω₁ : ω₁.IsNondegenerate) {f : M₀ → M₁} (hf : ContMDiff I₀ I₁ ∞ f) (x₀ : M₀)
    (v w : TangentSpace I₀ x₀) :
    hω₁.symplecticFormAt (f x₀) (mfderiv I₀ I₁ f x₀ v) (mfderiv I₀ I₁ f x₀ w) =
      (SmoothForm.mpullback f hf ω₁).bilinFormAt x₀ v w := by
  rw [IsNondegenerate.symplecticFormAt_apply, SmoothForm.bilinFormAt_apply,
    SmoothForm.eval₂_mpullback]

/-- If the differential of a smooth map `f : M₀ → M₁` at `x₀` is invertible, then the pull-back
`f^* ω₁` is nondegenerate at `x₀` exactly when `ω₁` is nondegenerate at `f x₀`. The point `x₀`
may lie on the boundary of `M₀`, where `f` need not be a local diffeomorphism. -/
theorem nondegenerate_bilinFormAt_mpullback_iff {f : M₀ → M₁} (hf : ContMDiff I₀ I₁ ∞ f)
    (ω₁ : SmoothTwoForm I₁ M₁) {x₀ : M₀} (hdf : (mfderiv I₀ I₁ f x₀).IsInvertible) :
    ((SmoothForm.mpullback f hf ω₁).bilinFormAt x₀).Nondegenerate ↔
      (ω₁.bilinFormAt (f x₀)).Nondegenerate := by
  obtain ⟨e, he⟩ := hdf
  have h : (SmoothForm.mpullback f hf ω₁).bilinFormAt x₀ =
      LinearMap.BilinForm.congr e.symm.toLinearEquiv (ω₁.bilinFormAt (f x₀)) := by
    refine LinearMap.ext₂ fun v w ↦ ?_
    rw [LinearMap.BilinForm.congr_apply, ContinuousLinearEquiv.coe_symm_toLinearEquiv,
      ContinuousLinearEquiv.symm_symm, SmoothForm.bilinFormAt_apply, SmoothForm.bilinFormAt_apply,
      SmoothForm.eval₂_mpullback, ← he]
    simp only [ContinuousLinearEquiv.coe_coe]
  rw [h, LinearMap.BilinForm.nondegenerate_congr_iff]

end TauCeti.SmoothTwoForm

end
