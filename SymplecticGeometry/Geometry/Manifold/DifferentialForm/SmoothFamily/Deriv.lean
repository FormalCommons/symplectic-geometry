/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Slice
import SymplecticGeometry.Geometry.Manifold.ContMDiff.MFDeriv
import SymplecticGeometry.Geometry.Manifold.ContMDiff.Opens
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Opens

/-!
# The derivative in the parameter of a smooth family of forms

Let `F` be a manifold and let `β b` be a `k`-form on `F` for each point `b` of an open subset `U`
of a normed space `EB`, with the model `𝓘(ℝ, EB)`, such that `(b, y) ↦ β b y` is a smooth section
of the bundle of `k`-forms of `F` along the projection `(b, y) ↦ y`.

* `ContMDiff.isSmoothForm_mfderiv_family_apply`: for `b ∈ U` and `a ∈ EB` the
  `k`-form whose value at `y` is the derivative at `b`, in the direction `a`, of `b' ↦ β b' y` is
  smooth. In the frames of the tangent trivializations of `F`, its values are the partial
  derivatives in the parameter of the functions of
  `ContMDiffAt.roughForm_family_apply_trivializationAt` (`SmoothFamily/Slice.lean`), extended by
  `0` outside `U` (`ContMDiffAt.opens_prod_of_eq`), and these are smooth in `y` by
  `ContMDiffAt.fderiv_left`. No orientation, metric or countability of `F` is needed, and the
  degree `k` is arbitrary.

This is the smoothness in the base of the integrand of the fibre integral over a product, as in
Bott–Tu, §6.

The lemma is a statement about a `ContMDiff` hypothesis, so it sits in the namespace `ContMDiff`,
where dot notation finds it, as the lemmas of `SmoothFamily/Slice.lean` sit in `ContMDiffAt`.

## References

* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §6 (integration
  along the fibre).
-/

public section

noncomputable section

open Bundle Set Function TopologicalSpace
open scoped ContDiff Manifold

namespace ContMDiff

open TauCeti SymplecticGeometry

variable {E H F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {J : ModelWithCorners ℝ E H} [TopologicalSpace F] [ChartedSpace H F]
  [IsManifold J ∞ F] {k : ℕ} {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {U : Opens EB}

/-- **The derivative in the parameter of a smooth family of forms is a smooth form.** Let `β b`
be a `k`-form on a manifold `F` for each `b` in an open subset `U` of a normed space `EB`, such
that `(b, y) ↦ β b y` is a smooth section of the bundle of `k`-forms along `(b, y) ↦ y`. For
`b ∈ U` and `a ∈ EB`, the `k`-form on `F` whose value at `y` is the derivative at `b`, in the
direction `a`, of `b' ↦ β b' y` is smooth. -/
theorem isSmoothForm_mfderiv_family_apply {β : U → RoughForm J F ℝ k}
    (hβ : ContMDiff (𝓘(ℝ, EB).prod J) (J.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ)) ∞ (sliceSection β))
    (b : U) (a : EB) :
    IsSmoothForm J ∞ (fun y ↦ show E [⋀^Fin k]→L[ℝ] ℝ from
      mfderiv 𝓘(ℝ, EB) 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ)
        (fun b' : U ↦ show E [⋀^Fin k]→L[ℝ] ℝ from β b' y) b a) := by
  classical
  -- The family extended by `0` outside `U`, as a function of `EB × F` into one normed space.
  let B : EB → F → E [⋀^Fin k]→L[ℝ] ℝ := fun z y ↦ if h : z ∈ U then β ⟨z, h⟩ y else 0
  have hB (b' : U) (y : F) : B b' y = β b' y := dite_eq_left b'.property
  -- Its values on a frame of a tangent trivialization are jointly smooth.
  have hBv (y₀ : F) (v : Fin k → E) : ContMDiffAt (𝓘(ℝ, EB).prod J) 𝓘(ℝ) ∞
      (uncurry fun z y ↦ B z y ((trivializationAt E (TangentSpace J) y₀).symmL ℝ y ∘ v))
      ((b : EB), y₀) :=
    (ContMDiffAt.roughForm_family_apply_trivializationAt (hβ (b, y₀)) v).opens_prod_of_eq
      fun z hz y ↦ congrArg (fun φ : E [⋀^Fin k]→L[ℝ] ℝ ↦ φ _) (hB ⟨z, hz⟩ y)
  -- At each `y`, the extended family is differentiable in the parameter at `b`.
  have hdiff (y : F) : DifferentiableAt ℝ (B · y) b := by
    have hs : ContMDiffAt 𝓘(ℝ, EB) 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ) ∞ (B · y) b :=
      contMDiffAt_subtype_iff.1 <| (ContMDiffAt.roughForm_family_apply (q₀ := (b, y))
        (hβ (b, y))).congr_of_eventuallyEq (Filter.Eventually.of_forall fun b' ↦ hB b' y)
    exact (contMDiffAt_iff_contDiffAt.1 hs).differentiableAt (by simp)
  -- The derivative of the family is that of the extended family on `EB`.
  have hD (y : F) : (show E [⋀^Fin k]→L[ℝ] ℝ from mfderiv 𝓘(ℝ, EB) 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ)
      (fun b' : U ↦ show E [⋀^Fin k]→L[ℝ] ℝ from β b' y) b a) = fderiv ℝ (B · y) b a := by
    have heq : (fun b' : U ↦ show E [⋀^Fin k]→L[ℝ] ℝ from β b' y) = (B · y) ∘ Subtype.val :=
      funext fun b' ↦ (hB b' y).symm
    dsimp only at heq ⊢
    rw [heq]
    exact mfderiv_modelSpace_comp_subtypeVal_apply a
  refine isSmoothForm_iff_forall_contMDiffAt_trivializationAt_apply.2 fun y₀ v ↦ ?_
  -- In the frame of the trivialization at `y₀`, the form is the partial derivative in the
  -- parameter of the function of `hBv y₀ v`.
  have hval (y : F) : (show E [⋀^Fin k]→L[ℝ] ℝ from mfderiv 𝓘(ℝ, EB) 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ)
      (fun b' : U ↦ show E [⋀^Fin k]→L[ℝ] ℝ from β b' y) b a)
        ((trivializationAt E (TangentSpace J) y₀).symmL ℝ y ∘ v) =
      fderiv ℝ (fun z ↦ B z y ((trivializationAt E (TangentSpace J) y₀).symmL ℝ y ∘ v)) b a := by
    rw [hD]
    exact (fderiv_continuousAlternatingMap_apply_const_apply (hdiff y) _ a).symm
  exact ((((hBv y₀ v).fderiv_left (n := ∞) (by simp)).comp y₀
    (contMDiffAt_const.prodMk contMDiffAt_id)).clm_apply (contMDiffAt_const (c := a)))
    |>.congr_of_eventuallyEq (Filter.Eventually.of_forall hval)

end ContMDiff

end
