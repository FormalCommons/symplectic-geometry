/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
import SymplecticGeometry.Geometry.Manifold.ContMDiff.MFDeriv
import SymplecticGeometry.Geometry.Manifold.ContMDiff.Opens
import TauCeti.Geometry.Manifold.ContMDiff.ContinuousAlternatingMap
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# The derivative in the parameter of a smooth family of forms

Let `F` be a manifold and let `β p` be a `k`-form on `F` for each point `p` of a parameter
manifold `P`, such that `(p, y) ↦ β p y` is a `C^n` section of the bundle of `k`-forms of `F`
along the projection `(p, y) ↦ y` (the form in which Tau Ceti's
`TauCeti.contMDiff_mpullback_prodMk_form` gives the slices of a form on a product).

* `TauCeti.ContMDiffAt.roughForm_family_apply_trivializationAt`: the values of `β p y` on the
  frame `e.symmL y ∘ v` of the tangent trivialization `e` of `F` at `y₀`, for a fixed tuple `v`
  of model vectors, are `C^n` in `(p, y)` at each point over `y₀`. This is the family version of
  one direction of Tau Ceti's `TauCeti.isSmoothForm_iff_forall_contMDiffAt_trivializationAt_apply`.
* `TauCeti.isSmoothForm_mfderiv_family_apply`: when `P` is an open subset `U` of a normed space
  `EB`, with the model `𝓘(ℝ, EB)`, and the family is smooth, then for `b ∈ U` and `a ∈ EB` the
  `k`-form whose value at `y` is the derivative at `b`, in the direction `a`, of `b' ↦ β b' y` is
  smooth. In the frames above, its values are the partial derivatives in the parameter of the
  functions of the first point, extended by `0` outside `U`
  (`ContMDiffAt.opens_prod_of_eq`), and these are smooth in `y` by `ContMDiffAt.fderiv_left`.
  No orientation, metric or countability of `F` is needed, and the degree `k` is arbitrary.

This is the smoothness in the base of the integrand of the fibre integral over a product, as in
Bott–Tu, §6.

## References

* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §6 (integration
  along the fibre).
-/

public section

noncomputable section

open Bundle Set Function TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti

variable {EP HP P : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {K : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]
  {E H F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {J : ModelWithCorners ℝ E H} [TopologicalSpace F] [ChartedSpace H F]
  {k : ℕ}

/-- **A smooth family of forms read in a tangent trivialization.** Let `β p` be a `k`-form on
`F` for each `p : P`, such that `(p, y) ↦ β p y`, as a section of the bundle of `k`-forms along
`(p, y) ↦ y`, is `C^n` at `q₀`. For each tuple `v` of model vectors, the value of `β p y` on the
frame `e.symmL y ∘ v`, where `e` is the tangent trivialization of `F` at `q₀.2`, is `C^n` in
`(p, y)` at `q₀`. -/
theorem ContMDiffAt.roughForm_family_apply_trivializationAt [IsManifold J 1 F] {n : WithTop ℕ∞}
    {β : P → RoughForm J F ℝ k} {q₀ : P × F}
    (hβ : ContMDiffAt (K.prod J) (J.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ)) n
      (fun q : P × F ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] ℝ)
        (E := fun y : F ↦ TangentSpace J y [⋀^Fin k]→L[ℝ] Trivial F ℝ y) q.2 (β q.1 q.2)) q₀)
    (v : Fin k → E) :
    ContMDiffAt (K.prod J) 𝓘(ℝ) n
      (fun q : P × F ↦ β q.1 q.2 ((trivializationAt E (TangentSpace J) q₀.2).symmL ℝ q.2 ∘ v))
      q₀ := by
  have h := (contMDiffAt_totalSpace_iff.1 hβ).2
  simp only [FiberBundle.trivializationAt_continuousAlternatingMap_apply_snd,
    contMDiffAt_continuousAlternatingMap_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply] at h
  exact h v

variable [IsManifold J ∞ F] {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {U : Opens EB}

/-- **The derivative in the parameter of a smooth family of forms is a smooth form.** Let `β b`
be a `k`-form on a manifold `F` for each `b` in an open subset `U` of a normed space `EB`, such
that `(b, y) ↦ β b y` is a smooth section of the bundle of `k`-forms along `(b, y) ↦ y`. For
`b ∈ U` and `a ∈ EB`, the `k`-form on `F` whose value at `y` is the derivative at `b`, in the
direction `a`, of `b' ↦ β b' y` is smooth. -/
theorem isSmoothForm_mfderiv_family_apply {β : U → RoughForm J F ℝ k}
    (hβ : ContMDiff (𝓘(ℝ, EB).prod J) (J.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ)) ∞
      (fun q : U × F ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] ℝ)
        (E := fun y : F ↦ TangentSpace J y [⋀^Fin k]→L[ℝ] Trivial F ℝ y) q.2 (β q.1 q.2)))
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
    have hs : ContMDiffAt 𝓘(ℝ, EB) 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ) ∞ (B · y) b := by
      refine contMDiffAt_continuousAlternatingMap_apply.2 fun w ↦ ?_
      have hw : (trivializationAt E (TangentSpace J) y).symmL ℝ y ∘
          ((trivializationAt E (TangentSpace J) y).continuousLinearMapAt ℝ y ∘ w) = w :=
        funext fun i ↦ Trivialization.symmL_continuousLinearMapAt (R := ℝ)
          (trivializationAt E (TangentSpace J) y) (mem_baseSet_trivializationAt E _ y) (w i)
      have h := (hBv y ((trivializationAt E (TangentSpace J) y).continuousLinearMapAt ℝ y ∘ w)).comp
        (b : EB) (contMDiffAt_id.prodMk contMDiffAt_const)
      rw [← hw]
      exact h
    exact (contMDiffAt_iff_contDiffAt.1 hs).differentiableAt (by simp)
  -- The derivative of the family is that of the extended family on `EB`.
  have hD (y : F) : (show E [⋀^Fin k]→L[ℝ] ℝ from mfderiv 𝓘(ℝ, EB) 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ)
      (fun b' : U ↦ show E [⋀^Fin k]→L[ℝ] ℝ from β b' y) b a) = fderiv ℝ (B · y) b a := by
    have heq : (fun b' : U ↦ show E [⋀^Fin k]→L[ℝ] ℝ from β b' y) = (B · y) ∘ Subtype.val :=
      funext fun b' ↦ (hB b' y).symm
    dsimp only at heq ⊢
    rw [heq]
    refine (Manifold.mfderiv_comp_subtype_val_apply (J := 𝓘(ℝ, EB)) (U := U)
      (I := 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ)) (f := (B · y)) (x := b) a).trans ?_
    rw [(hdiff y).hasFDerivAt.hasMFDerivAt.mfderiv]
    -- The two sides agree up to the identification of `TangentSpace 𝓘(ℝ, EB) b` with `EB`,
    -- which holds by definition; no lemma states it for these applications.
    rfl
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

end TauCeti

end
