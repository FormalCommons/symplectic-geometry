/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Fibration.LocalForm
import SymplecticGeometry.Geometry.Manifold.DeRham.FamilyPrimitive
import SymplecticGeometry.Geometry.Manifold.ContMDiff.Opens
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Interior
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Prod

/-!
# Closed forms over a patch with given fibre and mixed components

Let `τ` be a smooth two-form on `EB × F`, in the setting of `Fibration/LocalForm.lean`: `EB` is a
real Banach space with a basis `bs`, and `τ` has the mixed components `αᵢ(x)` and the base
components `f_{ij}(x)`, families of one-forms and functions on `F` indexed by `x ∈ EB`. This file
prepares the construction of a closed two-form over a patch `U ×ˢ univ` of `EB × F` with the same
fibre and mixed components as `τ`, the local step of the existence of the coupling form of a
symplectic connection with Hamiltonian curvature ([McDuffSalamon2017], §6.4, proof of
Theorem 6.4.1).

The result here chooses primitives of the curls `∂ᵢαⱼ(x) - ∂ⱼαᵢ(x)` of the mixed components
smoothly in `x`, where `∂ᵢ` differentiates along `bs i`. If, at every `x` of an open
set `U`, the curl is the differential of a smooth function on `F`, then there is a function `f`
on `EB × F`, smooth on `U ×ˢ univ` and vanishing on `U × {y₀}`, whose restriction to each fibre
over `x ∈ U` is such a primitive
(`TauCeti.SmoothTwoForm.exists_contMDiffOn_mvfderiv_eq_fderiv_mixedComponent_sub`).

## Main results

* `TauCeti.SmoothTwoForm.exists_contMDiffOn_mvfderiv_eq_fderiv_mixedComponent_sub`: jointly
  smooth primitives of the curls over an open patch, normalized at a point `y₀` of `F`.

## Implementation notes

By the formula for the curl in `Fibration/LocalForm.lean`
(`TauCeti.SmoothTwoForm.fderiv_mixedComponent_sub_fderiv_mixedComponent`), the curl at `x` is
`d_F f_{ij}(x)` minus the slice over `x` of the smooth one-form `η = ι(∂ⱼ, 0) ι(∂ᵢ, 0) dτ` on
`EB × F`. If the curl at `x` is exact, then so is that slice.
The slices of `η` over the patch, the subtype of `U` as an open subset of `EB`, form a smooth
family of exact one-forms on `F`, so the library's
`SymplecticGeometry.exists_contMDiff_mextDeriv_eq_of_forall_mem_exactForms` gives them jointly
smooth primitives `h`. Then `f_{ij} - h`, extended by zero off the patch, has the curls as fibre
differentials, and subtracting its values at `y₀` normalizes it. Smoothness on `U ×ˢ univ` comes
from that of `h` on `U × F` by `ContMDiff.contMDiffOn_opens_prod_of_eq`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §6.4 (proof of Theorem 6.4.1), with [McDuffSalamon2019Errata].
-/

public section

noncomputable section

open Set
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {EF HF F : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] [TopologicalSpace HF]
  {IF : ModelWithCorners ℝ EF HF} [TopologicalSpace F] [ChartedSpace HF F] [IsManifold IF ∞ F]
  {ι : Type*} (τ : SmoothTwoForm (𝓘(ℝ, EB).prod IF) (EB × F)) (bs : Module.Basis ι ℝ EB)

open SymplecticGeometry in
/-- The slices of the one-form `ι(bs j, 0) ι(bs i, 0) dτ` on `EB × F`: on a vector `w` tangent
to `F`, the slice over `x` takes the value of `dτ` on `(bs i, 0), (bs j, 0), (0, w)`. -/
private theorem exists_mpullback_prodMk_apply_eq_mextDeriv (i j : ι) :
    ∃ η : SmoothForm (𝓘(ℝ, EB).prod IF) (EB × F) ℝ 1, ∀ (x : EB) (y : F) (w : TangentSpace IF y),
      (SmoothForm.mpullback (Prod.mk x) (contMDiff_const.prodMk contMDiff_id) η).val y ![w] =
        mextDeriv τ.val (x, y) ![(bs i, 0), (bs j, 0), ((0 : EB), w)] := by
  refine ⟨SmoothForm.interiorProduct (baseField bs j)
    (SmoothForm.interiorProduct (baseField bs i) (mextDerivₗ _ 2 τ)), fun x y w ↦ ?_⟩
  rw [SmoothForm.mpullback_apply_one, mfderiv_prodMk_right_apply, SmoothForm.coe_interiorProduct,
    RoughForm.interior_apply, SmoothForm.coe_interiorProduct, RoughForm.interior_apply,
    mextDerivₗ_apply, baseField_apply, baseField_apply]
  -- The vector `(0, w)` lies in the tangent space of `EB × F`, which is `EB × EF` by definition.
  rfl

variable [CompleteSpace EB] [CompleteSpace EF]

/-- **Smooth primitives of the curls of the mixed components.** Let `τ` be a smooth two-form on
`EB × F` with mixed components `αₖ` for the basis `bs`, and `U` an open set of `EB`. If, at every
`x ∈ U`, the one-form `∂ᵢαⱼ(x) - ∂ⱼαᵢ(x)` on `F` is the differential of a smooth function, then
for every `y₀ : F` there is a function `f` on `EB × F`, smooth on `U ×ˢ univ`, with
`f (x, y₀) = 0` for `x ∈ U`, whose restriction to the fibre over each `x ∈ U` has differential
`∂ᵢαⱼ(x) - ∂ⱼαᵢ(x)`. Here `∂ₖ` differentiates in `x` along `bs k`. -/
theorem exists_contMDiffOn_mvfderiv_eq_fderiv_mixedComponent_sub {U : Set EB} (hU : IsOpen U)
    {i j : ι}
    (h : ∀ x ∈ U, ∃ g : F → ℝ, ContMDiff IF 𝓘(ℝ) ∞ g ∧ ∀ (y : F) (w : TangentSpace IF y),
      mvfderiv IF g y w =
        fderiv ℝ (fun x' ↦ RoughForm.mixedComponent τ.val bs j x' y ![w]) x (bs i) -
          fderiv ℝ (fun x' ↦ RoughForm.mixedComponent τ.val bs i x' y ![w]) x (bs j))
    (y₀ : F) :
    ∃ f : EB × F → ℝ, ContMDiffOn (𝓘(ℝ, EB).prod IF) 𝓘(ℝ) ∞ f (U ×ˢ univ) ∧
      (∀ x ∈ U, f (x, y₀) = 0) ∧ ∀ x ∈ U, ∀ (y : F) (w : TangentSpace IF y),
        mvfderiv IF (fun y ↦ f (x, y)) y w =
          fderiv ℝ (fun x' ↦ RoughForm.mixedComponent τ.val bs j x' y ![w]) x (bs i) -
            fderiv ℝ (fun x' ↦ RoughForm.mixedComponent τ.val bs i x' y ![w]) x (bs j) := by
  classical
  let V : TopologicalSpace.Opens EB := ⟨U, hU⟩
  obtain ⟨η, hη⟩ := exists_mpullback_prodMk_apply_eq_mextDeriv τ bs i j
  -- The slices of `η` over the patch form a smooth family of one-forms on `F`.
  let α : V → SmoothForm IF F ℝ 1 := fun t ↦
    SmoothForm.mpullback (Prod.mk (t : EB)) (contMDiff_const.prodMk contMDiff_id) η
  have hα : SymplecticGeometry.IsSmoothFamily 𝓘(ℝ, EB) α :=
    (SymplecticGeometry.isSmoothFamily_mpullback_prodMk η).comp _ contMDiff_subtypeVal
  have hf := contMDiff_baseComponent τ bs i j
  have hfx (x : EB) : ContMDiff IF 𝓘(ℝ) ∞ (RoughForm.baseComponent τ.val bs i j x) :=
    hf.comp (contMDiff_const.prodMk contMDiff_id)
  -- Each `α t` is the differential of `f_{ij}(t) - g` for a primitive `g` of the curl at `t`.
  have hex (t : V) : α t ∈ exactForms IF F 1 := by
    obtain ⟨g, hg, hdg⟩ := h t t.property
    rw [exactForms_succ, LinearMap.mem_range]
    refine ⟨⟨RoughForm.ofFunction IF _,
      (isSmoothForm_ofFunction_iff.2 ((hfx t).sub hg)).mem_smoothBundleForms⟩, Subtype.ext ?_⟩
    rw [mextDerivₗ_apply]
    funext y
    rw [mextDeriv_ofFunction]
    ext v
    rw [ContinuousAlternatingMap.ofSubsingleton_apply_apply, show v = ![v 0] from
      funext fun k ↦ by fin_cases k; rfl, hη, mvfderiv_fun_sub
      ((hfx t).mdifferentiableAt (by simp)) (hg.mdifferentiableAt (by simp)), sub_apply, hdg,
      fderiv_mixedComponent_sub_fderiv_mixedComponent]
    abel
  obtain ⟨h₀, hh₀, hdh₀⟩ :=
    SymplecticGeometry.exists_contMDiff_mextDeriv_eq_of_forall_mem_exactForms hα hex
  -- The primitives `h₀ (t, ·)` of the `α t`, extended by zero off the patch.
  let H : EB × F → ℝ := fun p ↦ if hp : p.1 ∈ U then h₀ (⟨p.1, hp⟩, p.2) else 0
  have hH {x : EB} (hx : x ∈ U) (y : F) : H (x, y) = h₀ (⟨x, hx⟩, y) := by simp [H, hx]
  have hHs : ContMDiffOn (𝓘(ℝ, EB).prod IF) 𝓘(ℝ) ∞ H (U ×ˢ univ) :=
    hh₀.contMDiffOn_opens_prod_of_eq (U := V) fun x hx y ↦ hH hx y
  let f₀ : EB × F → ℝ := fun p ↦ RoughForm.baseComponent τ.val bs i j p.1 p.2 - H p
  have hf₀ : ContMDiffOn (𝓘(ℝ, EB).prod IF) 𝓘(ℝ) ∞ f₀ (U ×ˢ univ) := hf.contMDiffOn.sub hHs
  refine ⟨fun p ↦ f₀ p - f₀ (p.1, y₀), hf₀.sub (hf₀.comp
    (contMDiff_fst.prodMk contMDiff_const).contMDiffOn fun p hp ↦ ⟨hp.1, mem_univ _⟩),
    fun x _ ↦ sub_self _, fun x hx y w ↦ ?_⟩
  let t : V := ⟨x, hx⟩
  have hh : ContMDiff IF 𝓘(ℝ) ∞ fun y ↦ h₀ (t, y) :=
    hh₀.comp (contMDiff_const.prodMk contMDiff_id)
  have he : (fun y ↦ f₀ (x, y) - f₀ (x, y₀)) =
      fun y ↦ (RoughForm.baseComponent τ.val bs i j x y - h₀ (t, y)) - f₀ (x, y₀) :=
    funext fun y ↦ by simp only [f₀, hH hx y, t]
  have hd : mvfderiv IF (fun y ↦ h₀ (t, y)) y w = (α t).val y ![w] := by
    rw [mvfderiv_apply_eq_mfderiv_apply, ← mextDeriv_ofFunction_apply, hdh₀ t]
  rw [he, mvfderiv_fun_sub (((hfx x).sub hh).mdifferentiableAt (by simp))
      mdifferentiableAt_const, mvfderiv_const, sub_zero, mvfderiv_fun_sub
      ((hfx x).mdifferentiableAt (by simp)) (hh.mdifferentiableAt (by simp)), sub_apply, hd, hη,
    fderiv_mixedComponent_sub_fderiv_mixedComponent]

end TauCeti.SmoothTwoForm

end
