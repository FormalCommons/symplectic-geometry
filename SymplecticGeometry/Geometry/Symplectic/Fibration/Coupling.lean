/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.FiberBundle.RestrictsTo
public import SymplecticGeometry.Geometry.Symplectic.Fibration.HorizontalDistribution
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Descent
import SymplecticGeometry.Geometry.Symplectic.Fibration.Curvature
import TauCeti.Geometry.Manifold.MFDeriv.Constancy

/-!
# Coupling forms: closed forms with the same fibres and connection

Let `A` be a smooth atlas of `proj : M → B` with model fibre `F`, and let `τ` and `τ'` be closed
two-forms on `M` that both restrict to a nondegenerate form `σ` on `F` along `A` and have the same
horizontal spaces. This file shows that their difference `τ' - τ` is basic for `proj`, in the
sense of Tau Ceti's `TauCeti.RoughForm.IsBasic`, when `F` is preconnected: its value at a point
depends only on the image of the point under `proj` and on the images of its arguments under the
derivative of `proj`. This is a step of the uniqueness of coupling forms, McDuff–Salamon
[McDuffSalamon2017], Theorem 6.4.1, and Guillemin–Lerman–Sternberg [GuilleminLermanSternberg1996],
§1.4.

The argument:

* The two forms agree on pairs of vertical vectors, since both pull back to `σ` on each fibre
  (`TauCeti.MapFiber.Atlas.RestrictsTo.apply_eq`). Having the same horizontal
  spaces, they then agree on `(η, v)` for every vertical `η`
  (`TauCeti.SmoothTwoForm.horizontalDistribution_eq_iff`). So `τ' - τ` is semibasic, and at each
  point its value only depends on the images of its arguments under the derivative of `proj`
  (`TauCeti.RoughForm.IsSemibasicAt.apply_eq_of_mfderiv_eq`).
* Hence it is enough to compare its values on horizontal lifts `w₁♯, w₂♯` of fields `w₁ w₂` on
  `B` that are smooth at a point `b`, at two points over `b`. The functions `τ(w₁♯, w₂♯)` and
  `τ'(w₁♯, w₂♯)` have the same derivative along vertical vectors
  (`TauCeti.IsEhresmannConnection.mvfderiv_val_horizontalLiftField_eq_of_isClosed`), so their
  difference, read on the fibre through a fibre inclusion of `A`, has zero derivative, and is
  constant on the preconnected `F` (Tau Ceti's `MDifferentiable.apply_eq_of_mfderiv_eq_zero`).

## Main results

* `TauCeti.MapFiber.Atlas.isBasic_sub_of_horizontalDistribution_eq`: the difference of two closed
  forms with the same restriction to the fibres and the same connection is basic.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §6.4, Theorem 6.4.1.
* [D. McDuff and D. Salamon, *Errata*][McDuffSalamon2019Errata]
* [V. Guillemin, E. Lerman, S. Sternberg, *Symplectic Fibrations and Multiplicity
  Diagrams*][GuilleminLermanSternberg1996], §1.4.
-/

public section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti.MapFiber.Atlas

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {B : Type*}
  [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners ℝ EF HF} {F : Type*} [TopologicalSpace F] [ChartedSpace HF F]
  [IsManifold IF ∞ F]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM] {HM : Type*}
  [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM} [IM.Boundaryless] {M : Type*}
  [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ∞ M]
  {proj : M → B} {A : Atlas F proj} {σ : SmoothTwoForm IF F} {τ τ' : SmoothTwoForm IM M}

/-- **Closed forms with the same fibres and connection differ by a basic form.** Let `A` be a
smooth atlas of `proj : M → B` with preconnected model fibre `F`, and let `τ` and `τ'` be closed
two-forms on `M` that restrict to the same nondegenerate form `σ` on `F` and have the same
horizontal spaces. Then `τ' - τ` is basic for `proj`: `(τ' - τ)_x(v) = (τ' - τ)_y(w)` whenever
`proj x = proj y` and the derivatives of `proj` send `v` and `w` to the same vectors. -/
theorem isBasic_sub_of_horizontalDistribution_eq [PreconnectedSpace F]
    (hA : A.IsContMDiff ∞ IB IF IM) (hσ : σ.IsNondegenerate) (hτc : τ.IsClosed)
    (hτ'c : τ'.IsClosed) (hτ : A.RestrictsTo σ τ) (hτ' : A.RestrictsTo σ τ')
    (hD : SmoothTwoForm.horizontalDistribution IB proj τ =
      SmoothTwoForm.horizontalDistribution IB proj τ') :
    RoughForm.IsBasic IB proj (τ' - τ).val := by
  have hnd := hτ.isVerticallyNondegenerate hA hσ
  have hE := hnd.isEhresmannConnection (hA.isSubmersion ENat.LEInfty.out)
  have hproj : ContMDiff IM IB 2 proj := (hA.isSubmersion ENat.LEInfty.out).contMDiff.of_le
    (by simp)
  -- The forms agree as soon as one argument is vertical.
  have hmix := (SmoothTwoForm.horizontalDistribution_eq_iff hnd fun x η₁ hη₁ η₂ hη₂ ↦ by
    rw [SmoothForm.bilinFormAt_apply, SmoothForm.bilinFormAt_apply, SmoothBundleForm.eval₂_apply,
      SmoothBundleForm.eval₂_apply]
    exact hτ.apply_eq hA hτ' (Fin.forall_fin_two.2 ⟨hη₁, hη₂⟩)).1 hD
  -- So `τ' - τ` is semibasic.
  have hsemi : RoughForm.IsSemibasic IB proj (τ' - τ).val := by
    refine SmoothForm.isSemibasic_iff_ker_mfderiv_le.2 fun x η hη ↦ ?_
    ext v
    have h := hmix x η hη v
    rw [SmoothForm.bilinFormAt_apply, SmoothForm.bilinFormAt_apply, SmoothBundleForm.eval₂_apply,
      SmoothBundleForm.eval₂_apply] at h
    rw [SmoothForm.bilinFormAt_apply, LinearMap.zero_apply, SmoothBundleForm.eval₂_apply,
      Submodule.coe_sub, Pi.sub_apply, ContinuousAlternatingMap.sub_apply, h, sub_self]
  refine RoughForm.isBasic_iff.2 fun x y hxy v w hvw ↦ ?_
  -- Extend the images of the arguments to fields on `B`, smooth at `proj x`.
  let U₁ := FiberBundle.extend EB (mfderiv IM IB proj x (v 0))
  let U₂ := FiberBundle.extend EB (mfderiv IM IB proj x (v 1))
  -- The values of two-forms on the horizontal lifts of `U₁` and `U₂`.
  let G : SmoothTwoForm IM M → M → ℝ := fun ρ z ↦
    ρ.val z ![hE.horizontalLiftField U₁ z, hE.horizontalLiftField U₂ z]
  let g : M → ℝ := G τ' - G τ
  -- At any point over `proj x`, the value of `τ' - τ` on lifts of the images of `v` is that of `g`.
  have hlift : ∀ z, proj z = proj x → ∀ u : Fin 2 → TangentSpace IM z,
      (∀ i, mfderiv IM IB proj z (u i) = mfderiv IM IB proj x (v i)) → (τ' - τ).val z u = g z := by
    intro z hz u hu
    refine ((RoughForm.isSemibasic_def.1 hsemi z).apply_eq_of_mfderiv_eq
      (w := ![hE.horizontalLiftField U₁ z, hE.horizontalLiftField U₂ z]) fun i ↦ ?_).trans ?_
    swap
    · simp only [g, G, Submodule.coe_sub, Pi.sub_apply, ContinuousAlternatingMap.sub_apply]
    rw [hu i]
    -- The fields `U₁` and `U₂` take the prescribed values over `proj z = proj x`.
    fin_cases i <;>
      exact (eq_of_heq ((congr_arg_heq _ hz).trans
        (heq_of_eq (FiberBundle.extend_apply_self _ _)))).symm.trans
          (hE.mfderiv_horizontalLiftField _ z).symm
  -- `g` is constant on the fibre over `proj x`.
  have hconst : g x = g y := by
    let e := A.trivAt (proj x)
    have hb : proj x ∈ e.baseSet := A.mem_baseSet_trivAt (proj x)
    have hι : ContMDiff IF IM ∞ (e.fiberInclusionMap hb) :=
      e.contMDiff_fiberInclusionMap (hA.contMDiffOn_trivAt_symm (proj x)) hb
    have hU₁ : ContMDiffAt IB IB.tangent 1 (T% U₁) (proj x) :=
      FiberBundle.contMDiffAt_extend (I := IB) EB _
    have hU₂ : ContMDiffAt IB IB.tangent 1 (T% U₂) (proj x) :=
      FiberBundle.contMDiffAt_extend (I := IB) EB _
    -- At each point over `proj x`, the two functions making up `g` are differentiable.
    have hdiff : ∀ z, proj z = proj x → ∀ ρ : SmoothTwoForm IM M,
        MDifferentiableAt IM 𝓘(ℝ, ℝ) (G ρ) z := by
      intro z hz ρ
      have h₁ := hE.mdifferentiableAt_horizontalLiftField (by simp) (hproj z) (hz ▸ hU₁)
      have h₂ := hE.mdifferentiableAt_horizontalLiftField (by simp) (hproj z) (hz ▸ hU₂)
      convert ρ.mdifferentiableAt_apply_vectorField
        (V := ![hE.horizontalLiftField U₁, hE.horizontalLiftField U₂])
        (fun i ↦ by fin_cases i <;> assumption) using 3 with z
      ext i
      fin_cases i <;> simp
    have hg : ∀ z, proj z = proj x → MDifferentiableAt IM 𝓘(ℝ, ℝ) g z := fun z hz ↦
      (hdiff z hz τ').sub (hdiff z hz τ)
    have hgι : MDifferentiable IF 𝓘(ℝ, ℝ) (g ∘ e.fiberInclusionMap hb) := fun p ↦
      (hg _ (e.proj_fiberInclusionMap hb p)).comp p (hι.mdifferentiable (by simp) p)
    have hzero : ∀ p, mfderiv IF 𝓘(ℝ, ℝ) (g ∘ e.fiberInclusionMap hb) p = 0 := by
      intro p
      have hp := e.proj_fiberInclusionMap hb p
      ext ε
      have hη :=
        e.mfderiv_proj_mfderiv_fiberInclusionMap_apply (IM := IM) (IB := IB) (IF := IF) hb p ε
      -- `mvfderiv` of a real function is its `mfderiv`, read in `ℝ`.
      change mvfderiv IF (g ∘ e.fiberInclusionMap hb) p ε = 0
      rw [mvfderiv_comp_apply p (hg _ hp) (hι.mdifferentiable (by simp) p),
        mvfderiv_sub (hdiff _ hp τ') (hdiff _ hp τ), sub_apply, sub_eq_zero]
      exact TauCeti.IsEhresmannConnection.mvfderiv_val_horizontalLiftField_eq_of_isClosed hE
        (by simp) hproj hτc hτ'c hmix (by rwa [hp]) (by rwa [hp]) hη
    have hxι : e.fiberInclusionMap hb (e x).2 = x := e.fiberInclusionMap_snd_apply hb
    have hyι : e.fiberInclusionMap hb (e y).2 = y := by
      rw [e.fiberInclusionMap_apply, hxy, e.symm_apply_mk_proj (e.mem_source.2 (hxy ▸ hb))]
    have h := hgι.apply_eq_of_mfderiv_eq_zero hzero (e x).2 (e y).2
    rwa [Function.comp_apply, Function.comp_apply, hxι, hyι] at h
  refine (hlift x rfl v fun _ ↦ rfl).trans (hconst.trans (hlift y hxy.symm w fun i ↦ ?_).symm)
  -- The images of `w` and `v` agree, read over `proj y = proj x`.
  exact eq_of_heq ((heq_tangentSpaceCast hxy.symm _).symm.trans (heq_of_eq (hvw i).symm))

end TauCeti.MapFiber.Atlas

end
