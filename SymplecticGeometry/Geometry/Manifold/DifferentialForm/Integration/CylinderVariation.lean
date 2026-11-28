/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Homotopy
import SymplecticGeometry.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.Prod
import SymplecticGeometry.Analysis.SpecialFunctions.SmoothTransition.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth

/-!
# Variation of the integral of a two-form over a family of cylinders

Let `u : ℝ × ℝ × ℝ → M` be a `C²` map, written `u (s, t, θ)`, and `τ` a `C¹` two-form on `M`.
For each `s`, the slice `(t, θ) ↦ u (s, t, θ)` is a map of the plane, and Tau Ceti's
`TauCeti.rectangleIntegral` integrates `τ` over it on `[0, 1] × [0, 1]`. This file computes the
derivative of that integral in `s`.

The pointwise step is the coordinate formula for the exterior derivative of the flat two-form
`u^* τ` on `ℝ × ℝ × ℝ` (Tau Ceti's `TauCeti.extDeriv_apply_triple`), read back on `M`
through Tau Ceti's `TauCeti.mpullback_mextDeriv`: the partial derivative in `s` of
`τ (∂ₜu, ∂_θu)` is `dτ (∂ₛu, ∂ₜu, ∂_θu) + ∂ₜ (τ (∂ₛu, ∂_θu)) - ∂_θ (τ (∂ₛu, ∂ₜu))`
(`TauCeti.fderiv_mpullback_apply_eq_mextDeriv_add_sub`). Here `τ (∂ᵢu, ∂ⱼu)` is the pullback
`u^* τ` evaluated on the coordinate vectors, and the partial derivatives are `fderiv` applied to
coordinate vectors. Passing to the flat form `u^* τ` follows the opening of the proof of Tau
Ceti's `TauCeti.rectangleIntegral_mextDeriv`.

Integrating over the square, after differentiating under the integral sign
(`intervalIntegral.hasDerivAt_integral_integral_of_contDiff`), the term in `t` integrates to the
values on the boundary loops `t = 0` and `t = 1`, and, when `u` is `1`-periodic in `θ`, the term
in `θ` integrates to zero (`TauCeti.hasDerivAt_rectangleIntegral_slice`), by the invariance of
the pullback under the period, as in the proof of Tau Ceti's
`TauCeti.rectangleIntegral_comp_add_snd_of_periodic`. This extends Tau Ceti's
`TauCeti.hasDerivAt_rectangleIntegral_comp_prodMap_affine`, which differentiates the integral over
a family of rectangles in two parameters, to a third parameter.

The derivative at `s₀` depends only on `u` near the slice at `s₀`: composing `u` in `s` with a
smooth map of `ℝ` into a neighbourhood of `s₀` that is the identity near `s₀`
(`SymplecticGeometry.exists_contDiff_eqOn_id_Icc_mem_Ioo`), gives the formula for `u` smooth only
near that slice (`TauCeti.hasDerivAt_rectangleIntegral_slice_of_contMDiffOn`).

## Main results

* `TauCeti.fderiv_mpullback_apply_eq_mextDeriv_add_sub`: the pointwise formula.
* `TauCeti.hasDerivAt_rectangleIntegral_slice`: the derivative of the integral of `τ` over the
  cylinders `(t, θ) ↦ u (s, t, θ)`.
* `TauCeti.hasDerivAt_rectangleIntegral_slice_of_contMDiffOn`: the same derivative at `s₀`, for
  `u` that is `C²` and periodic only for `s` near `s₀`.

## References

* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §1
  (the exterior derivative in coordinates).
-/

public section

open Set MeasureTheory Function
open scoped Manifold Interval ContDiff Topology

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- The integral of a two-form over the slice `(t, θ) ↦ u (s, t, θ)` of a differentiable map
`u : ℝ × ℝ × ℝ → M` is the iterated integral of the pullback `u^* φ` on the coordinate vectors of
`t` and `θ`, at the points `(s, t, θ)`. -/
theorem rectangleIntegral_prodMk_eq_integral (φ : RoughForm I M F 2) {u : ℝ × ℝ × ℝ → M}
    (hu : MDifferentiable 𝓘(ℝ, ℝ × ℝ × ℝ) I u) (s : ℝ) (a b : ℝ × ℝ) :
    rectangleIntegral φ (fun z ↦ u (s, z)) a b = ∫ t in a.1..b.1, ∫ θ in a.2..b.2,
      mpullback 𝓘(ℝ, ℝ × ℝ × ℝ) I u φ (s, t, θ) ![(0, 1, 0), (0, 0, 1)] := by
  rw [rectangleIntegral_def]
  refine intervalIntegral.integral_congr fun t _ ↦ intervalIntegral.integral_congr fun θ _ ↦ ?_
  refine (mpullback_comp_prodMk_apply_modelSpace (hu _) φ _).trans
    (congrArg (mpullback 𝓘(ℝ, ℝ × ℝ × ℝ) I u φ (s, t, θ)) (FinVec.etaExpand_eq _).symm)

variable [IsManifold I 2 M]

/-- **The exterior derivative on the coordinate fields of a three-parameter family.** For a `C¹`
two-form `τ` and a `C²` map `u : ℝ × ℝ × ℝ → M`, write `τ (∂ᵢu, ∂ⱼu)` for the pullback
`u^* τ` evaluated on two coordinate vectors, and `∂ₛ`, `∂ₜ`, `∂_θ` for `fderiv` applied to the
coordinate vectors. Then
`∂ₛ (τ (∂ₜu, ∂_θu)) = dτ (∂ₛu, ∂ₜu, ∂_θu) + ∂ₜ (τ (∂ₛu, ∂_θu)) - ∂_θ (τ (∂ₛu, ∂ₜu))`. -/
theorem fderiv_mpullback_apply_eq_mextDeriv_add_sub {τ : RoughForm I M F 2}
    (hτ : IsSmoothForm I 1 τ) {u : ℝ × ℝ × ℝ → M} (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ × ℝ) I 2 u)
    (x : ℝ × ℝ × ℝ) :
    fderiv ℝ (fun y ↦ mpullback 𝓘(ℝ, ℝ × ℝ × ℝ) I u τ y ![(0, 1, 0), (0, 0, 1)]) x (1, 0, 0) =
      mpullback 𝓘(ℝ, ℝ × ℝ × ℝ) I u (mextDeriv τ) x ![(1, 0, 0), (0, 1, 0), (0, 0, 1)] +
        fderiv ℝ (fun y ↦ mpullback 𝓘(ℝ, ℝ × ℝ × ℝ) I u τ y ![(1, 0, 0), (0, 0, 1)]) x
          (0, 1, 0) -
        fderiv ℝ (fun y ↦ mpullback 𝓘(ℝ, ℝ × ℝ × ℝ) I u τ y ![(1, 0, 0), (0, 1, 0)]) x
          (0, 0, 1) := by
  have hψ : ContDiff ℝ 1 (mpullback 𝓘(ℝ, ℝ × ℝ × ℝ) I u τ) :=
    isSmoothForm_modelSpace_iff.mp (hτ.mpullback (by simpa [one_add_one_eq_two] using hu))
  have hd : extDeriv (mpullback 𝓘(ℝ, ℝ × ℝ × ℝ) I u τ) x
      ![((1 : ℝ), (0 : ℝ), (0 : ℝ)), (0, 1, 0), (0, 0, 1)] =
      fderiv ℝ (fun y ↦ mpullback 𝓘(ℝ, ℝ × ℝ × ℝ) I u τ y ![(0, 1, 0), (0, 0, 1)]) x (1, 0, 0) -
        fderiv ℝ (fun y ↦ mpullback 𝓘(ℝ, ℝ × ℝ × ℝ) I u τ y ![(1, 0, 0), (0, 0, 1)]) x
          (0, 1, 0) +
        fderiv ℝ (fun y ↦ mpullback 𝓘(ℝ, ℝ × ℝ × ℝ) I u τ y ![(1, 0, 0), (0, 1, 0)]) x
          (0, 0, 1) := by
    refine (extDeriv_apply_triple x _ _ _).trans ?_
    rw [← fderiv_continuousAlternatingMap_apply_const_apply (hψ.differentiable one_ne_zero x),
      ← fderiv_continuousAlternatingMap_apply_const_apply (hψ.differentiable one_ne_zero x),
      ← fderiv_continuousAlternatingMap_apply_const_apply (hψ.differentiable one_ne_zero x)]
    -- The two sides differ only in how the vector literals were elaborated.
    rfl
  rw [mpullback_mextDeriv hu ((isSmoothBundleForm_def _ _).mpr hτ.contMDiff),
    mextDeriv_eq_extDeriv]
  -- `hd` is stated on vectors of `ℝ × ℝ × ℝ`, the goal on the same vectors as tangent vectors.
  refine Eq.trans ?_ (congrArg (fun z ↦ z + _ - _) hd.symm)
  abel

/-- **The first variation of the area of a family of cylinders.** Let `τ` be a `C¹` two-form and
`u : ℝ × ℝ × ℝ → M` a `C²` map, `1`-periodic in its last coordinate, so that each slice
`(t, θ) ↦ u (s, t, θ)` is a cylinder. The integral of `τ` over the slice, on `[0, 1] × [0, 1]`,
has derivative in `s` the integral of `dτ (∂ₛu, ∂ₜu, ∂_θu)` over the square, plus the integral over
`θ ∈ [0, 1]` of the difference of `τ (∂ₛu, ∂_θu)` between the boundary loops `t = 1` and `t = 0`.
-/
theorem hasDerivAt_rectangleIntegral_slice [CompleteSpace F] {τ : RoughForm I M F 2}
    (hτ : IsSmoothForm I 1 τ) {u : ℝ × ℝ × ℝ → M} (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ × ℝ) I 2 u)
    (hper : ∀ s t θ, u (s, t, θ + 1) = u (s, t, θ)) (s₀ : ℝ) :
    HasDerivAt (fun s ↦ rectangleIntegral τ (fun z ↦ u (s, z)) (0, 0) (1, 1))
      ((∫ t in 0..1, ∫ θ in 0..1, mpullback 𝓘(ℝ, ℝ × ℝ × ℝ) I u (mextDeriv τ) (s₀, t, θ)
          ![(1, 0, 0), (0, 1, 0), (0, 0, 1)]) +
        ∫ θ in 0..1, (mpullback 𝓘(ℝ, ℝ × ℝ × ℝ) I u τ (s₀, 1, θ) ![(1, 0, 0), (0, 0, 1)] -
          mpullback 𝓘(ℝ, ℝ × ℝ × ℝ) I u τ (s₀, 0, θ) ![(1, 0, 0), (0, 0, 1)])) s₀ := by
  -- The pullbacks `u^* τ` and `u^* dτ`, as flat forms on `ℝ × ℝ × ℝ`.
  let ψ : ℝ × ℝ × ℝ → (ℝ × ℝ × ℝ) [⋀^Fin 2]→L[ℝ] F := mpullback 𝓘(ℝ, ℝ × ℝ × ℝ) I u τ
  let D : ℝ × ℝ × ℝ → F := fun x ↦
    (mpullback 𝓘(ℝ, ℝ × ℝ × ℝ) I u (mextDeriv τ) :
      ℝ × ℝ × ℝ → (ℝ × ℝ × ℝ) [⋀^Fin 3]→L[ℝ] F) x ![(1, 0, 0), (0, 1, 0), (0, 0, 1)]
  have hψ : ContDiff ℝ 1 ψ :=
    isSmoothForm_modelSpace_iff.mp (hτ.mpullback (by simpa [one_add_one_eq_two] using hu))
  -- The coefficients `τ (∂ᵢu, ∂ⱼu)` of the pullback, and their partial derivatives.
  have hg (v : Fin 2 → ℝ × ℝ × ℝ) : ContDiff ℝ 1 fun y ↦ ψ y v :=
    (ContinuousAlternatingMap.apply ℝ (ℝ × ℝ × ℝ) F v).contDiff.comp hψ
  have hgd (v : Fin 2 → ℝ × ℝ × ℝ) (w : ℝ × ℝ × ℝ) :
      Continuous fun y ↦ fderiv ℝ (fun y ↦ ψ y v) y w :=
    ((hg v).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hpd (v : Fin 2 → ℝ × ℝ × ℝ) {f : ℝ → ℝ × ℝ × ℝ} {w : ℝ × ℝ × ℝ} {r : ℝ}
      (hf : HasDerivAt f w r) :
      HasDerivAt (fun r ↦ ψ (f r) v) (fderiv ℝ (fun y ↦ ψ y v) (f r) w) r :=
    ((hg v).differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt r hf
  have hcurve (a b c : ℝ) : HasDerivAt (fun r ↦ ((a, b, r) : ℝ × ℝ × ℝ)) (0, 0, 1) c :=
    (hasDerivAt_const c a).prodMk ((hasDerivAt_const c b).prodMk (hasDerivAt_id c))
  have hcurve' (a b c : ℝ) : HasDerivAt (fun r ↦ ((a, r, c) : ℝ × ℝ × ℝ)) (0, 1, 0) b :=
    (hasDerivAt_const b a).prodMk ((hasDerivAt_id b).prodMk (hasDerivAt_const b c))
  have hslc : Continuous fun p : ℝ × ℝ ↦ ((s₀, p.1, p.2) : ℝ × ℝ × ℝ) := by fun_prop
  -- The pointwise formula, and the continuity of each of its terms.
  have hform (x : ℝ × ℝ × ℝ) : fderiv ℝ (fun y ↦ ψ y ![(0, 1, 0), (0, 0, 1)]) x (1, 0, 0) =
      D x + fderiv ℝ (fun y ↦ ψ y ![(1, 0, 0), (0, 0, 1)]) x (0, 1, 0) -
        fderiv ℝ (fun y ↦ ψ y ![(1, 0, 0), (0, 1, 0)]) x (0, 0, 1) :=
    fderiv_mpullback_apply_eq_mextDeriv_add_sub hτ hu x
  have hD : Continuous D :=
    (isSmoothForm_mextDeriv hτ (by norm_num)).continuous_mpullback_apply
      (hu.of_le one_le_two) ![(1, 0, 0), (0, 1, 0), (0, 0, 1)]
  have hint {f : ℝ × ℝ × ℝ → F} (hf : Continuous f) (t : ℝ) :
      IntervalIntegrable (fun θ ↦ f (s₀, t, θ)) volume 0 1 :=
    (hf.comp (by fun_prop)).intervalIntegrable _ _
  -- The term in `θ` integrates to zero, by periodicity.
  have hψper (y : ℝ × ℝ × ℝ) : ψ (y + (0, 0, 1)) = ψ y :=
    mpullback_add_of_forall_add_eq (hu.mdifferentiable two_ne_zero)
      (fun ⟨a, b, c⟩ ↦ by simpa using hper a b c) τ y
  have hQ (t : ℝ) : ∫ θ in 0..1,
      fderiv ℝ (fun y ↦ ψ y ![(1, 0, 0), (0, 1, 0)]) (s₀, t, θ) (0, 0, 1) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ ↦ hpd _ (hcurve s₀ t θ))
      (hint (hgd _ _) t), sub_eq_zero]
    simpa using congrArg (· ![((1 : ℝ), (0 : ℝ), (0 : ℝ)), (0, 1, 0)]) (hψper (s₀, t, 0))
  -- The term in `t` integrates to the boundary values.
  have hP : ∫ t in 0..1, ∫ θ in 0..1,
      fderiv ℝ (fun y ↦ ψ y ![(1, 0, 0), (0, 0, 1)]) (s₀, t, θ) (0, 1, 0) =
      ∫ θ in 0..1, (ψ (s₀, 1, θ) ![(1, 0, 0), (0, 0, 1)] -
        ψ (s₀, 0, θ) ![(1, 0, 0), (0, 0, 1)]) := by
    rw [intervalIntegral_intervalIntegral_swap]
    · refine intervalIntegral.integral_congr fun θ _ ↦ ?_
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hpd _ (hcurve' s₀ t θ))
        (((hgd _ _).comp (by fun_prop : Continuous fun t : ℝ ↦ (s₀, t, θ))).intervalIntegrable _ _)
    · exact (((hgd _ _).comp hslc).continuousOn.integrableOn_compact
        (isCompact_uIcc.prod isCompact_uIcc)).mono_set (prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  have key : ∫ t in 0..1, ∫ θ in 0..1,
      fderiv ℝ (fun y ↦ ψ y ![(0, 1, 0), (0, 0, 1)]) (s₀, t, θ) (1, 0, 0) =
      (∫ t in 0..1, ∫ θ in 0..1, D (s₀, t, θ)) +
        ∫ θ in 0..1, (ψ (s₀, 1, θ) ![(1, 0, 0), (0, 0, 1)] -
          ψ (s₀, 0, θ) ![(1, 0, 0), (0, 0, 1)]) := by
    rw [← hP, ← intervalIntegral.integral_add]
    · refine intervalIntegral.integral_congr fun t _ ↦ ?_
      simp only [hform]
      rw [intervalIntegral.integral_sub ((hint hD t).add (hint (hgd _ _) t)) (hint (hgd _ _) t),
        hQ, sub_zero, intervalIntegral.integral_add (hint hD t) (hint (hgd _ _) t)]
    · exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun t θ ↦ D (s₀, t, θ)) (hD.comp hslc) 0 1).intervalIntegrable _ _
    · exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun t θ ↦ fderiv ℝ (fun y ↦ ψ y ![(1, 0, 0), (0, 0, 1)]) (s₀, t, θ) (0, 1, 0))
        ((hgd _ _).comp hslc) 0 1).intervalIntegrable _ _
  simp only [rectangleIntegral_prodMk_eq_integral τ (hu.mdifferentiable two_ne_zero)]
  exact (intervalIntegral.hasDerivAt_integral_integral_of_contDiff (hg ![(0, 1, 0), (0, 0, 1)])
    0 1 0 1
    s₀).congr_deriv key
/-- **The first variation of the area of a family of cylinders, from smoothness near a slice.**
The derivative at `s₀` in `TauCeti.hasDerivAt_rectangleIntegral_slice` only needs `u` to be `C²`,
and `1`-periodic in its last coordinate, for `s` in a neighbourhood `U` of `s₀`. -/
theorem hasDerivAt_rectangleIntegral_slice_of_contMDiffOn [CompleteSpace F]
    {τ : RoughForm I M F 2} (hτ : IsSmoothForm I 1 τ) {u : ℝ × ℝ × ℝ → M} {U : Set ℝ} {s₀ : ℝ}
    (hU : U ∈ 𝓝 s₀) (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ × ℝ) I 2 u (U ×ˢ univ))
    (hper : ∀ s ∈ U, ∀ t θ, u (s, t, θ + 1) = u (s, t, θ)) :
    HasDerivAt (fun s ↦ rectangleIntegral τ (fun z ↦ u (s, z)) (0, 0) (1, 1))
      ((∫ t in 0..1, ∫ θ in 0..1, mpullback 𝓘(ℝ, ℝ × ℝ × ℝ) I u (mextDeriv τ) (s₀, t, θ)
          ![(1, 0, 0), (0, 1, 0), (0, 0, 1)]) +
        ∫ θ in 0..1, (mpullback 𝓘(ℝ, ℝ × ℝ × ℝ) I u τ (s₀, 1, θ) ![(1, 0, 0), (0, 0, 1)] -
          mpullback 𝓘(ℝ, ℝ × ℝ × ℝ) I u τ (s₀, 0, θ) ![(1, 0, 0), (0, 0, 1)])) s₀ := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hU
  -- A smooth map `ρ` of `ℝ` into the ball of radius `δ` about `s₀`, the identity near `s₀`.
  obtain ⟨ρ, hρ, hρid, hρU, -⟩ := SymplecticGeometry.exists_contDiff_eqOn_id_Icc_mem_Ioo
    (a := s₀ - δ / 2) (b := s₀ + δ / 2) (by linarith) (half_pos hδ)
  replace hρU (r : ℝ) : ρ r ∈ U := hball (by
    rw [Real.ball_eq_Ioo]
    convert hρU r using 2 <;> ring)
  have hρs : ρ =ᶠ[𝓝 s₀] id :=
    Filter.eventuallyEq_of_mem (Icc_mem_nhds (by linarith) (by linarith)) hρid
  -- `u` reparametrized by `ρ` in `s` is smooth everywhere, and agrees with `u` near `s₀`.
  set w : ℝ × ℝ × ℝ → M := fun p ↦ u (ρ p.1, p.2)
  have hw : ContMDiff 𝓘(ℝ, ℝ × ℝ × ℝ) I 2 w :=
    hu.comp_contMDiff (((hρ.comp contDiff_fst).prodMk contDiff_snd).contMDiff.of_le (by simp))
      fun p ↦ ⟨hρU p.1, mem_univ _⟩
  have hwu (t θ : ℝ) : w =ᶠ[𝓝 (s₀, t, θ)] u := by
    filter_upwards [hρs.comp_tendsto (continuous_fst.tendsto (s₀, t, θ))] with p hp
    simp only [w, comp_apply, id] at hp ⊢
    rw [hp]
  have key := hasDerivAt_rectangleIntegral_slice hτ hw (fun s t θ ↦ hper (ρ s) (hρU s) t θ) s₀
  simp only [(hwu _ _).mpullback_eq] at key
  refine key.congr_of_eventuallyEq ?_
  filter_upwards [hρs] with s hs
  simp only [w, hs, id]

end TauCeti
