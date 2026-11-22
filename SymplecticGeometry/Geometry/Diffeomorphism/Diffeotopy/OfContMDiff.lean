/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Real
import TauCeti.Analysis.Calculus.JointImplicitFunction
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import SymplecticGeometry.Analysis.Calculus.ContDiff.Seeley.Extension

/-!
# Diffeotopies from families of diffeomorphisms

A family `ψ : unitInterval → M ≃ₘ M` of diffeomorphisms of a finite-dimensional boundaryless
manifold that is jointly smooth in `(t, x)` and starts at the identity is a diffeotopy. The point is
that the inverses `(t, y) ↦ ψ_t⁻¹ y` are jointly smooth too, also at the ends of the interval,
where the inverse function theorem on the manifold with boundary `unitInterval × M` does not apply.

## Main definitions

* `TauCeti.Diffeotopy.ofContMDiff ψ hψ h₀`: the diffeotopy `(t, x) ↦ ψ_t x` of a jointly smooth
  family `ψ` over `[0, 1]` with `ψ 0 = id`.

## Main results

* `Diffeomorph.contMDiff_symm_eval_unitInterval`: the inverses of a jointly smooth family of
  diffeomorphisms over `[0, 1]` are jointly smooth.
* `TauCeti.Diffeotopy.ofContMDiff_eq_ofReal`: on the restriction of a family over `ℝ`, the
  constructor agrees with `TauCeti.Diffeotopy.ofReal`.

## Implementation notes

The inverses are smooth near each point `(t₀, ψ_{t₀} x₀)`. In charts at `x₀` and at `ψ_{t₀} x₀`,
the family is a map `G (s, u)` smooth on `Icc a b ×ˢ U`, for an interval `[a, b]` that is a
neighbourhood of `t₀` in `[0, 1]` and an open `U`. Seeley's extension
(`SymplecticGeometry.exists_contDiffOn_eqOn_Icc_prod`) gives a map `H` smooth on `univ ×ˢ U` that
agrees with `G` there. Its partial derivative in `u` at `(t₀, u₀)` is the derivative of `ψ_{t₀}` in
charts, which is invertible, so Tau Ceti's implicit function theorem with a moving level
(`HasStrictFDerivAt.jointImplicitFunctionOfProdDomain`) solves `H (s, u) = v` near
`(t₀, H (t₀, u₀))` by a smooth `u = φ (s, v)`. For `s ∈ [a, b]` the equation is
`G (s, u) = v`, so `φ` computes `ψ_s⁻¹` in charts. The argument is the same at interior times and
at the ends: at an end, the extension `H` supplies the values of `G` that are missing for times
outside `[0, 1]`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.1.
* R. T. Seeley, *Extension of $C^\infty$ functions defined in a half space*,
  Proc. Amer. Math. Soc. 15 (1964), 625–626.
-/

public noncomputable section

open Set Filter Function
open scoped Manifold ContDiff Topology

section SymmEval

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- A step of `Diffeomorph.contMDiff_symm_eval_unitInterval`: for a continuous `f` on
`unitInterval × M`, an interval `[a, b]` that is a neighbourhood of `t₀` in `[0, 1]`, and an open
`U` in the target of the chart at `x₀` containing the image of `x₀`, such that `f` maps
`[a, b] × U`, read through the chart at `x₀`, into the source of the chart at `f (t₀, x₀)`. -/
private theorem exists_Icc_prod_extChartAt [BoundarylessManifold I M] {f : unitInterval × M → M}
    (hf : Continuous f) (t₀ : unitInterval) (x₀ : M) :
    ∃ a b : ℝ, ∃ U : Set E, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧ IsOpen U ∧ extChartAt I x₀ x₀ ∈ U ∧
      {s : unitInterval | (s : ℝ) ∈ Icc a b} ∈ 𝓝 t₀ ∧
      ∀ s : unitInterval, (s : ℝ) ∈ Icc a b → ∀ u ∈ U, u ∈ (extChartAt I x₀).target ∧
        f (s, (extChartAt I x₀).symm u) ∈ (extChartAt I (f (t₀, x₀))).source := by
  set e := extChartAt I x₀
  have htarget : e.target ∈ 𝓝 (e x₀) :=
    nhdsWithin_eq_nhds.2 (range_mem_nhds_isInteriorPoint
      (BoundarylessManifold.isInteriorPoint (I := I) (x := x₀))) ▸
      extChartAt_target_mem_nhdsWithin x₀
  have hc : ContinuousAt (fun q : unitInterval × E ↦ f (q.1, e.symm q.2)) (t₀, e x₀) :=
    hf.continuousAt.comp (continuousAt_fst.prodMk (ContinuousAt.comp (f := Prod.snd)
      (continuousAt_extChartAt_symm'' (mem_extChartAt_target x₀)) continuousAt_snd))
  have hS : Prod.snd ⁻¹' e.target ∩
      (fun q : unitInterval × E ↦ f (q.1, e.symm q.2)) ⁻¹' (extChartAt I (f (t₀, x₀))).source ∈
      𝓝 (t₀, e x₀) := by
    refine inter_mem ((continuous_snd.continuousAt (x := (t₀, e x₀))).preimage_mem_nhds htarget)
      (hc.preimage_mem_nhds ?_)
    simp only [e, extChartAt_to_inv]
    exact extChartAt_source_mem_nhds _
  obtain ⟨V, hV, W, hW, hVW⟩ := mem_nhds_prod_iff.1 hS
  obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhds_iff.1 hV
  have h₀ := t₀.property.1
  have h₁ := t₀.property.2
  refine ⟨max 0 (t₀ - δ / 2), min 1 (t₀ + δ / 2), interior W, le_max_left _ _, ?_,
    min_le_left _ _, isOpen_interior,
    mem_interior_iff_mem_nhds.2 hW, mem_of_superset (Metric.ball_mem_nhds t₀ (half_pos hδ)) ?_,
    fun s hs u hu ↦ hVW (mk_mem_prod (hδV ?_) (interior_subset hu))⟩
  · simp only [max_lt_iff, lt_min_iff]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · intro s hs
    have h := abs_lt.1 (Real.dist_eq _ _ ▸ Subtype.dist_eq s t₀ ▸ Metric.mem_ball.1 hs)
    exact ⟨max_le s.property.1 (by linarith), le_min s.property.2 (by linarith)⟩
  · rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, abs_lt]
    have := le_of_max_le_right hs.1
    have := le_min_iff.1 hs.2
    constructor <;> linarith

/-- A step of `Diffeomorph.contMDiff_symm_eval_unitInterval`: a smooth map `f` on
`unitInterval × M`, written in charts on `[a, b] × U` as in `exists_Icc_prod_extChartAt`, is smooth
there. -/
private theorem contDiffOn_extChartAt_comp_projIcc [IsManifold I ∞ M] {f : unitInterval × M → M}
    (hf : ContMDiff ((𝓡∂ 1).prod I) I ∞ f) {x₀ y₀ : M} {a b : ℝ} {U : Set E}
    (hab : Icc a b ⊆ Icc 0 1)
    (hU : ∀ s : unitInterval, (s : ℝ) ∈ Icc a b → ∀ u ∈ U, u ∈ (extChartAt I x₀).target ∧
      f (s, (extChartAt I x₀).symm u) ∈ (extChartAt I y₀).source) :
    ContDiffOn ℝ ∞ (fun q : ℝ × E ↦
      extChartAt I y₀ (f (projIcc 0 1 zero_le_one q.1, (extChartAt I x₀).symm q.2)))
      (Icc a b ×ˢ U) := by
  have hU' {q : ℝ × E} (hq : q ∈ Icc a b ×ˢ U) := hU (projIcc 0 1 zero_le_one q.1)
    (by rw [projIcc_of_mem _ (hab hq.1)]; exact hq.1) q.2 hq.2
  refine contMDiffOn_iff_contDiffOn.1 ?_
  have hP : ContMDiffOn 𝓘(ℝ, ℝ × E) ((𝓡∂ 1).prod I) ∞
      (fun q : ℝ × E ↦ (projIcc 0 1 zero_le_one q.1, (extChartAt I x₀).symm q.2))
      (Icc a b ×ˢ U) :=
    ((contMDiffOn_projIcc.mono hab).comp contDiff_fst.contMDiff.contMDiffOn
      fun q (hq : q ∈ Icc a b ×ˢ U) ↦ hq.1).prodMk ((contMDiffOn_extChartAt_symm x₀).comp
        contDiff_snd.contMDiff.contMDiffOn fun q (hq : q ∈ Icc a b ×ˢ U) ↦ (hU' hq).1)
  refine contMDiffOn_extChartAt.comp (hf.comp_contMDiffOn hP) fun q hq ↦ ?_
  rw [← extChartAt_source I]
  exact (hU' hq).2

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M]

/-- The local step of `Diffeomorph.contMDiff_symm_eval_unitInterval`: the inverses are jointly
smooth at `(t₀, ψ_{t₀} x₀)`. -/
private theorem Diffeomorph.contMDiffAt_symm_eval_unitInterval {ψ : unitInterval → M ≃ₘ⟮I, I⟯ M}
    (hψ : ContMDiff ((𝓡∂ 1).prod I) I ∞ (fun p : unitInterval × M ↦ ψ p.1 p.2))
    (t₀ : unitInterval) (x₀ : M) :
    ContMDiffAt ((𝓡∂ 1).prod I) I ∞ (fun p : unitInterval × M ↦ (ψ p.1).symm p.2)
      (t₀, ψ t₀ x₀) := by
  set e := extChartAt I x₀
  set e' := extChartAt I (ψ t₀ x₀)
  obtain ⟨a, b, U, ha, hab, hb, hU, hu₀, hnhds, hmaps⟩ :=
    exists_Icc_prod_extChartAt (I := I) hψ.continuous t₀ x₀
  obtain ⟨Hf, hH, hHG⟩ := SymplecticGeometry.exists_contDiffOn_eqOn_Icc_prod hab hU
    (contDiffOn_extChartAt_comp_projIcc hψ (Icc_subset_Icc ha hb) hmaps)
  set u₀ := e x₀
  have ht₀ : (t₀ : ℝ) ∈ Icc a b := mem_ofPred_eq ▸ mem_of_mem_nhds hnhds
  have hHG' {s : unitInterval} (hs : (s : ℝ) ∈ Icc a b) {u : E} (hu : u ∈ U) :
      Hf (s, u) = e' (ψ s (e.symm u)) := by
    rw [hHG ⟨hs, hu⟩]
    simp only [projIcc_val, e, e']
  have hHt₀ : (fun u ↦ Hf (t₀, u)) =ᶠ[𝓝 u₀] writtenInExtChartAt I I x₀ (ψ t₀) := by
    filter_upwards [hU.mem_nhds hu₀] with u hu
    rw [hHG' ht₀ hu]
    simp only [writtenInExtChartAt, comp_apply, e, e']
  have hHz : Hf ((t₀ : ℝ), u₀) = e' (ψ t₀ x₀) := by
    rw [hHG' ht₀ hu₀]
    simp only [u₀, e, extChartAt_to_inv]
  -- The equation `Hf (s, u) = v`, solved for `u` near `((t₀, e' (ψ_{t₀} x₀)), u₀)`.
  have hHat : ContDiffAt ℝ ∞ Hf ((t₀ : ℝ), u₀) :=
    hH.contDiffAt (prod_mem_nhds univ_mem (hU.mem_nhds hu₀))
  have hψd : HasFDerivAt (writtenInExtChartAt I I x₀ (ψ t₀)) (mfderiv I I (ψ t₀) x₀) u₀ :=
    ((((ψ t₀).contMDiff.mdifferentiableAt (by simp)).hasMFDerivAt).2).hasFDerivAt
      (range_mem_nhds_isInteriorPoint BoundarylessManifold.isInteriorPoint)
  have hpartial : fderiv ℝ Hf ((t₀ : ℝ), u₀) ∘L ContinuousLinearMap.inr ℝ ℝ E =
      mfderiv I I (ψ t₀) x₀ :=
    ((hHat.differentiableAt (by simp)).hasFDerivAt.comp u₀
      (hasFDerivAt_prodMk_right (t₀ : ℝ) u₀)).congr_of_eventuallyEq hHt₀.symm |>.unique hψd
  have hinv : (fderiv ℝ Hf ((t₀ : ℝ), u₀) ∘L ContinuousLinearMap.inr ℝ ℝ E).IsInvertible := by
    rw [hpartial]
    exact (ψ t₀).isInvertible_mfderiv (by simp)
  have hd := hHat.hasStrictFDerivAt_fderiv (by simp)
  set φ := hd.jointImplicitFunctionOfProdDomain hinv
  have hφ₀ : φ ((t₀ : ℝ), Hf ((t₀ : ℝ), u₀)) = u₀ :=
    hd.jointImplicitFunctionOfProdDomain_apply_self hinv
  have hφd : ContDiffAt ℝ ∞ φ ((t₀ : ℝ), Hf ((t₀ : ℝ), u₀)) :=
    hd.contDiffAt_jointImplicitFunctionOfProdDomain hinv hHat
  have hφeq : ∀ᶠ q in 𝓝 ((t₀ : ℝ), Hf ((t₀ : ℝ), u₀)), Hf (q.1, φ q) = q.2 :=
    hd.eventually_apply_jointImplicitFunctionOfProdDomain hinv
  rw [hHz] at hφ₀ hφd hφeq
  -- The inverses in charts.
  have hin : ContMDiffAt ((𝓡∂ 1).prod I) 𝓘(ℝ, ℝ × E) ∞
      (fun p : unitInterval × M ↦ ((p.1 : ℝ), e' p.2)) (t₀, ψ t₀ x₀) :=
    ContMDiffAt.prodMk_space (contMDiff_subtypeVal_Icc.comp contMDiff_fst).contMDiffAt
      ((contMDiffAt_extChartAt (x := ψ t₀ x₀)).comp (t₀, ψ t₀ x₀) contMDiffAt_snd)
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I ∞ e.symm (φ ((t₀ : ℝ), e' (ψ t₀ x₀))) := by
    rw [hφ₀]
    exact (contMDiffOn_extChartAt_symm x₀).contMDiffAt (mem_of_superset (hU.mem_nhds hu₀)
      fun u hu ↦ (hmaps t₀ ht₀ u hu).1)
  have hg : ContMDiffAt ((𝓡∂ 1).prod I) I ∞
      (fun p : unitInterval × M ↦ e.symm (φ ((p.1 : ℝ), e' p.2))) (t₀, ψ t₀ x₀) :=
    hsymm.comp (t₀, ψ t₀ x₀) (hφd.contMDiffAt.comp (t₀, ψ t₀ x₀) hin)
  refine hg.congr_of_eventuallyEq ?_
  -- Near `(t₀, ψ_{t₀} x₀)`, the solution computes `ψ_s⁻¹` in charts.
  have hnear : ∀ᶠ q in 𝓝 ((t₀ : ℝ), e' (ψ t₀ x₀)), Hf (q.1, φ q) = q.2 ∧ φ q ∈ U :=
    hφeq.and (hφd.continuousAt.preimage_mem_nhds (hφ₀ ▸ hU.mem_nhds hu₀))
  filter_upwards [hin.continuousAt.eventually hnear,
    continuous_snd.continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds (I := I) (ψ t₀ x₀)),
    continuous_fst.continuousAt.preimage_mem_nhds hnhds] with p ⟨hpH, hpU⟩ hpe hpab
  have heq := e'.injOn (hmaps p.1 hpab _ hpU).2 hpe ((hHG' hpab hpU).symm.trans hpH)
  exact (congrArg (ψ p.1).symm heq).symm.trans ((ψ p.1).symm_apply_apply _)

/-- On a finite-dimensional boundaryless manifold, the inverses of a jointly smooth family of
diffeomorphisms over `[0, 1]` are jointly smooth: `(t, y) ↦ ψ_t⁻¹ y` is smooth on
`unitInterval × M`. -/
theorem Diffeomorph.contMDiff_symm_eval_unitInterval {ψ : unitInterval → M ≃ₘ⟮I, I⟯ M}
    (hψ : ContMDiff ((𝓡∂ 1).prod I) I ∞ (fun p : unitInterval × M ↦ ψ p.1 p.2)) :
    ContMDiff ((𝓡∂ 1).prod I) I ∞ (fun p : unitInterval × M ↦ (ψ p.1).symm p.2) := by
  rintro ⟨t₀, y₀⟩
  obtain ⟨x₀, rfl⟩ := (ψ t₀).surjective y₀
  exact Diffeomorph.contMDiffAt_symm_eval_unitInterval hψ t₀ x₀

end SymmEval

namespace TauCeti.Diffeotopy

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [BoundarylessManifold I M]
  (ψ : unitInterval → M ≃ₘ⟮I, I⟯ M)
  (hψ : ContMDiff ((𝓡∂ 1).prod I) I ∞ (fun p : unitInterval × M ↦ ψ p.1 p.2))
  (h₀ : ∀ x, ψ 0 x = x)

/-- The diffeotopy `(t, x) ↦ ψ_t x` of a jointly smooth family `ψ` of diffeomorphisms over
`[0, 1]` with `ψ 0 = id`. Its inverse is jointly smooth by
`Diffeomorph.contMDiff_symm_eval_unitInterval`. -/
def ofContMDiff : Diffeotopy I ∞ M where
  toDiffeomorph :=
    { toFun := fun p ↦ (p.1, ψ p.1 p.2)
      invFun := fun p ↦ (p.1, (ψ p.1).symm p.2)
      left_inv := fun p ↦ by simp
      right_inv := fun p ↦ by simp
      contMDiff_toFun := contMDiff_fst.prodMk hψ
      contMDiff_invFun := contMDiff_fst.prodMk (Diffeomorph.contMDiff_symm_eval_unitInterval hψ) }
  fst_apply _ := rfl
  snd_apply_zero' := h₀

/-- The diffeotopy `ofContMDiff ψ hψ h₀` sends `(t, x)` to `ψ_t x`. -/
@[simp]
theorem ofContMDiff_apply (p : unitInterval × M) : ofContMDiff ψ hψ h₀ p = ψ p.1 p.2 :=
  (rfl)

/-- The time-`t` slice of `ofContMDiff ψ hψ h₀` is `ψ_t`. -/
@[simp]
theorem timeSlice_ofContMDiff (t : unitInterval) : (ofContMDiff ψ hψ h₀).timeSlice t = ψ t :=
  Diffeomorph.ext fun x ↦ by rw [timeSlice_apply, ofContMDiff_apply]

/-- The inverse of the level-preserving diffeomorphism of `ofContMDiff ψ hψ h₀` sends `(t, y)` to
`(t, ψ_t⁻¹ y)`. -/
@[simp]
theorem toDiffeomorph_symm_ofContMDiff_apply (p : unitInterval × M) :
    (ofContMDiff ψ hψ h₀).toDiffeomorph.symm p = (p.1, (ψ p.1).symm p.2) :=
  (rfl)

/-- The inverse of `ofContMDiff ψ hψ h₀` sends `(t, y)` to `ψ_t⁻¹ y`. -/
theorem symm_ofContMDiff_apply (p : unitInterval × M) :
    (ofContMDiff ψ hψ h₀).symm p = (ψ p.1).symm p.2 := by
  rw [symm_apply, toDiffeomorph_symm_ofContMDiff_apply]

/-- The final map of `ofContMDiff ψ hψ h₀` is `ψ_1`. -/
@[simp]
theorem final_ofContMDiff : (ofContMDiff ψ hψ h₀).final = ψ 1 := by
  rw [final_def, timeSlice_ofContMDiff]

/-- On the restriction to `[0, 1]` of a jointly smooth family `φ` over `ℝ`, the constructor
`ofContMDiff` agrees with `ofReal`. -/
theorem ofContMDiff_eq_ofReal (φ : ℝ → M ≃ₘ⟮I, I⟯ M)
    (hφ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M ↦ φ p.1 p.2)) (hφ₀ : ∀ x, φ 0 x = x)
    (hφ' : ContMDiff ((𝓡∂ 1).prod I) I ∞ (fun p : unitInterval × M ↦ φ p.1 p.2))
    (hφ₀' : ∀ x, φ ((0 : unitInterval) : ℝ) x = x) :
    ofContMDiff (fun t : unitInterval ↦ φ t) hφ' hφ₀' = ofReal φ hφ hφ₀ :=
  ext fun p ↦ by rw [ofContMDiff_apply, ofReal_apply]

end TauCeti.Diffeotopy

end
