/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Beurling.Cauchy
public import TauCeti.Analysis.Normed.Operator.ComplexLinearPart
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.Sobolev.Mollification.Basic
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import TauCeti.MeasureTheory.Function.UnifTight
import SymplecticGeometry.Analysis.Normed.Operator.ComplexLinearPart
import SymplecticGeometry.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# The `L²` estimate for `∂̄ + μ ∂` in the plane

For maps `v` from the plane to a complex Hilbert space, the `L²` Beurling transform has norm at
most one and sends `∂̄v` to `∂v`, so `‖∂v‖₂ ≤ ‖∂̄v‖₂`. A coefficient `μ` with `‖μ‖ ≤ m`
almost everywhere then changes `∂̄` by a term of norm at most `m ‖∂̄v‖₂`, which gives
`(1 - m) ‖∂̄v‖₂ ≤ ‖∂̄v + μ ∂v‖₂`; for `m < 1` this bounds `∂̄v` by `∂̄v + μ ∂v`.

## Main results

* `TauCeti.eLpNorm_wirtingerDeriv_le_eLpNorm_conjWirtingerDeriv`: `‖∂u‖₂ ≤ ‖∂̄u‖₂` for a Schwartz
  function `u`, from `TauCeti.beurlingL2_toLp_conjWirtingerDerivCLM` and
  `TauCeti.norm_beurlingL2_le`.
* `TauCeti.eLpNorm_conjWirtingerDeriv_le_of_norm_le`: the estimate for `∂̄ + μ ∂` on Schwartz
  functions.
* `TauCeti.HasWeakFDerivOn.eLpNorm_complexLinearPart_le_eLpNorm_complexAntilinearPart` and
  `TauCeti.HasWeakFDerivOn.eLpNorm_complexAntilinearPart_le_of_norm_le`: the same two estimates
  for a compactly supported `v` with a weak derivative `D ∈ L²`, where `∂v` and `∂̄v` are the
  complex-linear and complex-antilinear parts of `D`. Mollification reduces them to the
  Schwartz case.
* `ContDiff.eLpNorm_conjWirtingerDeriv_le_of_norm_le` and `ContDiff.eLpNorm_fderiv_le_of_norm_le`:
  for a compactly supported `C¹` map `v` and a coefficient with `‖μ‖ ≤ m` only on the support
  of `v`, the estimate `(1 - m) ‖∂̄v‖₂ ≤ ‖∂̄v + μ ∂v‖₂` and, for `m < 1`, the bound
  `‖Dv‖₂ ≤ 2 (1 - m)⁻¹ ‖∂̄v + μ ∂v‖₂` of the whole derivative. They follow from the previous two
  results, applied to the classical derivative (Tau Ceti's `ContDiffOn.hasWeakFDerivOn_fderiv`)
  and to the coefficient `μ` cut off outside the support of `v`, where `∂v` vanishes. The bound
  of `Dv` by `∂v` and `∂̄v` adapts the proof of Tau Ceti's
  `TauCeti.exists_eLpNorm_fderiv_cauchyTransform_le`.

The absorption step is `MeasureTheory.one_sub_mul_eLpNorm_le_eLpNorm_add_smul`, and the passage
to the limit `MeasureTheory.eLpNorm_le_eLpNorm_of_tendsto`, with Tau Ceti's
`MeasureTheory.tendsto_eLpNorm_comp_sub_comp_of_tendsto` for the convergence of `∂` and `∂̄` of
the mollified maps.

## References

* [D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix B (the Beurling transform on `L²`).
-/

public section

open MeasureTheory Complex Filter Topology ContinuousLinearMap
open scoped ENNReal NNReal SchwartzMap Convolution ContDiff

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **`‖∂u‖₂ ≤ ‖∂̄u‖₂` on Schwartz functions**: the `L²` Beurling transform, which has norm at most
one, sends `∂̄u` to `∂u`. -/
theorem eLpNorm_wirtingerDeriv_le_eLpNorm_conjWirtingerDeriv (u : 𝓢(ℂ, F)) :
    eLpNorm (fun z ↦ wirtingerDeriv (⇑u) z 1) 2 volume ≤
      eLpNorm (fun z ↦ conjWirtingerDeriv (⇑u) z 1) 2 volume := by
  have hle : ‖(SchwartzMap.wirtingerDerivCLM F u).toLp 2‖ ≤
      ‖(SchwartzMap.conjWirtingerDerivCLM F u).toLp 2‖ := by
    rw [← beurlingL2_toLp_conjWirtingerDerivCLM]
    exact ((beurlingL2 F).le_opNorm _).trans
      (mul_le_of_le_one_left (norm_nonneg _) (norm_beurlingL2_le (F := F)))
  rw [SchwartzMap.norm_toLp, SchwartzMap.norm_toLp] at hle
  rw [← funext (SchwartzMap.wirtingerDerivCLM_apply u),
    ← funext (SchwartzMap.conjWirtingerDerivCLM_apply u)]
  exact (ENNReal.toReal_le_toReal ((SchwartzMap.memLp _ 2 volume).eLpNorm_ne_top)
      ((SchwartzMap.memLp _ 2 volume).eLpNorm_ne_top)).1 hle

/-- **The estimate for `∂̄ + μ ∂` on Schwartz functions**: if `‖μ‖ ≤ m` almost everywhere, then
`(1 - m) ‖∂̄u‖₂ ≤ ‖∂̄u + μ ∂u‖₂`. -/
theorem eLpNorm_conjWirtingerDeriv_le_of_norm_le (u : 𝓢(ℂ, F)) {μ : ℂ → ℂ}
    (hμ : AEStronglyMeasurable μ volume) {m : ℝ≥0} (hμm : ∀ᵐ z, ‖μ z‖ ≤ m) :
    (1 - (m : ℝ≥0∞)) * eLpNorm (fun z ↦ conjWirtingerDeriv (⇑u) z 1) 2 volume ≤
      eLpNorm (fun z ↦ conjWirtingerDeriv (⇑u) z 1 + μ z • wirtingerDeriv (⇑u) z 1) 2 volume := by
  have hm₁ := SchwartzMap.memLp (SchwartzMap.conjWirtingerDerivCLM F u) 2 volume
  have hm₂ := SchwartzMap.memLp (SchwartzMap.wirtingerDerivCLM F u) 2 volume
  rw [funext (SchwartzMap.wirtingerDerivCLM_apply u)] at hm₂
  rw [funext (SchwartzMap.conjWirtingerDerivCLM_apply u)] at hm₁
  exact one_sub_mul_eLpNorm_le_eLpNorm_add_smul one_le_two hm₂.aestronglyMeasurable hμ hμm
    (eLpNorm_wirtingerDeriv_le_eLpNorm_conjWirtingerDeriv u) hm₁.eLpNorm_ne_top

/-- **`‖∂v‖₂ ≤ ‖∂̄v‖₂` for compactly supported `W^{1,2}` maps.** If `D` is a weak derivative of a
compactly supported `v` on the plane and `D ∈ L²`, then the `L²` norm of its complex-linear part
`∂v` is at most that of its complex-antilinear part `∂̄v`. -/
theorem HasWeakFDerivOn.eLpNorm_complexLinearPart_le_eLpNorm_complexAntilinearPart
    {v : ℂ → F} {D : ℂ → ℂ →L[ℝ] F} (h : HasWeakFDerivOn volume ⊤ v D)
    (hv : HasCompactSupport v) (hD : MemLp D 2 volume) :
    eLpNorm (fun z ↦ (D z).complexLinearPart 1) 2 volume ≤
      eLpNorm (fun z ↦ (D z).complexAntilinearPart 1) 2 volume := by
  have hvl : LocallyIntegrable v volume := locallyIntegrableOn_univ.1 h.locallyIntegrableOn
  have hDl : LocallyIntegrable D volume := hD.locallyIntegrable one_le_two
  -- Mollify `v` by Tau Ceti's shrinking normalized bumps.
  let φ : ℕ → ContDiffBump (0 : ℂ) := ContDiffBump.shrinking one_pos
  let w : ℕ → ℂ → F := fun n ↦ v ⋆[(lsmul ℝ ℝ).flip, volume] (φ n).normed volume
  have hw (n : ℕ) : ContDiff ℝ ∞ (w n) :=
    (φ n).hasCompactSupport_normed.contDiff_convolution_right _ hvl (φ n).contDiff_normed
  have hwc (n : ℕ) : HasCompactSupport (w n) := hv.convolution _ (φ n).hasCompactSupport_normed
  have hdw (n : ℕ) : fderiv ℝ (w n) = (φ n).normed volume ⋆[lsmul ℝ ℝ, volume] D := by
    ext1 z
    rw [h.fderiv_convolution_right hvl hDl _ (φ n).contDiff_normed (φ n).hasCompactSupport_normed
      z fun _ _ ↦ trivial, convolution_flip]
  have hconv :=
    tendsto_eLpNorm_normed_convolution_sub (by norm_num) (ContDiffBump.tendsto_rOut_shrinking
      (c := (0 : ℂ)) one_pos) hD
  have hdm (n : ℕ) : MemLp (fderiv ℝ (w n)) 2 volume :=
    ((hw n).continuous_fderiv (by simp)).memLp_of_hasCompactSupport ((hwc n).fderiv (𝕜 := ℝ))
  have hconv' : Tendsto (fun n ↦ eLpNorm (fderiv ℝ (w n) - D) 2 volume) atTop (𝓝 0) := by
    simpa only [hdw] using hconv
  -- A continuous `P` with `‖P A‖ ≤ ‖A‖` keeps the convergence of `D w n → D`.
  have hlim (P : (ℂ →L[ℝ] F) → F) (hPc : Continuous P) (hPn : ∀ A, ‖P A‖ ≤ ‖A‖) :
      Tendsto (fun n ↦ eLpNorm (P ∘ fderiv ℝ (w n) - P ∘ D) 2 volume) atTop (𝓝 0) :=
    tendsto_eLpNorm_comp_sub_comp_of_tendsto one_le_two (by norm_num) hPc hPn hdm hD hconv'
  refine eLpNorm_le_eLpNorm_of_tendsto one_le_two
    (a' := fun n z ↦ (fderiv ℝ (w n) z).complexLinearPart 1)
    (b' := fun n z ↦ (fderiv ℝ (w n) z).complexAntilinearPart 1) (.of_forall fun n ↦ ?_)
    (hlim (fun A ↦ A.complexLinearPart 1)
      ((continuous_eval_const 1).comp continuous_complexLinearPart)
      fun A ↦ (norm_complexLinearPart_apply_le A 1).trans_eq (by rw [norm_one, mul_one]))
    (hlim (fun A ↦ A.complexAntilinearPart 1)
      ((continuous_eval_const 1).comp continuous_complexAntilinearPart)
      fun A ↦ (norm_complexAntilinearPart_apply_le A 1).trans_eq (by rw [norm_one, mul_one]))
  have hcoe : ⇑((hwc n).toSchwartzMap (hw n)) = w n :=
    funext (HasCompactSupport.toSchwartzMap_toFun _ _)
  have := eLpNorm_wirtingerDeriv_le_eLpNorm_conjWirtingerDeriv ((hwc n).toSchwartzMap (hw n))
  simpa only [hcoe, wirtingerDeriv_eq_complexLinearPart,
    conjWirtingerDeriv_eq_complexAntilinearPart] using this

/-- **The estimate for `∂̄ + μ ∂` on compactly supported `W^{1,2}` maps.** If `D ∈ L²` is a weak
derivative of a compactly supported `v` on the plane and `‖μ‖ ≤ m` almost everywhere, then
`(1 - m) ‖∂̄v‖₂ ≤ ‖∂̄v + μ ∂v‖₂`, where `∂v` and `∂̄v` are the complex-linear and
complex-antilinear parts of `D`. -/
theorem HasWeakFDerivOn.eLpNorm_complexAntilinearPart_le_of_norm_le
    {v : ℂ → F} {D : ℂ → ℂ →L[ℝ] F} (h : HasWeakFDerivOn volume ⊤ v D)
    (hv : HasCompactSupport v) (hD : MemLp D 2 volume) {μ : ℂ → ℂ}
    (hμ : AEStronglyMeasurable μ volume) {m : ℝ≥0} (hμm : ∀ᵐ z, ‖μ z‖ ≤ m) :
    (1 - (m : ℝ≥0∞)) * eLpNorm (fun z ↦ (D z).complexAntilinearPart 1) 2 volume ≤
      eLpNorm (fun z ↦ (D z).complexAntilinearPart 1 + μ z • (D z).complexLinearPart 1) 2
        volume := by
  have hQ : MemLp (fun z ↦ (D z).complexAntilinearPart 1) 2 volume :=
    hD.of_le (((continuous_eval_const 1).comp
      continuous_complexAntilinearPart).comp_aestronglyMeasurable hD.aestronglyMeasurable)
      (.of_forall fun z ↦ by
        simpa using norm_complexAntilinearPart_apply_le (D z) 1)
  exact one_sub_mul_eLpNorm_le_eLpNorm_add_smul one_le_two
    (((continuous_eval_const 1).comp
      continuous_complexLinearPart).comp_aestronglyMeasurable hD.aestronglyMeasurable)
    hμ hμm (h.eLpNorm_complexLinearPart_le_eLpNorm_complexAntilinearPart hv hD)
    hQ.eLpNorm_ne_top


/-- **The estimate for `∂̄ + μ ∂` on compactly supported `C¹` maps.** If `v` is a compactly
supported `C¹` map on the plane and `‖μ‖ ≤ m` on the topological support of `v`, then
`(1 - m) ‖∂̄v‖₂ ≤ ‖∂̄v + μ ∂v‖₂`. Off the support of `v` the coefficient `μ` is arbitrary, since
`∂v` vanishes there. -/
theorem _root_.ContDiff.eLpNorm_conjWirtingerDeriv_le_of_norm_le {v : ℂ → F}
    (hv : ContDiff ℝ 1 v) (hc : HasCompactSupport v) {μ : ℂ → ℂ}
    (hμ : AEStronglyMeasurable μ volume) {m : ℝ≥0} (hμm : ∀ z ∈ tsupport v, ‖μ z‖ ≤ m) :
    (1 - (m : ℝ≥0∞)) * eLpNorm (fun z ↦ conjWirtingerDeriv v z 1) 2 volume ≤
      eLpNorm (fun z ↦ conjWirtingerDeriv v z 1 + μ z • wirtingerDeriv v z 1) 2 volume := by
  have hν : AEStronglyMeasurable ((tsupport v).indicator μ) volume :=
    hμ.indicator (isClosed_tsupport v).measurableSet
  have hνm : ∀ᵐ z, ‖(tsupport v).indicator μ z‖ ≤ m := .of_forall fun z ↦ by
    by_cases hz : z ∈ tsupport v
    · simpa [Set.indicator_of_mem hz] using hμm z hz
    · simp [Set.indicator_of_notMem hz]
  have heq : (fun z ↦ conjWirtingerDeriv v z 1 + (tsupport v).indicator μ z •
      wirtingerDeriv v z 1) = fun z ↦ conjWirtingerDeriv v z 1 + μ z • wirtingerDeriv v z 1 := by
    ext z
    by_cases hz : z ∈ tsupport v
    · rw [Set.indicator_of_mem hz]
    · simp [Set.indicator_of_notMem hz, wirtingerDeriv_eq_complexLinearPart,
        fderiv_of_notMem_tsupport (𝕜 := ℝ) hz]
  have hD : MemLp (fderiv ℝ v) 2 volume :=
    (hv.continuous_fderiv one_ne_zero).memLp_of_hasCompactSupport (hc.fderiv (𝕜 := ℝ))
  have := (hv.contDiffOn (s := Set.univ)).hasWeakFDerivOn_fderiv (μ := volume) (Ω := ⊤)
    |>.eLpNorm_complexAntilinearPart_le_of_norm_le hc hD hν hνm
  simpa only [← wirtingerDeriv_eq_complexLinearPart, ← conjWirtingerDeriv_eq_complexAntilinearPart,
    heq] using this

/-- **The bound of the whole derivative by `∂̄ + μ ∂`.** If `v` is a compactly supported `C¹` map
on the plane and `‖μ‖ ≤ m < 1` on the topological support of `v`, then
`‖Dv‖₂ ≤ 2 (1 - m)⁻¹ ‖∂̄v + μ ∂v‖₂`. -/
theorem _root_.ContDiff.eLpNorm_fderiv_le_of_norm_le {v : ℂ → F}
    (hv : ContDiff ℝ 1 v) (hc : HasCompactSupport v) {μ : ℂ → ℂ}
    (hμ : AEStronglyMeasurable μ volume) {m : ℝ≥0} (hm : m < 1)
    (hμm : ∀ z ∈ tsupport v, ‖μ z‖ ≤ m) :
    eLpNorm (fderiv ℝ v) 2 volume ≤ 2 * (1 - (m : ℝ≥0∞))⁻¹ *
      eLpNorm (fun z ↦ conjWirtingerDeriv v z 1 + μ z • wirtingerDeriv v z 1) 2 volume := by
  have hdv : Continuous (fderiv ℝ v) := hv.continuous_fderiv one_ne_zero
  have hD : MemLp (fderiv ℝ v) 2 volume := hdv.memLp_of_hasCompactSupport (hc.fderiv (𝕜 := ℝ))
  have hw : Continuous fun z ↦ wirtingerDeriv v z 1 := hv.continuous_wirtingerDeriv_apply 1
  have hcw : Continuous fun z ↦ conjWirtingerDeriv v z 1 :=
    hv.continuous_conjWirtingerDeriv_apply 1
  have hle : eLpNorm (fun z ↦ wirtingerDeriv v z 1) 2 volume ≤
      eLpNorm (fun z ↦ conjWirtingerDeriv v z 1) 2 volume := by
    simpa only [← wirtingerDeriv_eq_complexLinearPart,
      ← conjWirtingerDeriv_eq_complexAntilinearPart] using
      (hv.contDiffOn (s := Set.univ)).hasWeakFDerivOn_fderiv (μ := volume) (Ω := ⊤)
        |>.eLpNorm_complexLinearPart_le_eLpNorm_complexAntilinearPart hc hD
  have hm₀ : (1 - (m : ℝ≥0∞)) ≠ 0 := (tsub_pos_of_lt (by exact_mod_cast hm)).ne'
  have habs : eLpNorm (fun z ↦ conjWirtingerDeriv v z 1) 2 volume ≤ (1 - (m : ℝ≥0∞))⁻¹ *
      eLpNorm (fun z ↦ conjWirtingerDeriv v z 1 + μ z • wirtingerDeriv v z 1) 2 volume := by
    rw [← ENNReal.div_eq_inv_mul, ENNReal.le_div_iff_mul_le (.inl hm₀) (.inl (by simp)), mul_comm]
    exact hv.eLpNorm_conjWirtingerDeriv_le_of_norm_le hc hμ hμm
  calc eLpNorm (fderiv ℝ v) 2 volume
      ≤ eLpNorm (fun z ↦ ‖wirtingerDeriv v z 1‖ + ‖conjWirtingerDeriv v z 1‖) 2 volume :=
        eLpNorm_mono_real hdv.aestronglyMeasurable
          (norm_fderiv_le_norm_wirtingerDeriv_add_norm_conjWirtingerDeriv v)
    _ ≤ eLpNorm (fun z ↦ wirtingerDeriv v z 1) 2 volume +
          eLpNorm (fun z ↦ conjWirtingerDeriv v z 1) 2 volume := by
        refine (eLpNorm_add_le (f := fun z ↦ ‖wirtingerDeriv v z 1‖)
          (g := fun z ↦ ‖conjWirtingerDeriv v z 1‖) one_le_two).trans_eq ?_
        rw [eLpNorm_norm _ hw.aestronglyMeasurable, eLpNorm_norm _ hcw.aestronglyMeasurable]
    _ ≤ 2 * eLpNorm (fun z ↦ conjWirtingerDeriv v z 1) 2 volume := by
        rw [two_mul]
        gcongr
    _ ≤ 2 * (1 - (m : ℝ≥0∞))⁻¹ *
          eLpNorm (fun z ↦ conjWirtingerDeriv v z 1 + μ z • wirtingerDeriv v z 1) 2 volume := by
        rw [mul_assoc]
        gcongr

end TauCeti

end
