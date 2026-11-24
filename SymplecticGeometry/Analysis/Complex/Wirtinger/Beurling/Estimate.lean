/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Beurling.Cauchy
public import TauCeti.Analysis.Normed.Operator.ComplexLinearPart
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import TauCeti.Analysis.Sobolev.Mollification.Basic
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
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
The absorption step is `MeasureTheory.one_sub_mul_eLpNorm_le_eLpNorm_add_smul`, and the passage
to the limit `MeasureTheory.eLpNorm_le_eLpNorm_of_tendsto`.

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
  -- Mollify `v` by normalized bumps of radius `1 / (n + 1)`.
  let φ : ℕ → ContDiffBump (0 : ℂ) := fun n ↦
    ⟨1 / ((n : ℝ) + 2), 1 / ((n : ℝ) + 1), by positivity,
      one_div_lt_one_div_of_lt (by positivity) (by linarith)⟩
  have hφ : Tendsto (fun n ↦ (φ n).rOut) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let w : ℕ → ℂ → F := fun n ↦ v ⋆[(lsmul ℝ ℝ).flip, volume] (φ n).normed volume
  have hw (n : ℕ) : ContDiff ℝ ∞ (w n) :=
    (φ n).hasCompactSupport_normed.contDiff_convolution_right _ hvl (φ n).contDiff_normed
  have hwc (n : ℕ) : HasCompactSupport (w n) := hv.convolution _ (φ n).hasCompactSupport_normed
  have hdw (n : ℕ) : fderiv ℝ (w n) = (φ n).normed volume ⋆[lsmul ℝ ℝ, volume] D := by
    ext1 z
    rw [h.fderiv_convolution_right hvl hDl _ (φ n).contDiff_normed (φ n).hasCompactSupport_normed
      z fun _ _ ↦ trivial, convolution_flip]
  have hconv := tendsto_eLpNorm_normed_convolution_sub (by norm_num) hφ hD
  have hdc (n : ℕ) : Continuous (fderiv ℝ (w n)) := (hw n).continuous_fderiv (by simp)
  have hP : Continuous fun A : ℂ →L[ℝ] F ↦ A.complexLinearPart 1 :=
    continuous_complexLinearPart.clm_apply continuous_const
  have hQ := continuous_complexAntilinearPart_apply (E := ℂ) (F := F) 1
  refine eLpNorm_le_eLpNorm_of_tendsto one_le_two
    (a' := fun n z ↦ (fderiv ℝ (w n) z).complexLinearPart 1)
    (b' := fun n z ↦ (fderiv ℝ (w n) z).complexAntilinearPart 1) (fun n ↦ ?_) ?_ ?_
  · have hcoe : ⇑((hwc n).toSchwartzMap (hw n)) = w n :=
      funext (HasCompactSupport.toSchwartzMap_toFun _ _)
    have := eLpNorm_wirtingerDeriv_le_eLpNorm_conjWirtingerDeriv ((hwc n).toSchwartzMap (hw n))
    simpa only [hcoe, wirtingerDeriv_eq_complexLinearPart,
      conjWirtingerDeriv_eq_complexAntilinearPart] using this
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconv (fun _ ↦ zero_le)
      fun n ↦ eLpNorm_mono ((hP.comp (hdc n)).aestronglyMeasurable.sub
        (hP.comp_aestronglyMeasurable hD.aestronglyMeasurable)) fun z ↦ ?_
    simp only [Pi.sub_apply, hdw]
    rw [← sub_apply, ← ContinuousLinearMap.complexLinearPart_sub]
    exact (norm_complexLinearPart_apply_le _ 1).trans_eq (by rw [norm_one, mul_one])
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconv (fun _ ↦ zero_le)
      fun n ↦ eLpNorm_mono ((hQ.comp (hdc n)).aestronglyMeasurable.sub
        (hQ.comp_aestronglyMeasurable hD.aestronglyMeasurable)) fun z ↦ ?_
    simp only [Pi.sub_apply, hdw]
    rw [← sub_apply, ← ContinuousLinearMap.complexAntilinearPart_sub]
    exact (norm_complexAntilinearPart_apply_le _ 1).trans_eq (by rw [norm_one, mul_one])

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
    hD.of_le ((continuous_complexAntilinearPart_apply 1).comp_aestronglyMeasurable
      hD.aestronglyMeasurable) (.of_forall fun z ↦ by
        simpa using norm_complexAntilinearPart_apply_le (D z) 1)
  exact one_sub_mul_eLpNorm_le_eLpNorm_add_smul one_le_two
    ((continuous_complexLinearPart.clm_apply
      (continuous_const (y := (1 : ℂ)))).comp_aestronglyMeasurable
      hD.aestronglyMeasurable)
    hμ hμm (h.eLpNorm_complexLinearPart_le_eLpNorm_complexAntilinearPart hv hD)
    hQ.eLpNorm_ne_top

end TauCeti

end
