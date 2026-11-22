/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Distribution.SmulLeft
public import Mathlib.MeasureTheory.Measure.Haar.Basic
import TauCeti.Analysis.Calculus.LineDeriv.IntegrationByParts
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Distribution.TestFunction.SmulLeft

/-!
# Distributions of functions under derivatives and multiplication

For a function `f` on an open set `Ω`, Mathlib's `Distribution.ofFun Ω f μ` is the distribution
`φ ↦ ∫ φ • f ∂μ`. This file computes two operations on it:

* `Distribution.lineDerivOp_ofFun`: if `f` is `C¹` on `Ω` and `μ` is an additive Haar measure,
  the derivative along `v` of the distribution of `f` is the distribution of the derivative
  `x ↦ fderiv ℝ f x v`. This is integration by parts against test functions, by Tau Ceti's
  `TauCeti.integral_bilinear_fderiv_right_eq_neg_left_of_hasCompactSupport`.
* `Distribution.smulLeftCLM_ofFun`: if `f` is locally integrable on `Ω`, the product of its
  distribution with a smooth function `g` is the distribution of `g • f`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §3.1 (derivatives of
  distributions; the derivative of a `C¹` function is its classical derivative).
-/

public section

open MeasureTheory TopologicalSpace
open scoped Distributions LineDeriv ContDiff

namespace Distribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens E} {μ : Measure E} {f : E → F}

/-- The derivative along `v` of the distribution of a function `f` that is `C¹` on `Ω` is the
distribution of its derivative `x ↦ fderiv ℝ f x v`, for an additive Haar measure. -/
theorem lineDerivOp_ofFun [μ.IsAddHaarMeasure] (hf : ContDiffOn ℝ 1 f Ω) (v : E) :
    ∂_{v} (ofFun Ω f μ ⊤) = ofFun Ω (fun x ↦ fderiv ℝ f x v) μ ⊤ := by
  ext φ
  have hf' : LocallyIntegrableOn f Ω μ :=
    hf.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet
  have hdf : LocallyIntegrableOn (fun x ↦ fderiv ℝ f x v) Ω μ :=
    ((hf.continuousOn_fderiv_of_isOpen Ω.isOpen le_rfl).clm_apply
      continuousOn_const).locallyIntegrableOn Ω.isOpen.measurableSet
  rw [lineDerivOp_apply_apply, map_neg, ofFun_apply hf', ofFun_apply hdf]
  have := TauCeti.integral_bilinear_fderiv_right_eq_neg_left_of_hasCompactSupport (μ := μ)
    (ContinuousLinearMap.lsmul ℝ ℝ).flip (f := f) (g := φ)
    (fun x hx ↦ hf.contDiffAt (Ω.isOpen.mem_nhds (φ.tsupport_subset hx)))
    (φ.contDiff.of_le (by simp)) φ.hasCompactSupport v
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply] at this
  simp only [TestFunction.lineDerivOp_apply_eq_fderiv, this, neg_neg]

/-- The product of the distribution of a function `f`, locally integrable on `Ω`, with a `C^n`
function `g` is the distribution of `g • f`. -/
theorem smulLeftCLM_ofFun {n : ℕ∞} {g : E → ℝ} (hg : ContDiff ℝ n g)
    (hf : LocallyIntegrableOn f Ω μ) :
    smulLeftCLM hg (ofFun Ω f μ n) = ofFun Ω (fun x ↦ g x • f x) μ n := by
  ext φ
  have hgf : LocallyIntegrableOn (fun x ↦ g x • f x) Ω μ :=
    hf.continuousOn_smul Ω.isOpen.isLocallyClosed hg.continuous.continuousOn
  rw [smulLeftCLM_apply, ofFun_apply hf, ofFun_apply hgf]
  simp [TestFunction.smulLeftCLM_apply, smul_smul, mul_comm]

end Distribution

end
