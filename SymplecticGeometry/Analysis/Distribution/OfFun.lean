/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Distribution.SmulLeft
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Basic
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Distribution.TestFunction.SmulLeft
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import SymplecticGeometry.MeasureTheory.Function.LocallyIntegrable

/-!
# Distributions of functions under derivatives and multiplication

For a function `f` on an open set `Ω`, Mathlib's `Distribution.ofFun Ω f μ` is the distribution
`φ ↦ ∫ φ • f ∂μ`. This file computes some operations on it:

* `TauCeti.HasWeakLineDerivOn.lineDerivOp_ofFun`: the derivative along `v` of the distribution
  of `f` is the distribution of a weak derivative of `f` along `v`.
* `Distribution.lineDerivOp_ofFun`: if `f` is `C¹` on `Ω` and `μ` is an additive Haar measure,
  the derivative along `v` of the distribution of `f` is the distribution of the derivative
  `x ↦ fderiv ℝ f x v`, since by Tau Ceti's `ContDiffOn.hasWeakFDerivOn_fderiv` the classical
  derivative of `f` is a weak one.
* `Distribution.smulLeftCLM_ofFun`: if `f` is locally integrable on `Ω`, the product of its
  distribution with a smooth function `g` is the distribution of `g • f`.
* `Distribution.ofFun_sum`: the distribution of a finite sum of locally integrable functions is
  the sum of their distributions.
* `Distribution.ofFun_smul_measure`: multiplying the measure by `c : ℝ≥0` multiplies the
  distribution by `c`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §3.1 (derivatives of
  distributions; the derivative of a `C¹` function is its classical derivative).
-/

public section

open MeasureTheory TopologicalSpace
open scoped Distributions LineDeriv ContDiff NNReal

namespace Distribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens E} {μ : Measure E} {f : E → F}

/-- If `u'` is a weak derivative of `u` along `v` on `Ω`, the derivative along `v` of the
distribution of `u` is the distribution of `u'`. -/
theorem _root_.TauCeti.HasWeakLineDerivOn.lineDerivOp_ofFun {u u' : E → F} {v : E}
    (h : TauCeti.HasWeakLineDerivOn μ Ω u u' v) :
    ∂_{v} (ofFun Ω u μ ⊤) = ofFun Ω u' μ ⊤ := by
  ext φ
  rw [lineDerivOp_apply_apply, map_neg, ofFun_apply h.locallyIntegrableOn,
    ofFun_apply h.locallyIntegrableOn_deriv]
  simp only [TestFunction.lineDerivOp_apply, h.integral_lineDeriv_smul_eq_neg_integral_smul,
    neg_neg]

/-- The derivative along `v` of the distribution of a function `f` that is `C¹` on `Ω` is the
distribution of its derivative `x ↦ fderiv ℝ f x v`, for an additive Haar measure. -/
theorem lineDerivOp_ofFun [FiniteDimensional ℝ E] [CompleteSpace F] [μ.IsAddHaarMeasure]
    (hf : ContDiffOn ℝ 1 f Ω) (v : E) :
    ∂_{v} (ofFun Ω f μ ⊤) = ofFun Ω (fun x ↦ fderiv ℝ f x v) μ ⊤ :=
  (hf.hasWeakFDerivOn_fderiv.hasWeakLineDerivOn v).lineDerivOp_ofFun

/-- The product of the distribution of a function `f`, locally integrable on `Ω`, with a `C^n`
function `g` is the distribution of `g • f`. -/
theorem smulLeftCLM_ofFun [FiniteDimensional ℝ E] {n : ℕ∞} {g : E → ℝ} (hg : ContDiff ℝ n g)
    (hf : LocallyIntegrableOn f Ω μ) :
    smulLeftCLM hg (ofFun Ω f μ n) = ofFun Ω (fun x ↦ g x • f x) μ n := by
  ext φ
  have hgf : LocallyIntegrableOn (fun x ↦ g x • f x) Ω μ :=
    hf.continuousOn_smul Ω.isOpen.isLocallyClosed hg.continuous.continuousOn
  rw [smulLeftCLM_apply, ofFun_apply hf, ofFun_apply hgf]
  simp [TestFunction.smulLeftCLM_apply, smul_smul, mul_comm]

/-- The distribution of a finite sum of functions locally integrable on `Ω` is the sum of their
distributions. -/
theorem ofFun_sum {ι : Type*} {n : ℕ∞} (s : Finset ι) {f : ι → E → F}
    (hf : ∀ i ∈ s, LocallyIntegrableOn (f i) Ω μ) :
    ofFun Ω (fun x ↦ ∑ i ∈ s, f i x) μ n = ∑ i ∈ s, ofFun Ω (f i) μ n := by
  induction s using Finset.cons_induction with
  | empty => exact ofFun_zero
  | cons j s hj ih =>
    rw [Finset.forall_mem_cons] at hf
    rw [Finset.sum_cons, ← ih hf.2, ← ofFun_add hf.1 (locallyIntegrableOn_finsetSum s hf.2)]
    congr 1 with x
    simp

/-- The distribution of `f` for the measure `c • μ` is `c` times its distribution for `μ`. -/
@[simp]
theorem ofFun_smul_measure {n : ℕ∞} (c : ℝ≥0) :
    ofFun Ω f (c • μ) n = (c : ℝ) • ofFun Ω f μ n := by
  rcases eq_or_ne c 0 with rfl | hc
  · ext φ
    simp [ofFun_apply_eq_ite]
  have hiff : LocallyIntegrableOn f Ω (c • μ) ↔ LocallyIntegrableOn f Ω μ := by
    rw [← Measure.coe_nnreal_smul]
    exact locallyIntegrableOn_smul_measure_iff (ENNReal.coe_ne_zero.2 hc) ENNReal.coe_ne_top
  by_cases hf : LocallyIntegrableOn f Ω μ
  · ext φ
    rw [ofFun_apply (hiff.2 hf), smul_apply, ofFun_apply hf, integral_smul_nnreal_measure,
      NNReal.smul_def]
  · rw [ofFun_eq_zero hf, ofFun_eq_zero (mt hiff.1 hf), smul_zero]

end Distribution

end
