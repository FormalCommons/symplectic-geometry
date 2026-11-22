/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Distribution.SmulLeft
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv

/-!
# The Leibniz rule for products of distributions with smooth functions

For a smooth function `g : E → ℝ`, a vector `v` and a test function or a distribution `T` on an
open set `Ω`, the derivative along `v` of the product `g T` (Tau Ceti's `TestFunction.smulLeftCLM`
and `Distribution.smulLeftCLM`) is `(∂_v g) T + g ∂_v T`:

* `TestFunction.lineDerivOp_smulLeftCLM`: the Leibniz rule for test functions;
* `Distribution.lineDerivOp_smulLeftCLM`: the Leibniz rule for distributions, its transpose.

The statements follow Tau Ceti's `TemperedDistribution.lineDerivOp_smulLeftCLM`, the Leibniz rule
for tempered distributions.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §3.1.
-/

public section

open TopologicalSpace
open scoped Distributions ContDiff LineDeriv

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E} {g : E → ℝ}

/-- The derivative of a smooth function `g` along a fixed vector `v` is smooth. -/
theorem ContDiff.fderiv_apply_const (hg : ContDiff ℝ ∞ g) (v : E) :
    ContDiff ℝ ∞ fun x ↦ fderiv ℝ g x v :=
  (hg.fderiv_right le_rfl).clm_apply contDiff_const

namespace TestFunction

variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The Leibniz rule for test functions**: `∂_v (g φ) = (∂_v g) φ + g ∂_v φ`. -/
theorem lineDerivOp_smulLeftCLM (hg : ContDiff ℝ ∞ g) (φ : 𝓓(Ω, F)) (v : E) :
    ∂_{v} (smulLeftCLM hg φ) =
      smulLeftCLM (hg.fderiv_apply_const v) φ + smulLeftCLM hg (∂_{v} φ) := by
  ext x
  have hφ : DifferentiableAt ℝ φ x := φ.contDiff.differentiable (by simp) x
  simp only [lineDerivOp_apply_eq_fderiv, coe_smulLeftCLM, add_apply, smulLeftCLM_apply]
  rw [fderiv_smul (hg.differentiable (by simp) x) hφ]
  simp [add_comm]

end TestFunction

namespace Distribution

variable [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F]

/-- **The Leibniz rule for distributions**: `∂_v (g T) = (∂_v g) T + g ∂_v T`. -/
theorem lineDerivOp_smulLeftCLM (hg : ContDiff ℝ ∞ g) (T : 𝓓'(Ω, F)) (v : E) :
    ∂_{v} (smulLeftCLM hg T) =
      smulLeftCLM (hg.fderiv_apply_const v) T + smulLeftCLM hg (∂_{v} T) := by
  ext φ
  simp only [lineDerivOp_apply_apply, smulLeftCLM_apply, add_apply,
    map_neg, TestFunction.lineDerivOp_smulLeftCLM, map_add]
  abel

end Distribution

end
