/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.Calculus.ContDiff.Comp
public import TauCeti.Analysis.Distribution.SmulLeft
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv

/-!
# The Leibniz rule for products of distributions with smooth functions

For a smooth function `g : E → ℝ`, a vector `v` and a test function or a distribution `T` on an
open set `Ω`, the derivative along `v` of the product `g T` (Tau Ceti's `TestFunction.smulLeftCLM`
and `Distribution.smulLeftCLM`) is `(∂_v g) T + g ∂_v T`:

* `TestFunction.lineDerivOp_smulLeftCLM`: the Leibniz rule for test functions;
* `Distribution.lineDerivOp_smulLeftCLM`: the Leibniz rule for distributions, its transpose.

The file also computes the derivative of `z ↦ ψ (L z) • v` for a real test function `ψ` and a
continuous linear map `L` (`TestFunction.fderiv_comp_smul_const_apply`).

The statements follow Tau Ceti's `SchwartzMap.lineDerivOp_smulLeftCLM` and
`TemperedDistribution.lineDerivOp_smulLeftCLM`, the Leibniz rules for Schwartz functions and
tempered distributions, and the proof for test functions takes the same steps as the first.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §3.1.
-/

public section

open TopologicalSpace
open scoped Distributions ContDiff LineDeriv

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E} {g : E → ℝ}

namespace TestFunction

variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The Leibniz rule for test functions**: `∂_v (g φ) = (∂_v g) φ + g ∂_v φ`. -/
theorem lineDerivOp_smulLeftCLM (hg : ContDiff ℝ ∞ g) (φ : 𝓓(Ω, F)) (v : E) :
    ∂_{v} (smulLeftCLM hg φ) =
      smulLeftCLM (hg.fderiv_apply_const le_rfl v) φ + smulLeftCLM hg (∂_{v} φ) := by
  ext x
  have hφ : DifferentiableAt ℝ φ x := φ.contDiff.differentiable (by simp) x
  simp only [lineDerivOp_apply_eq_fderiv, coe_smulLeftCLM, add_apply, smulLeftCLM_apply]
  rw [fderiv_smul (hg.differentiable (by simp) x) hφ]
  simp [add_comm]

/-- The derivative along `u` of `z ↦ ψ (L z) • v`, for a real test function `ψ` and a continuous
linear map `L`, is `(∂_{L u} ψ) (L y) • v`. -/
theorem fderiv_comp_smul_const_apply {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {Ω' : Opens E'} (L : E →L[ℝ] E') (ψ : 𝓓(Ω', ℝ)) (v : F) (y u : E) :
    fderiv ℝ (fun z ↦ ψ (L z) • v) y u = ∂_{L u} ψ (L y) • v := by
  have hψ : DifferentiableAt ℝ ψ (L y) := ψ.contDiff.differentiable (by simp) _
  have hd : HasFDerivAt (fun z ↦ ψ (L z) • v) _ y :=
    (hψ.hasFDerivAt.comp y L.hasFDerivAt).smul_const v
  rw [hd.fderiv, lineDerivOp_apply_eq_fderiv]
  simp

end TestFunction

namespace Distribution

variable [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F]

/-- **The Leibniz rule for distributions**: `∂_v (g T) = (∂_v g) T + g ∂_v T`. -/
theorem lineDerivOp_smulLeftCLM (hg : ContDiff ℝ ∞ g) (T : 𝓓'(Ω, F)) (v : E) :
    ∂_{v} (smulLeftCLM hg T) =
      smulLeftCLM (hg.fderiv_apply_const le_rfl v) T + smulLeftCLM hg (∂_{v} T) := by
  ext φ
  simp only [lineDerivOp_apply_apply, smulLeftCLM_apply, add_apply,
    map_neg, TestFunction.lineDerivOp_smulLeftCLM, map_add]
  abel

end Distribution

end
