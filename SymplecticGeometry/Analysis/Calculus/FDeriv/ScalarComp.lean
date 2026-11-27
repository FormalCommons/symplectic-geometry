/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import TauCeti.Analysis.Calculus.SecondDerivative

/-!
# The second derivative of a function of one variable composed with a scalar function

For `f : E → 𝕜` and `φ : 𝕜 → F`, both `C²`, Tau Ceti's second-order chain rule
`TauCeti.fderiv_fderiv_scalar_comp_apply` writes the second derivative of `φ ∘ f` as
`(Df v · Df w) φ''(f x) + D²f(v, w) φ'(f x)`. This file turns it into a bound on the operator
norm:

`‖D²(φ ∘ f)(x)‖ ≤ ‖φ''(f x)‖ ‖Df(x)‖² + ‖φ'(f x)‖ ‖D²f(x)‖`

(`SymplecticGeometry.norm_fderiv_fderiv_comp_le`), together with the first-order bound
`‖D(φ ∘ f)(x)‖ ≤ ‖φ'(f x)‖ ‖Df(x)‖` (`SymplecticGeometry.norm_fderiv_comp_le`).
-/

public section

namespace SymplecticGeometry

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → 𝕜} {φ : 𝕜 → F} {x : E}

/-- The derivative of `φ ∘ f`, for `φ` of one variable differentiable at `f x` and `f`
differentiable at `x`, has norm at most `‖φ'(f x)‖ ‖Df(x)‖`. -/
theorem norm_fderiv_comp_le (hφ : DifferentiableAt 𝕜 φ (f x)) (hf : DifferentiableAt 𝕜 f x) :
    ‖fderiv 𝕜 (φ ∘ f) x‖ ≤ ‖deriv φ (f x)‖ * ‖fderiv 𝕜 f x‖ := by
  rw [fderiv_comp x hφ hf, norm_deriv_eq_norm_fderiv]
  exact ContinuousLinearMap.opNorm_comp_le (fderiv 𝕜 φ (f x)) (fderiv 𝕜 f x)

/-- **The second derivative of a composite with a function of one variable.** For `φ` of one
variable `C²` at `f x` and `f` `C²` at `x`, the second derivative of `φ ∘ f` at `x` has norm at
most `‖φ''(f x)‖ ‖Df(x)‖² + ‖φ'(f x)‖ ‖D²f(x)‖`. -/
theorem norm_fderiv_fderiv_comp_le (hφ : ContDiffAt 𝕜 2 φ (f x)) (hf : ContDiffAt 𝕜 2 f x) :
    ‖fderiv 𝕜 (fderiv 𝕜 (φ ∘ f)) x‖ ≤
      ‖iteratedDeriv 2 φ (f x)‖ * ‖fderiv 𝕜 f x‖ ^ 2 +
        ‖deriv φ (f x)‖ * ‖fderiv 𝕜 (fderiv 𝕜 f) x‖ := by
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) fun v w ↦ ?_
  rw [TauCeti.fderiv_fderiv_scalar_comp_apply hφ hf]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, norm_mul]
  have h1 := (fderiv 𝕜 f x).le_opNorm v
  have h2 := (fderiv 𝕜 f x).le_opNorm w
  have h3 := (fderiv 𝕜 (fderiv 𝕜 f) x).le_opNorm₂ v w
  calc ‖fderiv 𝕜 f x v‖ * ‖fderiv 𝕜 f x w‖ * ‖iteratedDeriv 2 φ (f x)‖ +
        ‖fderiv 𝕜 (fderiv 𝕜 f) x v w‖ * ‖deriv φ (f x)‖ ≤
      (‖fderiv 𝕜 f x‖ * ‖v‖) * (‖fderiv 𝕜 f x‖ * ‖w‖) * ‖iteratedDeriv 2 φ (f x)‖ +
        (‖fderiv 𝕜 (fderiv 𝕜 f) x‖ * ‖v‖ * ‖w‖) * ‖deriv φ (f x)‖ := by gcongr
    _ = _ := by ring

end SymplecticGeometry

end
