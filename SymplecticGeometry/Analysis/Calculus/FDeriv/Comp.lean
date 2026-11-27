/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Calculus.SecondDerivative

/-!
# Norms of the derivatives of a composite

For `g : F → G` and `f : E → F`, both `C²`, Tau Ceti's second-order chain rule
`TauCeti.fderiv_fderiv_comp_apply` writes the second derivative of `g ∘ f` as
`D²g(f x)(Df v, Df w) + Dg(f x)(D²f(v, w))`. This file turns it into a bound on the operator
norm:

`‖D²(g ∘ f)(x)‖ ≤ ‖D²g(f x)‖ ‖Df(x)‖² + ‖Dg(f x)‖ ‖D²f(x)‖`

(`SymplecticGeometry.norm_fderiv_fderiv_comp_le`).

When `f : E → 𝕜` is scalar and `φ : 𝕜 → F` is a function of one variable, the derivative of
`φ ∘ f` is `(Df x).smulRight (φ'(f x))` (`SymplecticGeometry.fderiv_scalar_comp`), so its norm
is `‖φ'(f x)‖ ‖Df(x)‖` (`SymplecticGeometry.norm_fderiv_scalar_comp`); and the bound above, read
with Tau Ceti's `TauCeti.norm_fderiv_fderiv` and Mathlib's
`norm_iteratedFDeriv_eq_norm_iteratedDeriv`, becomes
`‖D²(φ ∘ f)(x)‖ ≤ ‖φ''(f x)‖ ‖Df(x)‖² + ‖φ'(f x)‖ ‖D²f(x)‖`
(`SymplecticGeometry.norm_fderiv_fderiv_scalar_comp_le`), the norm form of Tau Ceti's
`TauCeti.fderiv_fderiv_scalar_comp_apply`.

Finally, if `g` is a left inverse of `h` near `x`, and `T` has the same value and derivative as
`h` at `x`, then `g ∘ T` has derivative the identity at `x`
(`SymplecticGeometry.fderiv_comp_eq_id_of_eventuallyEq_id`).
-/

public section

namespace SymplecticGeometry

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G]
  [NormedSpace 𝕜 G] {x : E}

/-- **The second derivative of a composite.** For `g` `C²` at `f x` and `f` `C²` at `x`, the
second derivative of `g ∘ f` at `x` has norm at most
`‖D²g(f x)‖ ‖Df(x)‖² + ‖Dg(f x)‖ ‖D²f(x)‖`. -/
theorem norm_fderiv_fderiv_comp_le {g : F → G} {f : E → F} (hg : ContDiffAt 𝕜 2 g (f x))
    (hf : ContDiffAt 𝕜 2 f x) :
    ‖fderiv 𝕜 (fderiv 𝕜 (g ∘ f)) x‖ ≤
      ‖fderiv 𝕜 (fderiv 𝕜 g) (f x)‖ * ‖fderiv 𝕜 f x‖ ^ 2 +
        ‖fderiv 𝕜 g (f x)‖ * ‖fderiv 𝕜 (fderiv 𝕜 f) x‖ := by
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) fun v w ↦ ?_
  rw [TauCeti.fderiv_fderiv_comp_apply hg hf]
  refine (norm_add_le _ _).trans ?_
  have h1 := (fderiv 𝕜 f x).le_opNorm v
  have h2 := (fderiv 𝕜 f x).le_opNorm w
  have h3 := (fderiv 𝕜 (fderiv 𝕜 g) (f x)).le_opNorm₂ (fderiv 𝕜 f x v) (fderiv 𝕜 f x w)
  have h4 := (fderiv 𝕜 g (f x)).le_opNorm (fderiv 𝕜 (fderiv 𝕜 f) x v w)
  have h5 := (fderiv 𝕜 (fderiv 𝕜 f) x).le_opNorm₂ v w
  calc _ ≤ ‖fderiv 𝕜 (fderiv 𝕜 g) (f x)‖ * ‖fderiv 𝕜 f x v‖ * ‖fderiv 𝕜 f x w‖ +
        ‖fderiv 𝕜 g (f x)‖ * ‖fderiv 𝕜 (fderiv 𝕜 f) x v w‖ := add_le_add h3 h4
    _ ≤ ‖fderiv 𝕜 (fderiv 𝕜 g) (f x)‖ * (‖fderiv 𝕜 f x‖ * ‖v‖) * (‖fderiv 𝕜 f x‖ * ‖w‖) +
        ‖fderiv 𝕜 g (f x)‖ * (‖fderiv 𝕜 (fderiv 𝕜 f) x‖ * ‖v‖ * ‖w‖) := by gcongr
    _ = _ := by ring

variable {f : E → 𝕜} {φ : 𝕜 → F}

/-- The derivative of `φ ∘ f`, for `φ` of one variable differentiable at `f x` and `f : E → 𝕜`
differentiable at `x`, is `Df(x)` scaled by `φ'(f x)`. -/
theorem fderiv_scalar_comp (hφ : DifferentiableAt 𝕜 φ (f x)) (hf : DifferentiableAt 𝕜 f x) :
    fderiv 𝕜 (φ ∘ f) x = (fderiv 𝕜 f x).smulRight (deriv φ (f x)) := by
  rw [fderiv_comp x hφ hf, ← toSpanSingleton_deriv, ContinuousLinearMap.toSpanSingleton_comp]

/-- The derivative of `φ ∘ f`, for `φ` of one variable differentiable at `f x` and `f : E → 𝕜`
differentiable at `x`, has norm `‖φ'(f x)‖ ‖Df(x)‖`. -/
theorem norm_fderiv_scalar_comp (hφ : DifferentiableAt 𝕜 φ (f x))
    (hf : DifferentiableAt 𝕜 f x) :
    ‖fderiv 𝕜 (φ ∘ f) x‖ = ‖deriv φ (f x)‖ * ‖fderiv 𝕜 f x‖ := by
  rw [fderiv_scalar_comp hφ hf, ContinuousLinearMap.norm_smulRight_apply, mul_comm]

/-- **The second derivative of a composite with a function of one variable.** For `φ` of one
variable `C²` at `f x` and `f : E → 𝕜` `C²` at `x`, the second derivative of `φ ∘ f` at `x` has
norm at most `‖φ''(f x)‖ ‖Df(x)‖² + ‖φ'(f x)‖ ‖D²f(x)‖`. -/
theorem norm_fderiv_fderiv_scalar_comp_le (hφ : ContDiffAt 𝕜 2 φ (f x))
    (hf : ContDiffAt 𝕜 2 f x) :
    ‖fderiv 𝕜 (fderiv 𝕜 (φ ∘ f)) x‖ ≤
      ‖iteratedDeriv 2 φ (f x)‖ * ‖fderiv 𝕜 f x‖ ^ 2 +
        ‖deriv φ (f x)‖ * ‖fderiv 𝕜 (fderiv 𝕜 f) x‖ := by
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv, ← TauCeti.norm_fderiv_fderiv,
    norm_deriv_eq_norm_fderiv]
  exact norm_fderiv_fderiv_comp_le hφ hf

/-- Let `g : F → E` be a left inverse of `h : E → F` near `x`, differentiable at `h x`, and let
`T : E → F` have the same value and the same derivative as `h` at `x`, with `h` and `T`
differentiable at `x`. Then `g ∘ T` has derivative the identity at `x`. -/
theorem fderiv_comp_eq_id_of_eventuallyEq_id {g : F → E} {h T : E → F}
    (hg : DifferentiableAt 𝕜 g (h x)) (hh : DifferentiableAt 𝕜 h x)
    (hT : DifferentiableAt 𝕜 T x) (hTx : T x = h x) (hT' : fderiv 𝕜 T x = fderiv 𝕜 h x)
    (hgh : g ∘ h =ᶠ[nhds x] id) : fderiv 𝕜 (g ∘ T) x = ContinuousLinearMap.id 𝕜 E := by
  rw [fderiv_comp x (hTx ▸ hg) hT, hT', hTx, ← fderiv_comp x hg hh, hgh.fderiv_eq, fderiv_id]

end SymplecticGeometry

end
