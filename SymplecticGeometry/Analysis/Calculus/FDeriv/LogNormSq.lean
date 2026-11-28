/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.InnerProductSpace.SquaredDistance
import SymplecticGeometry.Analysis.Complex.RealInner

/-!
# The first and second derivatives of `log ‖F‖²`

For a function `f : E → G` into an inner product space over `𝕜 = ℝ` or `ℂ` that is
differentiable at `x` with `f x ≠ 0`, the derivative of `z ↦ log ‖f z‖²` at `x` sends `u` to
`2 re ⟪f x, df u⟫ / ‖f x‖²` (`HasFDerivAt.log_norm_sq`, `fderiv_log_norm_sq_apply`). The proof
composes Mathlib's `HasFDerivAt.log` with `HasFDerivAt.inner`, through `z ↦ re ⟪f z, f z⟫`.

For a function `F : E → V` from a real normed space to a real inner product space that is `C²`
at `x` with `F x ≠ 0`, the second derivative of `z ↦ log ‖F z‖²` at `x` is
`2 (⟪dF u, dF w⟫ + ⟪F x, d²F(u, w)⟫) / ‖F x‖² - 4 ⟪F x, dF u⟫ ⟪F x, dF w⟫ / ‖F x‖⁴`
(`fderiv_fderiv_log_norm_sq_apply`). The proof composes Tau Ceti's second-order chain rule
through a scalar, `TauCeti.fderiv_fderiv_scalar_comp_apply`, with its derivatives of the squared
norm along a map, `TauCeti.fderiv_norm_sq_sub_comp` and
`TauCeti.fderiv_fderiv_norm_sq_sub_comp_apply`.

For `F : E → ℂ`, the sum of the second derivative over `(u, u)` and `(w, w)` is at most
`2 ‖dF u ² + dF w ²‖ / ‖F x‖² + 2 ⟪F x, d²F(u, u) + d²F(w, w)⟫ / ‖F x‖²`
(`fderiv_fderiv_log_norm_sq_add_le`): the square terms are controlled by
`Complex.norm_sq_mul_add_sub_inner_sq_le`. This is the form in which they are bounded when `w` is
the image of `u` by a complex structure, as in Auroux's estimate for the Hessian of `log |s_k|²`.

## References

* [D. Auroux, *Asymptotically holomorphic families of symplectic submanifolds*][Auroux1997],
  §5.1
-/

public section

open TauCeti

namespace SymplecticGeometry

section FirstDerivative

variable (𝕜 : Type*) {E G : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [NormedSpace ℝ G] {f : E → G} {x : E}

/-- **The derivative of `log ‖f‖²`.** If `f : E → G` has derivative `f'` at `x` and
`f x ≠ 0`, then `z ↦ log (‖f z‖ ^ 2)` has derivative `(‖f x‖ ^ 2)⁻¹ • (re ∘ D)` at `x`, where
`D` is the derivative of `z ↦ ⟪f z, f z⟫_𝕜` at `x` given by `HasFDerivAt.inner`. -/
theorem _root_.HasFDerivAt.log_norm_sq {f' : E →L[ℝ] G} (hf : HasFDerivAt f f' x)
    (hx : f x ≠ 0) :
    HasFDerivAt (fun z ↦ Real.log (‖f z‖ ^ 2))
      ((‖f x‖ ^ 2)⁻¹ • (RCLike.reCLM : 𝕜 →L[ℝ] ℝ).comp
        ((fderivInnerCLM 𝕜 (f x, f x)).comp (f'.prod f'))) x := by
  have h := (RCLike.reCLM.hasFDerivAt.comp x (hf.inner 𝕜 hf)).log (by
    simpa [Function.comp_apply, RCLike.reCLM_apply, inner_self_eq_norm_sq] using hx)
  simpa only [Function.comp_def, RCLike.reCLM_apply, inner_self_eq_norm_sq] using h

/-- **The derivative of `log ‖f‖²`, applied.** If `f : E → G` is differentiable at `x` and
`f x ≠ 0`, then the derivative of `z ↦ log (‖f z‖ ^ 2)` at `x` sends `u` to
`2 re ⟪f x, df u⟫_𝕜 / ‖f x‖²`. -/
theorem fderiv_log_norm_sq_apply (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0) (u : E) :
    fderiv ℝ (fun z ↦ Real.log (‖f z‖ ^ 2)) x u =
      2 * RCLike.re (inner 𝕜 (f x) (fderiv ℝ f x u)) / ‖f x‖ ^ 2 := by
  rw [(hf.hasFDerivAt.log_norm_sq 𝕜 hx).fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, fderivInnerCLM_apply, RCLike.reCLM_apply, smul_eq_mul,
    map_add]
  rw [← inner_conj_symm (f x) (fderiv ℝ f x u), RCLike.conj_re]
  ring

end FirstDerivative

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]

/-- **The second derivative of `log ‖F‖²`.** If `F : E → V` is `C²` at `x` and `F x ≠ 0`, then
the second derivative of `z ↦ log (‖F z‖ ^ 2)` at `x`, applied to `u` and `w`, is
`2 (⟪dF u, dF w⟫ + ⟪F x, d²F(u, w)⟫) / ‖F x‖² - 4 ⟪F x, dF u⟫ ⟪F x, dF w⟫ / ‖F x‖⁴`. -/
theorem fderiv_fderiv_log_norm_sq_apply {F : E → V} {x : E} (hF : ContDiffAt ℝ 2 F x)
    (hx : F x ≠ 0) (u w : E) :
    fderiv ℝ (fderiv ℝ fun z ↦ Real.log (‖F z‖ ^ 2)) x u w =
      2 * (inner ℝ (fderiv ℝ F x u) (fderiv ℝ F x w) +
          inner ℝ (F x) (fderiv ℝ (fderiv ℝ F) x u w)) / ‖F x‖ ^ 2 -
        4 * inner ℝ (F x) (fderiv ℝ F x u) * inner ℝ (F x) (fderiv ℝ F x w) / ‖F x‖ ^ 4 := by
  have hp : ‖F x‖ ^ 2 ≠ 0 := by positivity
  have h := fderiv_fderiv_scalar_comp_apply (f := fun z ↦ ‖F z‖ ^ 2)
    (Real.contDiffAt_log.2 hp) (ContDiffAt.norm_sq ℝ hF) u w
  have h2 := fderiv_fderiv_norm_sq_sub_comp_apply (a := 0) hF u w
  have h1 := fderiv_norm_sq_sub_comp (a := 0) (hF.differentiableAt (by norm_num))
  simp only [sub_zero] at h1 h2
  rw [Function.comp_def] at h
  rw [h, h1, h2]
  simp [Real.deriv_log', iteratedDeriv_succ]
  field_simp
  ring

/-- For `F : E → ℂ` that is `C²` at `x` with `F x ≠ 0`, the second derivative `H` of
`z ↦ log (‖F z‖ ^ 2)` at `x` satisfies
`H(u, u) + H(w, w) ≤ 2 ‖dF u ² + dF w ²‖ / ‖F x‖² + 2 ⟪F x, d²F(u, u) + d²F(w, w)⟫ / ‖F x‖²`,
for the real inner product of `ℂ`. -/
theorem fderiv_fderiv_log_norm_sq_add_le {F : E → ℂ} {x : E} (hF : ContDiffAt ℝ 2 F x)
    (hx : F x ≠ 0) (u w : E) :
    fderiv ℝ (fderiv ℝ fun z ↦ Real.log (‖F z‖ ^ 2)) x u u +
        fderiv ℝ (fderiv ℝ fun z ↦ Real.log (‖F z‖ ^ 2)) x w w ≤
      2 * ‖fderiv ℝ F x u ^ 2 + fderiv ℝ F x w ^ 2‖ / ‖F x‖ ^ 2 +
        2 * inner ℝ (F x) (fderiv ℝ (fderiv ℝ F) x u u + fderiv ℝ (fderiv ℝ F) x w w) /
          ‖F x‖ ^ 2 := by
  have : 0 < ‖F x‖ := norm_pos_iff.2 hx
  have halg := Complex.norm_sq_mul_add_sub_inner_sq_le (F x) (fderiv ℝ F x u) (fderiv ℝ F x w)
  rw [fderiv_fderiv_log_norm_sq_apply hF hx, fderiv_fderiv_log_norm_sq_apply hF hx,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, inner_add_right]
  have hsplit : ∀ A B c d c' d' : ℝ,
      2 * (A ^ 2 + c) / ‖F x‖ ^ 2 - 4 * d * d / ‖F x‖ ^ 4 +
          (2 * (B ^ 2 + c') / ‖F x‖ ^ 2 - 4 * d' * d' / ‖F x‖ ^ 4) =
        2 * (‖F x‖ ^ 2 * (A ^ 2 + B ^ 2) - 2 * (d ^ 2 + d' ^ 2)) / ‖F x‖ ^ 4 +
          2 * (c + c') / ‖F x‖ ^ 2 := by
    intros
    field_simp
    ring
  rw [hsplit, add_le_add_iff_right, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right halg (by positivity : (0 : ℝ) ≤ ‖F x‖ ^ 2)]

end SymplecticGeometry

end
