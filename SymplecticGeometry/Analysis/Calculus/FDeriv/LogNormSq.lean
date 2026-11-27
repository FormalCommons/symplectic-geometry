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
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The second derivative of `log ‖F‖²` for a complex function `F`

For a function `F : E → ℂ` on a real normed space that is `C²` at `x` with `F x ≠ 0`, the second
derivative of `z ↦ log ‖F z‖²` at `x` is
`2 (⟪dF u, dF w⟫ + ⟪F x, d²F(u, w)⟫) / ‖F x‖² - 4 ⟪F x, dF u⟫ ⟪F x, dF w⟫ / ‖F x‖⁴`,
the inner products being those of `ℂ` as a real inner product space
(`fderiv_fderiv_log_norm_sq_apply`).

The square terms of this formula, summed over two vectors, are bounded by the norm of the sum of
the squares of the two derivatives (`Complex.norm_sq_mul_add_sub_inner_sq_le`): this is how they
are controlled when the second vector is the image of the first by a complex structure, as in
Auroux's estimate for the Hessian of `log |s_k|²`.

## References

* [D. Auroux, *Asymptotically holomorphic families of symplectic submanifolds*][Auroux1997],
  §5.1
-/

public section

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The second derivative of `log ‖F‖²`.** If `F : E → ℂ` is `C²` at `x` and `F x ≠ 0`, then
the second derivative of `z ↦ log (‖F z‖ ^ 2)` at `x`, applied to `u` and `w`, is
`2 (⟪dF u, dF w⟫ + ⟪F x, d²F(u, w)⟫) / ‖F x‖² - 4 ⟪F x, dF u⟫ ⟪F x, dF w⟫ / ‖F x‖⁴`, for the
real inner product of `ℂ`. -/
theorem fderiv_fderiv_log_norm_sq_apply {F : E → ℂ} {x : E} (hF : ContDiffAt ℝ 2 F x)
    (hx : F x ≠ 0) (u w : E) :
    fderiv ℝ (fderiv ℝ fun z ↦ Real.log (‖F z‖ ^ 2)) x u w =
      2 * (inner ℝ (fderiv ℝ F x u) (fderiv ℝ F x w) +
          inner ℝ (F x) (fderiv ℝ (fderiv ℝ F) x u w)) / ‖F x‖ ^ 2 -
        4 * inner ℝ (F x) (fderiv ℝ F x u) * inner ℝ (F x) (fderiv ℝ F x w) / ‖F x‖ ^ 4 := by
  have hev : ∀ᶠ z in 𝓝 x, ContDiffAt ℝ 2 F z ∧ F z ≠ 0 :=
    (hF.eventually (by simp)).and (hF.continuousAt.eventually_ne hx)
  have hg : (fun z ↦ fderiv ℝ (fun z ↦ Real.log (‖F z‖ ^ 2)) z w) =ᶠ[𝓝 x]
      fun z ↦ (‖F z‖ ^ 2)⁻¹ * (2 * inner ℝ (F z) (fderiv ℝ F z w)) := by
    filter_upwards [hev] with z ⟨hz, hz0⟩
    rw [((hz.differentiableAt (by norm_num)).hasFDerivAt.norm_sq.log
      (by positivity)).fderiv]
    simp [mul_add]
  have hd2 : DifferentiableAt ℝ (fderiv ℝ fun z ↦ Real.log (‖F z‖ ^ 2)) x :=
    ((ContDiffAt.norm_sq ℝ hF |>.log (by positivity)).fderiv_right (m := 1)
      (by norm_num)).differentiableAt (by norm_num)
  have hF2 : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hF1 : HasFDerivAt F (fderiv ℝ F x) x :=
    (hF.differentiableAt (by norm_num)).hasFDerivAt
  rw [show fderiv ℝ (fderiv ℝ fun z ↦ Real.log (‖F z‖ ^ 2)) x u w =
      fderiv ℝ (fun z ↦ fderiv ℝ (fun z ↦ Real.log (‖F z‖ ^ 2)) z w) x u by
    rw [fderiv_clm_apply hd2 (differentiableAt_const w)]; simp, hg.fderiv_eq]
  have hin := hF1.inner ℝ (hF2.hasFDerivAt.clm_apply (hasFDerivAt_const w x))
  have hN : HasFDerivAt (fun z ↦ (‖F z‖ ^ 2)⁻¹) _ x :=
    (hasDerivAt_inv (by positivity : ‖F x‖ ^ 2 ≠ 0)).comp_hasFDerivAt x hF1.norm_sq
  have hP : HasFDerivAt (fun z ↦ (‖F z‖ ^ 2)⁻¹ * (2 * inner ℝ (F z) (fderiv ℝ F z w))) _ x :=
    hN.mul (hin.const_mul 2)
  rw [hP.fderiv]
  simp
  field_simp
  ring

/-- For complex numbers `p`, `a`, `b`,
`‖p‖² (‖a‖² + ‖b‖²) - 2 (⟪p, a⟫² + ⟪p, b⟫²) ≤ ‖p‖² ‖a² + b²‖`, for the real inner product of
`ℂ`: the left side is `-Re ((a² + b²) p̄²)`. -/
theorem Complex.norm_sq_mul_add_sub_inner_sq_le (p a b : ℂ) :
    ‖p‖ ^ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) - 2 * (inner ℝ p a ^ 2 + inner ℝ p b ^ 2) ≤
      ‖p‖ ^ 2 * ‖a ^ 2 + b ^ 2‖ := by
  have h : ‖p‖ ^ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) - 2 * (inner ℝ p a ^ 2 + inner ℝ p b ^ 2) =
      -((a ^ 2 + b ^ 2) * (starRingEnd ℂ p) ^ 2).re := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.inner, sq]
    simp
    ring
  rw [h, ← Complex.neg_re]
  calc (-((a ^ 2 + b ^ 2) * (starRingEnd ℂ p) ^ 2)).re
      ≤ ‖-((a ^ 2 + b ^ 2) * (starRingEnd ℂ p) ^ 2)‖ := Complex.re_le_norm _
    _ = ‖p‖ ^ 2 * ‖a ^ 2 + b ^ 2‖ := by simp [mul_comm]

end
