/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.Calculus.Taylor.Integral
import TauCeti.Analysis.InnerProductSpace.NormPow

/-!
# Derivatives of radial functions and of products in separate variables

Derivatives of two kinds of functions:

* a radial function `y ↦ β ‖y‖` on a real inner product space `V`. It is `Cⁿ` when `β` is `Cⁿ`
  and constant near `0` (`ContDiff.comp_norm_of_eventuallyEq_const`). Away from the origin its
  derivative along `v` is `β' (‖y‖) ⟪y, v⟫ / ‖y‖` (`fderiv_comp_norm_apply`), and its second
  derivative along the unit radial vector `‖y‖⁻¹ • y` is `β'' (‖y‖)`
  (`fderiv_fderiv_comp_norm_apply_inv_norm_smul`): along that line the norm is `‖y‖ + s`.
* a product `x ↦ g x.2 * h x.1` on `𝕜 × F`, whose derivative is
  `hasFDerivAt_comp_snd_mul_comp_fst`. Its first and second derivatives along `(1, 0)`
  involve only `h`, and those along `(0, v)` only `g`
  (`fderiv_comp_snd_mul_comp_fst_apply_one_zero`, `fderiv_comp_snd_mul_comp_fst_apply_zero`,
  `fderiv_fderiv_comp_snd_mul_comp_fst_apply_one_zero`,
  `fderiv_fderiv_comp_snd_mul_comp_fst_apply_zero`).

The smoothness of the radial function reduces to Tau Ceti's `ContDiff.comp_norm`, and its first
derivative to Tau Ceti's `hasFDerivAt_norm_of_ne` (both in
`TauCeti/Analysis/InnerProductSpace/NormPow.lean`). The second derivatives are computed along
lines with Tau Ceti's `ContDiffAt.deriv_deriv_comp_add_smul`, and on fibres of the product with
`fderiv_fderiv_slice_right_apply` and `fderiv_fderiv_const_smul`.
-/

public section

open Filter
open scoped Topology InnerProductSpace

namespace SymplecticGeometry

section Radial

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A radial function `y ↦ β ‖y‖` is `Cⁿ` on a real inner product space, the origin included,
when `β` is `Cⁿ` and constant near `0`. -/
theorem _root_.ContDiff.comp_norm_of_eventuallyEq_const {n : WithTop ℕ∞} {β : ℝ → F}
    (hβ : ContDiff ℝ n β) (h0 : β =ᶠ[𝓝 0] fun _ ↦ β 0) :
    ContDiff ℝ n fun y : V ↦ β ‖y‖ := by
  have h : 0 ∉ tsupport fun r ↦ β r - β 0 :=
    notMem_tsupport_iff_eventuallyEq.mpr (h0.mono fun r hr ↦ by simp [hr])
  simpa using ((hβ.sub contDiff_const).comp_norm (E := V) h).add (contDiff_const (c := β 0))

/-- Away from the origin, the derivative of the radial function `z ↦ β ‖z‖` at `y` along `v` is
`β' (‖y‖) ⟪y, v⟫ / ‖y‖`. -/
theorem fderiv_comp_norm_apply {β : ℝ → ℝ} {y : V} (hy : y ≠ 0)
    (hβ : DifferentiableAt ℝ β ‖y‖) (v : V) :
    fderiv ℝ (fun z : V ↦ β ‖z‖) y v = deriv β ‖y‖ * ⟪y, v⟫_ℝ / ‖y‖ := by
  have H : HasFDerivAt (fun z : V ↦ β ‖z‖) (deriv β ‖y‖ • ‖y‖⁻¹ • innerSL ℝ y) y :=
    hβ.hasDerivAt.comp_hasFDerivAt y (TauCeti.hasFDerivAt_norm_of_ne hy)
  rw [H.fderiv]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
  ring

/-- Away from the origin, the second derivative of the radial function `z ↦ β ‖z‖` at `y` along
the unit radial vector `u = ‖y‖⁻¹ • y` is `β'' (‖y‖)`. -/
theorem fderiv_fderiv_comp_norm_apply_inv_norm_smul {β : ℝ → ℝ} {y : V} (hy : y ≠ 0)
    (hβ : ContDiffAt ℝ 2 β ‖y‖) :
    fderiv ℝ (fderiv ℝ (fun z : V ↦ β ‖z‖)) y (‖y‖⁻¹ • y) (‖y‖⁻¹ • y) =
      deriv (deriv β) ‖y‖ := by
  have hpos : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hg : ContDiffAt ℝ 2 (fun z : V ↦ β ‖z‖) (y + (0 : ℝ) • (‖y‖⁻¹ • y)) := by
    rw [zero_smul, add_zero]
    exact hβ.comp y (contDiffAt_norm ℝ hy)
  -- Along the radial line through `y`, the norm is `‖y‖ + s` for `s > -‖y‖`.
  have hline : (fun s : ℝ ↦ β ‖y + s • (‖y‖⁻¹ • y)‖) =ᶠ[𝓝 0] fun s ↦ β (‖y‖ + s) := by
    filter_upwards [lt_mem_nhds (neg_lt_zero.mpr hpos)] with s hs
    have h1 : y + s • (‖y‖⁻¹ • y) = (1 + s / ‖y‖) • y := by
      rw [smul_smul, add_smul, one_smul, div_eq_mul_inv]
    have h2 : 0 ≤ 1 + s / ‖y‖ := by
      rw [← div_self hpos.ne', ← add_div]
      exact div_nonneg (by linarith) hpos.le
    rw [h1, norm_smul, Real.norm_of_nonneg h2, add_mul, one_mul, div_mul_cancel₀ _ hpos.ne']
  have h := hg.deriv_deriv_comp_add_smul
  rw [zero_smul, add_zero] at h
  rw [← h, hline.deriv.deriv_eq]
  rw [funext (deriv_comp_const_add β ‖y‖), deriv_comp_const_add, add_zero]

end Radial

section Product

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {g : F → 𝕜} {h : 𝕜 → 𝕜} {a : 𝕜} {b : F}

/-- The derivative of `x ↦ g x.2 * h x.1` at `(a, b)` sends `(s, v)` to
`g b * Dh(a) s + h a * Dg(b) v`. -/
theorem hasFDerivAt_comp_snd_mul_comp_fst (hg : DifferentiableAt 𝕜 g b)
    (hh : DifferentiableAt 𝕜 h a) :
    HasFDerivAt (fun x : 𝕜 × F ↦ g x.2 * h x.1)
      (g b • (fderiv 𝕜 h a).comp (ContinuousLinearMap.fst 𝕜 𝕜 F) +
        h a • (fderiv 𝕜 g b).comp (ContinuousLinearMap.snd 𝕜 𝕜 F)) (a, b) :=
  (hg.hasFDerivAt.comp (a, b) hasFDerivAt_snd).mul (hh.hasFDerivAt.comp (a, b) hasFDerivAt_fst)

/-- The derivative of `x ↦ g x.2 * h x.1` at `(a, b)` along `(1, 0)` is `g b * h' a`. -/
theorem fderiv_comp_snd_mul_comp_fst_apply_one_zero (hg : DifferentiableAt 𝕜 g b)
    (hh : DifferentiableAt 𝕜 h a) :
    fderiv 𝕜 (fun x : 𝕜 × F ↦ g x.2 * h x.1) (a, b) (1, 0) = g b * deriv h a := by
  simp [(hasFDerivAt_comp_snd_mul_comp_fst hg hh).fderiv]

/-- The derivative of `x ↦ g x.2 * h x.1` at `(a, b)` along `(0, v)` is `h a * g' b v`. -/
theorem fderiv_comp_snd_mul_comp_fst_apply_zero (hg : DifferentiableAt 𝕜 g b)
    (hh : DifferentiableAt 𝕜 h a) (v : F) :
    fderiv 𝕜 (fun x : 𝕜 × F ↦ g x.2 * h x.1) (a, b) (0, v) = h a * fderiv 𝕜 g b v := by
  simp [(hasFDerivAt_comp_snd_mul_comp_fst hg hh).fderiv]

/-- The second derivative of `x ↦ g x.2 * h x.1` at `(a, b)` along `(1, 0)` twice is
`g b * h'' a`. -/
theorem fderiv_fderiv_comp_snd_mul_comp_fst_apply_one_zero (hg : ContDiffAt 𝕜 2 g b)
    (hh : ContDiffAt 𝕜 2 h a) :
    fderiv 𝕜 (fderiv 𝕜 (fun x : 𝕜 × F ↦ g x.2 * h x.1)) (a, b) (1, 0) (1, 0) =
      g b * deriv (deriv h) a := by
  have hμ : ContDiffAt 𝕜 2 (fun x : 𝕜 × F ↦ g x.2 * h x.1) ((a, b) + (0 : 𝕜) • (1, 0)) := by
    rw [zero_smul, add_zero]
    exact (hg.comp (a, b) contDiffAt_snd).mul (hh.comp (a, b) contDiffAt_fst)
  have H := hμ.deriv_deriv_comp_add_smul
  rw [zero_smul, add_zero] at H
  rw [← H]
  simp [deriv_const_mul_field', deriv_comp_const_add]

/-- The second derivative of `x ↦ g x.2 * h x.1` at `(a, b)` along `(0, v)` and `(0, w)` is
`h a * g'' b v w`. -/
theorem fderiv_fderiv_comp_snd_mul_comp_fst_apply_zero (hg : ContDiffAt 𝕜 2 g b)
    (hh : ContDiffAt 𝕜 2 h a) (v w : F) :
    fderiv 𝕜 (fderiv 𝕜 (fun x : 𝕜 × F ↦ g x.2 * h x.1)) (a, b) (0, v) (0, w) =
      h a * fderiv 𝕜 (fderiv 𝕜 g) b v w := by
  have hμ : ContDiffAt 𝕜 2 (fun x : 𝕜 × F ↦ g x.2 * h x.1) (a, b) :=
    (hg.comp (a, b) contDiffAt_snd).mul (hh.comp (a, b) contDiffAt_fst)
  have hslice : (fun y ↦ g y * h a) = h a • g := funext fun y ↦ by simp [mul_comm]
  rw [← TauCeti.fderiv_fderiv_slice_right_apply hμ, hslice, TauCeti.fderiv_fderiv_const_smul]
  simp

end Product

end SymplecticGeometry

end
