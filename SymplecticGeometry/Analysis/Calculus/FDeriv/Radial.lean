/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Calculus.Taylor.Integral
import TauCeti.Analysis.InnerProductSpace.NormPow

/-!
# Derivatives of radial functions

Derivatives of a radial function `y ↦ β ‖y‖` on a real inner product space `V`, for `β : ℝ → F`.
It is `Cⁿ` when `β` is `Cⁿ` and constant near `0` (`ContDiff.comp_norm_of_eventuallyEq_const`).
Away from the origin its derivative along `v` is `(⟪y, v⟫ / ‖y‖) • β' (‖y‖)`
(`fderiv_comp_norm_apply`), and its second derivative along the unit radial vector `‖y‖⁻¹ • y` is
`β'' (‖y‖)` (`fderiv_fderiv_comp_norm_apply_inv_norm_smul`): along that line the norm is
`‖y‖ + s`.

The smoothness reduces to Tau Ceti's `ContDiff.comp_norm`, and the first derivative to Tau Ceti's
`hasFDerivAt_norm_of_ne` (both in `TauCeti/Analysis/InnerProductSpace/NormPow.lean`). The second
derivative is computed along the radial line with Tau Ceti's
`ContDiffAt.deriv_deriv_comp_add_smul`.
-/

public section

open Filter
open scoped Topology InnerProductSpace

namespace SymplecticGeometry

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
`(⟪y, v⟫ / ‖y‖) • β' (‖y‖)`. -/
theorem fderiv_comp_norm_apply {β : ℝ → F} {y : V} (hy : y ≠ 0)
    (hβ : DifferentiableAt ℝ β ‖y‖) (v : V) :
    fderiv ℝ (fun z : V ↦ β ‖z‖) y v = (⟪y, v⟫_ℝ / ‖y‖) • deriv β ‖y‖ := by
  have H : HasFDerivAt (fun z : V ↦ β ‖z‖) _ y :=
    hβ.hasFDerivAt.comp y (TauCeti.hasFDerivAt_norm_of_ne hy)
  rw [H.fderiv]
  simp [div_eq_inv_mul, mul_smul]

/-- Away from the origin, the second derivative of the radial function `z ↦ β ‖z‖` at `y` along
the unit radial vector `u = ‖y‖⁻¹ • y` is `β'' (‖y‖)`. -/
theorem fderiv_fderiv_comp_norm_apply_inv_norm_smul {β : ℝ → F} {y : V} (hy : y ≠ 0)
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

end SymplecticGeometry

end
