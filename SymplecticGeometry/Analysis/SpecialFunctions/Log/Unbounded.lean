/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Order.Bounds.Image
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Functions whose derivative is at least `k / t` near `0⁺`

A real function whose derivative is at least `k / t`, with `k > 0`, on an interval `(0, δ)`
grows at least like `k * log t` there, so it is not bounded below on `(0, δ)`
(`Real.not_bddBelow_image_Ioo_of_div_le_deriv`): the function minus `k * log` is monotone,
and `log t → -∞` as `t → 0⁺`.
-/

public section

open Filter Set Topology

namespace Real

/-- A real function `g`, differentiable on `(0, δ)` with `δ > 0`, whose derivative is at least
`k / t` with `k > 0` at each `t` of that interval, is not bounded below on it. -/
theorem not_bddBelow_image_Ioo_of_div_le_deriv {g : ℝ → ℝ} {k δ : ℝ} (hk : 0 < k)
    (hδ : 0 < δ) (hd : DifferentiableOn ℝ g (Ioo 0 δ))
    (hD : ∀ t ∈ Ioo 0 δ, k / t ≤ deriv g t) : ¬ BddBelow (g '' Ioo 0 δ) := by
  rintro ⟨M, hM⟩
  -- `t ↦ g t - k * log t` is monotone on `(0, δ)`.
  have hφ : ∀ t ∈ Ioo 0 δ, HasDerivAt (fun u ↦ g u - k * log u) (deriv g t - k * t⁻¹) t :=
    fun t ht ↦ ((hd t ht).differentiableAt (Ioo_mem_nhds ht.1 ht.2)).hasDerivAt.sub
      ((hasDerivAt_log ht.1.ne').const_mul k)
  have hmono : MonotoneOn (fun u ↦ g u - k * log u) (Ioo 0 δ) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioo 0 δ)
      (fun t ht ↦ (hφ t ht).continuousAt.continuousWithinAt)
      (fun t ht ↦ (hφ t (interior_subset ht)).hasDerivWithinAt) fun t ht ↦ ?_
    rw [interior_Ioo] at ht
    have := hD t ht
    rw [div_eq_mul_inv] at this
    linarith
  -- Fix `t = δ / 2`, and let `u → 0⁺`, where `log u → -∞`.
  have ht : δ / 2 ∈ Ioo 0 δ := ⟨by positivity, by linarith⟩
  obtain ⟨u, hu, hlog⟩ := ((eventually_mem_set.2 (Ioo_mem_nhdsGT ht.1)).and
    (tendsto_log_nhdsGT_zero.eventually_lt_atBot ((M - g (δ / 2) + k * log (δ / 2)) / k))).exists
  have hu' : u ∈ Ioo 0 δ := ⟨hu.1, hu.2.trans ht.2⟩
  have hle := hmono hu' ht hu.2.le
  have hgu := hM (mem_image_of_mem g hu')
  rw [lt_div_iff₀ hk] at hlog
  simp only at hle
  linarith

end Real

end
