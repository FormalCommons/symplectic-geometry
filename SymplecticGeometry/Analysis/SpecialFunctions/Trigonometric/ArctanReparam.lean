/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# A smooth map of the line into a ball, tangent to the identity at its centre

For `x : ℝ` and `δ > 0`, the map `r ↦ x + ε arctan ((r - x) / ε)` with `ε = δ / 4` is smooth,
takes values in the ball of radius `δ` about `x`, fixes `x` and has derivative `1` there
(`Real.exists_contDiff_mem_ball_hasDerivAt_one`). It turns a map that is smooth only near
`x` in one variable into a map smooth everywhere that agrees with it to first order at `x`.
-/

public section

open scoped ContDiff Real

namespace Real

/-- For `x : ℝ` and `δ > 0`, some smooth map `ρ : ℝ → ℝ` takes values in the ball of radius `δ`
about `x`, fixes `x` and has derivative `1` at `x`. -/
theorem exists_contDiff_mem_ball_hasDerivAt_one (x : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ ∧ (∀ r, ρ r ∈ Metric.ball x δ) ∧ ρ x = x ∧
      HasDerivAt ρ 1 x := by
  set ε := δ / 4
  have hε : 0 < ε := by positivity
  refine ⟨fun r ↦ x + ε * arctan ((r - x) / ε), contDiff_const.add (contDiff_const.mul
    (contDiff_arctan.comp ((contDiff_id.sub contDiff_const).div_const _))), fun r ↦ ?_,
    by simp, ?_⟩
  · rw [Metric.mem_ball, dist_eq, add_sub_cancel_left, abs_mul, abs_of_pos hε]
    calc ε * |arctan ((r - x) / ε)| < ε * (π / 2) :=
          mul_lt_mul_of_pos_left (abs_lt.2 ⟨neg_pi_div_two_lt_arctan _,
            arctan_lt_pi_div_two _⟩) hε
      _ < δ := by simp only [ε]; nlinarith [pi_le_four]
  · refine ((((hasDerivAt_id x).sub_const x).div_const ε).arctan.const_mul ε
      |>.const_add x).congr_deriv ?_
    simp only [id, sub_self, zero_div]
    field_simp
    norm_num

end Real
