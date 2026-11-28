/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Norm bounds from a lower bound on a real functional

Let `ℓ` be a continuous real linear functional on a seminormed space and `v` a vector with
`c (‖v‖² + ‖ℓ‖²) ≤ ℓ v`. Since `ℓ v ≤ ‖ℓ‖ ‖v‖`, this compares the two norms. Such inequalities
are what a gradient-like vector field `v` for a function with differential `ℓ` satisfies, as in the
proof of Proposition 9.23 of [CieliebakEliashberg2012].

## Main results

* `ContinuousLinearMap.mul_norm_le_opNorm_of_mul_le_apply`: `c ‖v‖ ≤ ‖ℓ‖`.
* `ContinuousLinearMap.mul_opNorm_le_norm_of_mul_le_apply`: `c ‖ℓ‖ ≤ ‖v‖`.
* `ContinuousLinearMap.norm_sub_le_of_mul_le_apply`: if `ℓ` and `ℓ'` both satisfy the inequality
  for the same `v` and `c > 0`, then `‖ℓ' - ℓ‖ ≤ (1 + 1 / c²) ‖ℓ‖`.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Proposition 9.23
-/

public section

namespace ContinuousLinearMap

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {ℓ ℓ' : E →L[ℝ] ℝ} {v : E}
  {c : ℝ}

/-- If `c (‖v‖² + ‖ℓ‖²) ≤ ℓ v`, then `c ‖v‖ ≤ ‖ℓ‖`. -/
theorem mul_norm_le_opNorm_of_mul_le_apply (h : c * (‖v‖ ^ 2 + ‖ℓ‖ ^ 2) ≤ ℓ v) :
    c * ‖v‖ ≤ ‖ℓ‖ := by
  rcases le_or_gt c 0 with hc | hc
  · nlinarith [norm_nonneg v, norm_nonneg ℓ]
  have h1 : ℓ v ≤ ‖ℓ‖ * ‖v‖ := (le_abs_self _).trans (ℓ.le_opNorm v)
  rcases (norm_nonneg v).eq_or_lt with h0 | h0
  · rw [← h0, mul_zero]; exact norm_nonneg ℓ
  · refine le_of_mul_le_mul_right ?_ h0
    nlinarith [sq_nonneg ‖ℓ‖]

/-- If `c (‖v‖² + ‖ℓ‖²) ≤ ℓ v`, then `c ‖ℓ‖ ≤ ‖v‖`. -/
theorem mul_opNorm_le_norm_of_mul_le_apply (h : c * (‖v‖ ^ 2 + ‖ℓ‖ ^ 2) ≤ ℓ v) :
    c * ‖ℓ‖ ≤ ‖v‖ := by
  rcases le_or_gt c 0 with hc | hc
  · nlinarith [norm_nonneg v, norm_nonneg ℓ]
  have h1 : ℓ v ≤ ‖ℓ‖ * ‖v‖ := (le_abs_self _).trans (ℓ.le_opNorm v)
  rcases (norm_nonneg ℓ).eq_or_lt with h0 | h0
  · rw [← h0, mul_zero]; exact norm_nonneg v
  · refine le_of_mul_le_mul_right ?_ h0
    nlinarith [sq_nonneg ‖v‖]

/-- If `ℓ` and `ℓ'` both satisfy `c (‖v‖² + ‖·‖²) ≤ · v` for the same vector `v`, with `c > 0`,
then `‖ℓ' - ℓ‖ ≤ (1 + 1 / c²) ‖ℓ‖`. -/
theorem norm_sub_le_of_mul_le_apply (hc : 0 < c) (h : c * (‖v‖ ^ 2 + ‖ℓ‖ ^ 2) ≤ ℓ v)
    (h' : c * (‖v‖ ^ 2 + ‖ℓ'‖ ^ 2) ≤ ℓ' v) : ‖ℓ' - ℓ‖ ≤ (1 + 1 / c ^ 2) * ‖ℓ‖ := by
  have h₁ := mul_norm_le_opNorm_of_mul_le_apply h
  have h₂ := mul_opNorm_le_norm_of_mul_le_apply h'
  have h₃ : ‖ℓ'‖ ≤ 1 / c ^ 2 * ‖ℓ‖ := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
    nlinarith
  calc ‖ℓ' - ℓ‖ ≤ ‖ℓ'‖ + ‖ℓ‖ := norm_sub_le _ _
    _ ≤ _ := by linarith

end ContinuousLinearMap

end
