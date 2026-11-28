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
* `ContinuousLinearMap.mul_le_one_sub_smul_add_smul_add_apply`: a convex combination of two
  functionals that satisfy the inequality for the same `v`, plus an error small relative to the
  first, satisfies it with the constant `c / 2`.

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

/-- **The gradient-like inequality for a perturbed convex combination.** Let `a b : E →L[ℝ] ℝ`
satisfy `c (‖v‖² + ‖a‖²) ≤ a v` and `c (‖v‖² + ‖b‖²) ≤ b v` with `c > 0`, let `s ∈ [0, 1]`,
and let `e` be an error with `‖e‖ ≤ η ‖a‖`, where `2 (η + η²) ≤ c²`. Then
`(1 - s) • a + s • b + e` satisfies the same inequality with the constant `c / 2`. -/
theorem mul_le_one_sub_smul_add_smul_add_apply {a b e : E →L[ℝ] ℝ} {v : E} {c s η : ℝ}
    (hc : 0 < c) (hs : s ∈ Set.Icc (0 : ℝ) 1) (ha : c * (‖v‖ ^ 2 + ‖a‖ ^ 2) ≤ a v)
    (hb : c * (‖v‖ ^ 2 + ‖b‖ ^ 2) ≤ b v) (hη : 2 * (η + η ^ 2) ≤ c ^ 2)
    (he : ‖e‖ ≤ η * ‖a‖) :
    c / 2 * (‖v‖ ^ 2 + ‖(1 - s) • a + s • b + e‖ ^ 2) ≤ ((1 - s) • a + s • b + e) v := by
  obtain ⟨hs0, hs1⟩ := hs
  -- Only `max η 0` matters: for `η < 0` the hypothesis `he` forces `a = 0` and `e = 0`.
  obtain ⟨η, hη0, hη, he⟩ : ∃ η' : ℝ, 0 ≤ η' ∧ 2 * (η' + η' ^ 2) ≤ c ^ 2 ∧ ‖e‖ ≤ η' * ‖a‖ :=
    ⟨max η 0, le_max_right _ _, by
      rcases le_total η 0 with h | h
      · rw [max_eq_right h]; nlinarith [sq_nonneg c]
      · rwa [max_eq_left h],
      he.trans (by gcongr; exact le_max_left _ _)⟩
  set m := (1 - s) • a + s • b
  have hav : c * ‖a‖ ≤ ‖v‖ := mul_opNorm_le_norm_of_mul_le_apply ha
  -- The convex combination satisfies the inequality with the constant `c`.
  have hmn : ‖m‖ ≤ (1 - s) * ‖a‖ + s * ‖b‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg hs0]
  have hm : c * (‖v‖ ^ 2 + ‖m‖ ^ 2) ≤ m v := by
    have hmv : m v = (1 - s) * a v + s * b v := by simp [m]
    have hsq : ‖m‖ ^ 2 ≤ (1 - s) * ‖a‖ ^ 2 + s * ‖b‖ ^ 2 := by
      nlinarith [pow_le_pow_left₀ (norm_nonneg m) hmn 2, mul_nonneg (mul_nonneg hs0
        (sub_nonneg.2 hs1)) (sq_nonneg (‖a‖ - ‖b‖))]
    rw [hmv]
    nlinarith [mul_le_mul_of_nonneg_left ha (sub_nonneg.2 hs1), mul_le_mul_of_nonneg_left hb hs0]
  -- The error costs at most half of the constant.
  have hev : -(‖e‖ * ‖v‖) ≤ e v := by
    have := e.le_opNorm v
    rw [Real.norm_eq_abs] at this
    linarith [neg_abs_le (e v)]
  have hce : c * ‖e‖ ≤ η * ‖v‖ := by
    calc c * ‖e‖ ≤ c * (η * ‖a‖) := by gcongr
      _ = η * (c * ‖a‖) := by ring
      _ ≤ η * ‖v‖ := by gcongr
  have hn : ‖m + e‖ ^ 2 ≤ 2 * ‖m‖ ^ 2 + 2 * ‖e‖ ^ 2 := by
    nlinarith [norm_add_le m e, norm_nonneg (m + e), sq_nonneg (‖m‖ - ‖e‖)]
  have hce2 : (c * ‖e‖) ^ 2 ≤ (η * ‖v‖) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hce 2
  have hkey : c * (c * ‖e‖ ^ 2 + ‖e‖ * ‖v‖) ≤ c * (c / 2 * ‖v‖ ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_right hce (norm_nonneg v), sq_nonneg ‖v‖]
  have hkey' : c * ‖e‖ ^ 2 + ‖e‖ * ‖v‖ ≤ c / 2 * ‖v‖ ^ 2 := le_of_mul_le_mul_left hkey hc
  rw [add_apply]
  nlinarith

end ContinuousLinearMap

end
