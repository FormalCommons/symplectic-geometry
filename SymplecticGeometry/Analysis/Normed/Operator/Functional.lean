/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Operator.Bilinear
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
* `ContinuousLinearMap.mul_le_apply_one_sub_smul_add_smul_add_of_le`: for a functional `φ`, a
  perturbed convex combination of two vectors that satisfy an inequality of this shape satisfies
  it with the constant `c / 2`, if the error is small.
* `ContinuousLinearMap.mul_le_one_sub_smul_add_smul_add_apply`: a convex combination of two
  functionals that satisfy the inequality for the same `v`, plus an error small relative to the
  first, satisfies it with the constant `c / 2`.
* `ContinuousLinearMap.mul_le_apply_one_sub_smul_add_smul_add`: the same for a convex
  combination of two vectors that satisfy the inequality for the same `ℓ`.

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

/-- **The gradient-like inequality for a perturbed convex combination, abstractly.** Let
`φ : E →L[ℝ] ℝ`, `c ≥ 0` and `Z : ℝ`, and let `x y : E` satisfy `c (‖x‖² + Z²) ≤ φ x` and
`c (‖y‖² + Z²) ≤ φ y`. Let `s ∈ [0, 1]`, and let `e : E` be an error with `-(‖e‖ Z) ≤ φ e` and
`c ‖e‖² + ‖e‖ Z ≤ c / 2 * Z²`. Then `u = (1 - s) • x + s • y + e` satisfies
`c / 2 * (‖u‖² + Z²) ≤ φ u`. -/
theorem mul_le_apply_one_sub_smul_add_smul_add_of_le {φ : E →L[ℝ] ℝ} {x y e : E} {s Z : ℝ}
    (hc : 0 ≤ c) (hs : s ∈ Set.Icc (0 : ℝ) 1) (hx : c * (‖x‖ ^ 2 + Z ^ 2) ≤ φ x)
    (hy : c * (‖y‖ ^ 2 + Z ^ 2) ≤ φ y) (he : -(‖e‖ * Z) ≤ φ e)
    (he' : c * ‖e‖ ^ 2 + ‖e‖ * Z ≤ c / 2 * Z ^ 2) :
    c / 2 * (‖(1 - s) • x + s • y + e‖ ^ 2 + Z ^ 2) ≤ φ ((1 - s) • x + s • y + e) := by
  obtain ⟨hs0, hs1⟩ := hs
  set u := (1 - s) • x + s • y
  -- The convex combination satisfies the inequality with the constant `c`.
  have hu : c * (‖u‖ ^ 2 + Z ^ 2) ≤ φ u := by
    have hφu : φ u = (1 - s) * φ x + s * φ y := by simp [u]
    have hsq : ‖u‖ ^ 2 ≤ (1 - s) * ‖x‖ ^ 2 + s * ‖y‖ ^ 2 := by
      have hconv : ConvexOn ℝ Set.univ fun x : E ↦ ‖x‖ ^ 2 :=
        (convexOn_norm convex_univ).pow (fun _ _ ↦ norm_nonneg _) 2
      simpa using hconv.2 (Set.mem_univ x) (Set.mem_univ y) (sub_nonneg.2 hs1) hs0 (by ring)
    rw [hφu]
    nlinarith [mul_le_mul_of_nonneg_left hx (sub_nonneg.2 hs1), mul_le_mul_of_nonneg_left hy hs0]
  -- The error costs at most half of the constant.
  have hn : ‖u + e‖ ^ 2 ≤ 2 * (‖u‖ ^ 2 + ‖e‖ ^ 2) :=
    (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le u e) 2).trans (add_sq_le ..)
  rw [map_add]
  nlinarith [mul_le_mul_of_nonneg_left hn hc]

/-- **The gradient-like inequality for a perturbed convex combination.** Let `a b : E →L[ℝ] ℝ`
satisfy `c (‖v‖² + ‖a‖²) ≤ a v` and `c (‖v‖² + ‖b‖²) ≤ b v` with `c > 0`, let `s ∈ [0, 1]`,
and let `e` be an error with `‖e‖ ≤ η ‖a‖`, where `2 (η + η²) ≤ c²`. Then
`ℓ = (1 - s) • a + s • b + e` satisfies `c / 2 * (‖v‖² + ‖ℓ‖²) ≤ ℓ v`. -/
theorem mul_le_one_sub_smul_add_smul_add_apply {a b e : E →L[ℝ] ℝ} {s η : ℝ}
    (hc : 0 < c) (hs : s ∈ Set.Icc (0 : ℝ) 1) (ha : c * (‖v‖ ^ 2 + ‖a‖ ^ 2) ≤ a v)
    (hb : c * (‖v‖ ^ 2 + ‖b‖ ^ 2) ≤ b v) (hη : 2 * (η + η ^ 2) ≤ c ^ 2)
    (he : ‖e‖ ≤ η * ‖a‖) :
    c / 2 * (‖v‖ ^ 2 + ‖(1 - s) • a + s • b + e‖ ^ 2) ≤ ((1 - s) • a + s • b + e) v := by
  -- Only `max η 0` matters: for `η < 0` the hypothesis `he` forces `a = 0` and `e = 0`.
  obtain ⟨η, hη0, hη, he⟩ : ∃ η' : ℝ, 0 ≤ η' ∧ 2 * (η' + η' ^ 2) ≤ c ^ 2 ∧ ‖e‖ ≤ η' * ‖a‖ :=
    ⟨max η 0, le_max_right _ _, by
      rcases le_total η 0 with h | h
      · rw [max_eq_right h]; nlinarith [sq_nonneg c]
      · rwa [max_eq_left h],
      he.trans (by gcongr; exact le_max_left _ _)⟩
  -- The error estimate.
  have hce : c * ‖e‖ ≤ η * ‖v‖ := by
    calc c * ‖e‖ ≤ c * (η * ‖a‖) := by gcongr
      _ = η * (c * ‖a‖) := by ring
      _ ≤ η * ‖v‖ := by gcongr; exact mul_opNorm_le_norm_of_mul_le_apply ha
  have hkey : c * (c * ‖e‖ ^ 2 + ‖e‖ * ‖v‖) ≤ c * (c / 2 * ‖v‖ ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_right hce (norm_nonneg v), sq_nonneg ‖v‖,
      pow_le_pow_left₀ (by positivity) hce 2]
  have h := mul_le_apply_one_sub_smul_add_smul_add_of_le (φ := apply ℝ ℝ v)
    hc.le hs (by simpa [add_comm] using ha) (by simpa [add_comm] using hb)
    (abs_le.1 (e.le_opNorm v)).1 (le_of_mul_le_mul_left hkey hc)
  simpa [add_comm] using h

/-- **The gradient-like inequality for a perturbed convex combination of vectors.** Let `a` be a
covector and `v w : E` vectors with `c (‖v‖² + ‖a‖²) ≤ a v` and `c (‖w‖² + ‖a‖²) ≤ a w`, where
`c > 0`; let `s ∈ [0, 1]`, and let `e` be an error with `‖e‖ ≤ η ‖a‖`, where
`2 (η + η²) ≤ c²`. Then `u = (1 - s) • v + s • w + e` satisfies
`c / 2 * (‖u‖² + ‖a‖²) ≤ a u`. This is `mul_le_one_sub_smul_add_smul_add_apply` with the roles
of vectors and covectors exchanged. -/
theorem mul_le_apply_one_sub_smul_add_smul_add {a : E →L[ℝ] ℝ} {w e : E} {s η : ℝ}
    (hc : 0 < c) (hs : s ∈ Set.Icc (0 : ℝ) 1) (hv : c * (‖v‖ ^ 2 + ‖a‖ ^ 2) ≤ a v)
    (hw : c * (‖w‖ ^ 2 + ‖a‖ ^ 2) ≤ a w) (hη : 2 * (η + η ^ 2) ≤ c ^ 2)
    (he : ‖e‖ ≤ η * ‖a‖) :
    c / 2 * (‖(1 - s) • v + s • w + e‖ ^ 2 + ‖a‖ ^ 2) ≤ a ((1 - s) • v + s • w + e) := by
  refine mul_le_apply_one_sub_smul_add_smul_add_of_le hc.le hs hv hw
    (by simpa [mul_comm] using (abs_le.1 (a.le_opNorm e)).1) ?_
  -- The error estimate: trivial if `a = 0`; otherwise `c ≤ 1 / 2`, so `‖e‖ ≤ c / 4 * ‖a‖`.
  rcases (norm_nonneg a).eq_or_lt with h0 | h0
  · have he0 : ‖e‖ = 0 := le_antisymm (by simpa [← h0] using he) (norm_nonneg e)
    rw [he0]; nlinarith [sq_nonneg ‖a‖]
  have hc2 : c ≤ 1 / 2 := by
    have : c * (‖v‖ ^ 2 + ‖a‖ ^ 2) ≤ 1 / 2 * (‖v‖ ^ 2 + ‖a‖ ^ 2) := by
      nlinarith [sq_nonneg (‖v‖ - ‖a‖), (abs_le.1 (a.le_opNorm v)).2]
    exact le_of_mul_le_mul_right this (by positivity)
  have hηc : η ≤ c / 4 := by nlinarith [sq_nonneg η]
  have hec : ‖e‖ ≤ c / 4 * ‖a‖ := he.trans (by gcongr)
  have h1 : c * ‖e‖ ^ 2 ≤ c / 4 * ‖a‖ ^ 2 := by
    calc c * ‖e‖ ^ 2 ≤ c * (c / 4 * ‖a‖) ^ 2 := by gcongr
      _ = c * (c ^ 2 / 4) * ‖a‖ ^ 2 / 4 := by ring
      _ ≤ c * 1 * ‖a‖ ^ 2 / 4 := by gcongr; nlinarith
      _ = c / 4 * ‖a‖ ^ 2 := by ring
  nlinarith [mul_le_mul_of_nonneg_right hec (norm_nonneg a)]

end ContinuousLinearMap

end
