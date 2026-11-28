/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Support
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.Module
import SymplecticGeometry.Geometry.Manifold.Riemannian.Surface.LogCutoff.Ball

/-!
# A logarithmic cut-off keeps a field gradient-like

Let `E` be a finite-dimensional real normed space, `X : E → E` a field and `f H : E → ℝ`
differentiable on a ball `B` around `0`, such that on `B` the field `X` satisfies the
gradient-like inequality `c (‖X‖² + ‖Df‖²) ≤ Df(X)` for both `f` and `f + H`, and
`|H z| ≤ A ‖z‖ ‖Df(z)‖`. This file shows that for every `r > 0` there is a smooth cut-off
`β : E → [0, 1]`, equal to `1` near `0` and supported in the ball of radius `r`, such that `X`
satisfies the gradient-like inequality on `B`, with constant `c / 2`, for every function
`f + t β H` with `t ∈ [0, 1]`. The constant does not depend on `r`.

The cut-off `β` is the one of
`SymplecticGeometry.exists_contDiff_tsupport_subset_ball_norm_mul_norm_fderiv_le`, built from
Tau Ceti's logarithmic profile, with `‖z‖ ‖Dβ(z)‖` small. The differential of `f + t β H` is
`(1 - tβ) Df + tβ D(f + H) + t H Dβ`. The first two terms satisfy the gradient-like inequality
with the constant `c`, by convexity (`SymplecticGeometry.mul_le_one_sub_smul_add_smul_add_apply`).
The last term has norm at most `A ‖z‖ ‖Dβ(z)‖ ‖Df(z)‖`; since `c ‖Df‖ ≤ ‖X‖`, it costs only half
of the constant once `‖z‖ ‖Dβ(z)‖` is small enough. A cut-off with `‖Dβ‖` of order `1 / r` would
not do, since `A` need not be small: this is why the cut-off is logarithmic.

This is the estimate that lets one cut off `t H` near a critical point in the proof of
Proposition 9.23 of [CieliebakEliashberg2012], as in their Lemma 12.9, where `|H| ≤ A ‖z‖ ‖Df‖`
comes from the radial estimates of `Morse/RadialEstimate.lean`.

## Main results

* `SymplecticGeometry.mul_le_one_sub_smul_add_smul_add_apply`: at one point, a convex
  combination of two differentials satisfying the gradient-like inequality, perturbed by a small
  error, satisfies it with half the constant.
* `SymplecticGeometry.exists_contDiff_tsupport_subset_ball_mul_le_fderiv_add_smul_mul_apply`:
  the cut-off `β` above.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012]
-/

public section

open Set Metric Filter Topology
open scoped ContDiff

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The gradient-like inequality for a perturbed convex combination.** Let `a b : E →L[ℝ] ℝ`
satisfy `c (‖v‖² + ‖a‖²) ≤ a v` and `c (‖v‖² + ‖b‖²) ≤ b v` with `c > 0`, let `s ∈ [0, 1]`,
and let `e` be an error with `‖e‖ ≤ η ‖a‖`, where `2 (η + η²) ≤ c²`. Then
`ℓ = (1 - s) • a + s • b + e` satisfies `c / 2 * (‖v‖² + ‖ℓ‖²) ≤ ℓ v`. -/
theorem mul_le_one_sub_smul_add_smul_add_apply {a b e : E →L[ℝ] ℝ} {v : E} {c s η : ℝ}
    (hc : 0 < c) (hs : s ∈ Icc (0 : ℝ) 1) (ha : c * (‖v‖ ^ 2 + ‖a‖ ^ 2) ≤ a v)
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
  set ℓ := (1 - s) • a + s • b
  -- `c ‖a‖ ≤ ‖v‖`, from the inequality for `a` and `a v ≤ ‖a‖ ‖v‖`.
  have hav : c * ‖a‖ ≤ ‖v‖ := by
    have h1 : a v ≤ ‖a‖ * ‖v‖ := (le_abs_self _).trans (a.le_opNorm v)
    rcases (norm_nonneg a).eq_or_lt with h0 | h0
    · rw [← h0, mul_zero]; exact norm_nonneg v
    · refine le_of_mul_le_mul_right ?_ h0
      nlinarith [sq_nonneg ‖v‖, sq_nonneg ‖a‖]
  -- The convex combination satisfies the inequality with the constant `c`.
  have hℓn : ‖ℓ‖ ≤ (1 - s) * ‖a‖ + s * ‖b‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg hs0]
  have hℓ : c * (‖v‖ ^ 2 + ‖ℓ‖ ^ 2) ≤ ℓ v := by
    have hℓv : ℓ v = (1 - s) * a v + s * b v := by simp [ℓ]
    have hsq : ‖ℓ‖ ^ 2 ≤ (1 - s) * ‖a‖ ^ 2 + s * ‖b‖ ^ 2 := by
      nlinarith [pow_le_pow_left₀ (norm_nonneg ℓ) hℓn 2, mul_nonneg (mul_nonneg hs0
        (sub_nonneg.2 hs1)) (sq_nonneg (‖a‖ - ‖b‖))]
    rw [hℓv]
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
  have hn : ‖ℓ + e‖ ^ 2 ≤ 2 * ‖ℓ‖ ^ 2 + 2 * ‖e‖ ^ 2 := by
    nlinarith [norm_add_le ℓ e, norm_nonneg (ℓ + e), sq_nonneg (‖ℓ‖ - ‖e‖)]
  have hce2 : (c * ‖e‖) ^ 2 ≤ (η * ‖v‖) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hce 2
  have hkey : c * (c * ‖e‖ ^ 2 + ‖e‖ * ‖v‖) ≤ c * (c / 2 * ‖v‖ ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_right hce (norm_nonneg v), sq_nonneg ‖v‖]
  have hkey' : c * ‖e‖ ^ 2 + ‖e‖ * ‖v‖ ≤ c / 2 * ‖v‖ ^ 2 := le_of_mul_le_mul_left hkey hc
  rw [add_apply]
  nlinarith

variable [FiniteDimensional ℝ E]

/-- **A logarithmic cut-off keeps a field gradient-like.** Let `E` be a finite-dimensional real
normed space, `X : E → E`, and `f H : E → ℝ` differentiable on `ball 0 r₀`, such that for every
`z` in that ball and some `c > 0` and `A`,
* `c (‖X z‖² + ‖Df(z)‖²) ≤ Df(z) (X z)`,
* `c (‖X z‖² + ‖D(f + H)(z)‖²) ≤ D(f + H)(z) (X z)`,
* `|H z| ≤ A ‖z‖ ‖Df(z)‖`.

Then for every `r > 0` there is a smooth `β : E → ℝ` with values in `[0, 1]`, equal to `1` near
`0`, with topological support in `ball 0 r`, such that for every `t ∈ [0, 1]` and `z` in
`ball 0 r₀`, with `F = f + t • (β * H)`,
`c / 2 * (‖X z‖² + ‖DF(z)‖²) ≤ DF(z) (X z)`. -/
theorem exists_contDiff_tsupport_subset_ball_mul_le_fderiv_add_smul_mul_apply {f H : E → ℝ}
    {X : E → E} {r₀ c A : ℝ} (hc : 0 < c) (hf : DifferentiableOn ℝ f (ball 0 r₀))
    (hH : DifferentiableOn ℝ H (ball 0 r₀))
    (h₁ : ∀ z ∈ ball (0 : E) r₀, c * (‖X z‖ ^ 2 + ‖fderiv ℝ f z‖ ^ 2) ≤ fderiv ℝ f z (X z))
    (h₂ : ∀ z ∈ ball (0 : E) r₀,
      c * (‖X z‖ ^ 2 + ‖fderiv ℝ (f + H) z‖ ^ 2) ≤ fderiv ℝ (f + H) z (X z))
    (h₃ : ∀ z ∈ ball (0 : E) r₀, |H z| ≤ A * ‖z‖ * ‖fderiv ℝ f z‖) {r : ℝ} (hr : 0 < r) :
    ∃ β : E → ℝ, ContDiff ℝ ∞ β ∧ (∀ z, β z ∈ Icc (0 : ℝ) 1) ∧ (∀ᶠ z in 𝓝 0, β z = 1) ∧
      tsupport β ⊆ ball 0 r ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ ball (0 : E) r₀,
        c / 2 * (‖X z‖ ^ 2 + ‖fderiv ℝ (f + t • (β * H)) z‖ ^ 2) ≤
          fderiv ℝ (f + t • (β * H)) z (X z) := by
  -- The error `t H Dβ` will be at most `m ‖Df‖`, with `2 (m + m ^ 2) ≤ c ^ 2`.
  set A' := max A 0
  set m := min (c ^ 2 / 4) 1
  have hm0 : 0 < m := lt_min (by positivity) one_pos
  have hm : 2 * (m + m ^ 2) ≤ c ^ 2 := by
    have h1 : m ≤ c ^ 2 / 4 := min_le_left _ _
    have h2 : m ≤ 1 := min_le_right _ _
    nlinarith
  obtain ⟨β, hβc, hβI, hβ1, hβs, hβD⟩ :=
    exists_contDiff_tsupport_subset_ball_norm_mul_norm_fderiv_le (E := E) hr
      (div_pos hm0 (by positivity : 0 < A' + 1))
  refine ⟨β, hβc, hβI, hβ1, hβs, fun t ht z hz₀ ↦ ?_⟩
  -- The differential of `f + t • (β * H)` at `z`.
  have hfz := (hf z hz₀).differentiableAt (isOpen_ball.mem_nhds hz₀)
  have hHz := (hH z hz₀).differentiableAt (isOpen_ball.mem_nhds hz₀)
  have hβz : DifferentiableAt ℝ β z := hβc.differentiable (by simp) z
  have hDF : fderiv ℝ (f + t • (β * H)) z =
      (1 - t * β z) • fderiv ℝ f z + (t * β z) • fderiv ℝ (f + H) z +
        (t * H z) • fderiv ℝ β z := by
    rw [fderiv_add hfz ((hβz.mul hHz).const_smul t), fderiv_const_smul (hβz.mul hHz),
      fderiv_mul hβz hHz, fderiv_add hfz hHz]
    module
  have hs : t * β z ∈ Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg ht.1 (hβI z).1, by nlinarith [ht.1, ht.2, (hβI z).1, (hβI z).2]⟩
  rw [hDF]
  refine mul_le_one_sub_smul_add_smul_add_apply hc hs (h₁ z hz₀) (h₂ z hz₀) hm ?_
  -- The error term `t H Dβ`.
  have hA' : |H z| ≤ A' * ‖z‖ * ‖fderiv ℝ f z‖ :=
    (h₃ z hz₀).trans (by gcongr; exact le_max_left _ _)
  have hAm : A' * (m / (A' + 1)) ≤ m := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [le_max_right A 0]
  rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg ht.1]
  calc t * |H z| * ‖fderiv ℝ β z‖ ≤ 1 * (A' * ‖z‖ * ‖fderiv ℝ f z‖) * ‖fderiv ℝ β z‖ := by
        gcongr; exact ht.2
    _ = A' * (‖z‖ * ‖fderiv ℝ β z‖) * ‖fderiv ℝ f z‖ := by ring
    _ ≤ A' * (m / (A' + 1)) * ‖fderiv ℝ f z‖ := by gcongr; exact hβD z
    _ ≤ m * ‖fderiv ℝ f z‖ := mul_le_mul_of_nonneg_right hAm (norm_nonneg _)

end SymplecticGeometry

end
