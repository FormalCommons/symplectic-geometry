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
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Normed.Module.Convex
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

The file also proves the version in which `f` stays fixed and the field moves. Let `X` and `X'`
both satisfy the gradient-like inequality for `f` on `B`, with `X' - X = J(DH)` for a bounded
family `J` of linear maps from covectors to vectors (in the application, `J(DG)` is the
Hamiltonian field of `G`). Then the same logarithmic cut-off `β` makes every field
`X + t J(D(β H))` with `t ∈ [0, 1]` gradient-like for `f` on `B`, with constant `c / 2`. Here
`X + t J(D(β H)) = (1 - tβ) X + tβ X' + t H J(Dβ)`, and the pointwise estimate is
`SymplecticGeometry.mul_le_apply_one_sub_smul_add_smul_add`, in which vectors and covectors have
exchanged roles. This is the field version of the cut-off in Lemma 12.9 of
[CieliebakEliashberg2012].

## Main results

* `SymplecticGeometry.mul_le_one_sub_smul_add_smul_add_apply`: at one point, a convex
  combination of two differentials satisfying the gradient-like inequality, perturbed by a small
  error, satisfies it with half the constant.
* `SymplecticGeometry.exists_contDiff_tsupport_subset_ball_mul_le_fderiv_add_smul_mul_apply`:
  the cut-off `β` above.
* `SymplecticGeometry.mul_le_apply_one_sub_smul_add_smul_add`: the pointwise estimate for a
  perturbed convex combination of two gradient-like vectors.
* `SymplecticGeometry.exists_contDiff_tsupport_subset_ball_mul_le_fderiv_apply_add_smul`: the
  cut-off of a Hamiltonian correction of the field.

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

/-- **The gradient-like inequality for a perturbed convex combination of fields.** Let `a` be a
covector and `v w : E` vectors with `c (‖v‖² + ‖a‖²) ≤ a v` and `c (‖w‖² + ‖a‖²) ≤ a w`, where
`c > 0`; let `s ∈ [0, 1]`, and let `e` be an error with `‖e‖ ≤ η ‖a‖`, where
`2 (η + η²) ≤ c²`. Then `u = (1 - s) • v + s • w + e` satisfies
`c / 2 * (‖u‖² + ‖a‖²) ≤ a u`. This is `mul_le_one_sub_smul_add_smul_add_apply` with the roles
of vectors and covectors exchanged. -/
theorem mul_le_apply_one_sub_smul_add_smul_add {a : E →L[ℝ] ℝ} {v w e : E} {c s η : ℝ}
    (hc : 0 < c) (hs : s ∈ Icc (0 : ℝ) 1) (hv : c * (‖v‖ ^ 2 + ‖a‖ ^ 2) ≤ a v)
    (hw : c * (‖w‖ ^ 2 + ‖a‖ ^ 2) ≤ a w) (hη : 2 * (η + η ^ 2) ≤ c ^ 2)
    (he : ‖e‖ ≤ η * ‖a‖) :
    c / 2 * (‖(1 - s) • v + s • w + e‖ ^ 2 + ‖a‖ ^ 2) ≤ a ((1 - s) • v + s • w + e) := by
  obtain ⟨hs0, hs1⟩ := hs
  set u := (1 - s) • v + s • w
  -- The convex combination satisfies the inequality with the constant `c`.
  have hu : c * (‖u‖ ^ 2 + ‖a‖ ^ 2) ≤ a u := by
    have hau : a u = (1 - s) * a v + s * a w := by simp [u]
    have hsq : ‖u‖ ^ 2 ≤ (1 - s) * ‖v‖ ^ 2 + s * ‖w‖ ^ 2 := by
      have hconv : ConvexOn ℝ univ fun x : E ↦ ‖x‖ ^ 2 :=
        (convexOn_norm convex_univ).pow (fun _ _ ↦ norm_nonneg _) 2
      simpa using hconv.2 (mem_univ v) (mem_univ w) (sub_nonneg.2 hs1) hs0 (by ring)
    rw [hau]
    nlinarith [mul_le_mul_of_nonneg_left hv (sub_nonneg.2 hs1), mul_le_mul_of_nonneg_left hw hs0]
  -- If `a = 0` then `v = w = e = 0`; otherwise `c ≤ 1 / 2`, so `‖e‖ ≤ c / 4 * ‖a‖`.
  have hav : a v ≤ ‖a‖ * ‖v‖ := (le_abs_self _).trans (a.le_opNorm v)
  have hae : -(‖a‖ * ‖e‖) ≤ a e := by
    have := a.le_opNorm e
    rw [Real.norm_eq_abs] at this
    linarith [neg_abs_le (a e)]
  have hn : ‖u + e‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖e‖ ^ 2 := by
    nlinarith [norm_add_le u e, norm_nonneg (u + e), sq_nonneg (‖u‖ - ‖e‖)]
  rcases (norm_nonneg a).eq_or_lt with h0 | h0
  · have he0 : ‖e‖ = 0 := le_antisymm (by simpa [← h0] using he) (norm_nonneg e)
    have hu0 : ‖u‖ ^ 2 = 0 := by
      rw [← h0] at hu
      have : a u ≤ ‖a‖ * ‖u‖ := (le_abs_self _).trans (a.le_opNorm u)
      rw [← h0] at this
      nlinarith [sq_nonneg ‖u‖]
    have hue : ‖u + e‖ ^ 2 = 0 := le_antisymm (by rw [he0] at hn; linarith) (by positivity)
    rw [← h0, zero_mul, neg_zero] at hae
    have : 0 ≤ c * (‖u‖ ^ 2 + ‖a‖ ^ 2) := by positivity
    rw [map_add, hue, ← h0]
    linarith
  · have hc2 : c ≤ 1 / 2 := by
      have : c * (‖v‖ ^ 2 + ‖a‖ ^ 2) ≤ 1 / 2 * (‖v‖ ^ 2 + ‖a‖ ^ 2) := by
        nlinarith [sq_nonneg (‖v‖ - ‖a‖)]
      exact le_of_mul_le_mul_right this (by positivity)
    have hηc : η ≤ c / 4 := by nlinarith [sq_nonneg η]
    have hec : ‖e‖ ≤ c / 4 * ‖a‖ := he.trans (by gcongr)
    have hkey : c * ‖e‖ ^ 2 + ‖a‖ * ‖e‖ ≤ c / 2 * ‖a‖ ^ 2 := by
      have h1 : c * ‖e‖ ^ 2 ≤ c / 4 * ‖a‖ ^ 2 := by
        calc c * ‖e‖ ^ 2 ≤ c * (c / 4 * ‖a‖) ^ 2 := by gcongr
          _ = c * (c ^ 2 / 4) * ‖a‖ ^ 2 / 4 := by ring
          _ ≤ c * 1 * ‖a‖ ^ 2 / 4 := by gcongr; nlinarith
          _ = c / 4 * ‖a‖ ^ 2 := by ring
      nlinarith [mul_le_mul_of_nonneg_left hec (norm_nonneg a)]
    rw [map_add]
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

/-- **A cut-off Hamiltonian correction keeps a field gradient-like.** Let `E` be a
finite-dimensional real normed space, `f H : E → ℝ` with `H` differentiable on `ball 0 r₀`,
`X X' : E → E` and `J : E → (E →L[ℝ] ℝ) →L[ℝ] E`, such that for every `z` in that ball and some
`c > 0`, `A` and `B`,
* `c (‖X z‖² + ‖Df(z)‖²) ≤ Df(z) (X z)` and the same for `X'`,
* `X' z - X z = J z (DH(z))`,
* `‖J z‖ ≤ B` and `|H z| ≤ A ‖z‖ ‖Df(z)‖`.

Then for every `r > 0` there is a smooth `β : E → ℝ` with values in `[0, 1]`, equal to `1` near
`0`, with topological support in `ball 0 r`, such that for every `t ∈ [0, 1]` and `z` in
`ball 0 r₀`, with `Y = X z + t • J z (D(β H)(z))`,
`c / 2 * (‖Y‖² + ‖Df(z)‖²) ≤ Df(z) Y`. -/
theorem exists_contDiff_tsupport_subset_ball_mul_le_fderiv_apply_add_smul {f H : E → ℝ}
    {X X' : E → E} {J : E → (E →L[ℝ] ℝ) →L[ℝ] E} {r₀ c A B : ℝ} (hc : 0 < c)
    (hH : DifferentiableOn ℝ H (ball 0 r₀))
    (h₁ : ∀ z ∈ ball (0 : E) r₀, c * (‖X z‖ ^ 2 + ‖fderiv ℝ f z‖ ^ 2) ≤ fderiv ℝ f z (X z))
    (h₂ : ∀ z ∈ ball (0 : E) r₀, c * (‖X' z‖ ^ 2 + ‖fderiv ℝ f z‖ ^ 2) ≤ fderiv ℝ f z (X' z))
    (h₃ : ∀ z ∈ ball (0 : E) r₀, X' z - X z = J z (fderiv ℝ H z))
    (h₄ : ∀ z ∈ ball (0 : E) r₀, ‖J z‖ ≤ B)
    (h₅ : ∀ z ∈ ball (0 : E) r₀, |H z| ≤ A * ‖z‖ * ‖fderiv ℝ f z‖) {r : ℝ} (hr : 0 < r) :
    ∃ β : E → ℝ, ContDiff ℝ ∞ β ∧ (∀ z, β z ∈ Icc (0 : ℝ) 1) ∧ (∀ᶠ z in 𝓝 0, β z = 1) ∧
      tsupport β ⊆ ball 0 r ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ ball (0 : E) r₀,
        c / 2 * (‖X z + t • J z (fderiv ℝ (β * H) z)‖ ^ 2 + ‖fderiv ℝ f z‖ ^ 2) ≤
          fderiv ℝ f z (X z + t • J z (fderiv ℝ (β * H) z)) := by
  -- The error `t H J(Dβ)` will be at most `m ‖Df‖`, with `2 (m + m ^ 2) ≤ c ^ 2`.
  set K := max A 0 * max B 0
  set m := min (c ^ 2 / 4) 1
  have hm0 : 0 < m := lt_min (by positivity) one_pos
  have hm : 2 * (m + m ^ 2) ≤ c ^ 2 := by
    have h1 : m ≤ c ^ 2 / 4 := min_le_left _ _
    have h2 : m ≤ 1 := min_le_right _ _
    nlinarith
  obtain ⟨β, hβc, hβI, hβ1, hβs, hβD⟩ :=
    exists_contDiff_tsupport_subset_ball_norm_mul_norm_fderiv_le (E := E) hr
      (div_pos hm0 (by positivity : 0 < K + 1))
  refine ⟨β, hβc, hβI, hβ1, hβs, fun t ht z hz₀ ↦ ?_⟩
  -- The corrected field at `z`.
  have hHz := (hH z hz₀).differentiableAt (isOpen_ball.mem_nhds hz₀)
  have hβz : DifferentiableAt ℝ β z := hβc.differentiable (by simp) z
  have hY : X z + t • J z (fderiv ℝ (β * H) z) =
      (1 - t * β z) • X z + (t * β z) • X' z + (t * H z) • J z (fderiv ℝ β z) := by
    rw [fderiv_mul hβz hHz, map_add, map_smul, map_smul, ← h₃ z hz₀]
    module
  have hs : t * β z ∈ Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg ht.1 (hβI z).1, by nlinarith [ht.1, ht.2, (hβI z).1, (hβI z).2]⟩
  rw [hY]
  refine mul_le_apply_one_sub_smul_add_smul_add hc hs (h₁ z hz₀) (h₂ z hz₀) hm ?_
  -- The error term `t H J(Dβ)`.
  have hA : |H z| ≤ max A 0 * ‖z‖ * ‖fderiv ℝ f z‖ :=
    (h₅ z hz₀).trans (by gcongr; exact le_max_left _ _)
  have hB : ‖J z‖ ≤ max B 0 := (h₄ z hz₀).trans (le_max_left _ _)
  have hKm : K * (m / (K + 1)) ≤ m := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg ht.1]
  calc t * |H z| * ‖J z (fderiv ℝ β z)‖
      ≤ 1 * (max A 0 * ‖z‖ * ‖fderiv ℝ f z‖) * (max B 0 * ‖fderiv ℝ β z‖) := by
        gcongr
        · exact ht.2
        · exact (J z).le_opNorm_of_le le_rfl |>.trans (by gcongr)
    _ = K * (‖z‖ * ‖fderiv ℝ β z‖) * ‖fderiv ℝ f z‖ := by ring
    _ ≤ K * (m / (K + 1)) * ‖fderiv ℝ f z‖ := by gcongr; exact hβD z
    _ ≤ m * ‖fderiv ℝ f z‖ := mul_le_mul_of_nonneg_right hKm (norm_nonneg _)

end SymplecticGeometry

end
