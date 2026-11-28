/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.Shape

import SymplecticGeometry.Geometry.Manifold.Riemannian.Surface.LogCutoff.SecondDeriv
import TauCeti.Geometry.Manifold.Riemannian.Surface.LogCutoff.Profile

/-!
# The `i`-convex model handle

This file is for the model handle of Cieliebak and Eliashberg's Theorem 4.2 for the standard
complex structure on `ℂᵏ × ℂᵐ`, in the shape coordinates `s = |x|²` and `t = |y|² + |w|²` of
`Surround/Shape.lean`. So far it holds the separable interpolation below and its strictly
plurisubharmonic consequence.

## The separable interpolation

In the proof of Theorem 4.2 the book joins the functions `64 t - s` and `a t - s` by its
Proposition 3.26. Both are of the form `g t - s`, and by
`SymplecticGeometry.isStrictlyPlurisubharmonicAt_shape` such a function is strictly
plurisubharmonic wherever `g' + 2 min(g'', 0) t > 1`. So the interpolation reduces to one real
variable, and Proposition 3.26 is not used.

* `SymplecticGeometry.eventually_exists_contDiff_eqOn_mul_Iic_eqOn_mul_Ici`: for slopes
  `1 < b` and `1 < a` and `0 < L`, for every small enough `t₀ > 0` there is a smooth `g` equal to
  `b t` on `(-∞, t₀]` and to `a t` on `[L, ∞)` with `1 < g' t + 2 min(g'' t, 0) t` for all
  `t ≥ 0`. It is `g t = t (b + (a - b) ψ t)`, with `ψ` Tau Ceti's logarithmic cutoff
  `TauCeti.logCutoffProfile t₀ L`, which is `0` up to `t₀` and `1` from `L` on. Then
  `g' = b + (a - b) (ψ + t ψ')` and `t g'' = (a - b) (2 t ψ' + t² ψ'')`. By
  `TauCeti.mul_deriv_logCutoffProfile_le` and
  `TauCeti.exists_abs_sq_mul_deriv_deriv_logCutoffProfile_le`, both `t ψ'` and `t² ψ''` are
  `O(1 / Λ)` for `Λ = log (L / t₀)`, which is large once `t₀` is small, while `b + (a - b) ψ`
  lies between `a` and `b`. This `g` need not be concave.
* `SymplecticGeometry.isStrictlyPlurisubharmonicAt_sub_shape_fst`: if
  `g' + 2 min(g'', 0) t > 1` at `t = t p`, then `g (t q) - s q` is strictly plurisubharmonic at
  `p`; the case `f s = -s` of `SymplecticGeometry.isStrictlyPlurisubharmonicAt_shape`.
* `SymplecticGeometry.eventually_exists_contDiff_isStrictlyPlurisubharmonicAt_sub_shape_fst`:
  the two together, for `b = 64` and `L = γ²`, the form in which the proof of Theorem 4.2 joins
  `64 t - s` to `a t - s` on `{γ² ≤ t}`.

## References

* [K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012]
-/

public section

open Real Set Filter Topology TauCeti
open scoped ContDiff

namespace SymplecticGeometry

variable {k m : ℕ}

/-- The first derivative of `t ↦ t (b + c f t)`. -/
private theorem deriv_mul_const_add_const_mul {f : ℝ → ℝ} (hf : Differentiable ℝ f) (b c : ℝ) :
    deriv (fun t ↦ t * (b + c * f t)) = fun t ↦ b + c * f t + c * (t * deriv f t) := by
  funext t
  refine ((hasDerivAt_id' t).mul (((hf t).hasDerivAt.const_mul c).const_add b)).deriv.trans ?_
  ring

/-- The second derivative of `t ↦ t (b + c f t)`. -/
private theorem iteratedDeriv_two_mul_const_add_const_mul {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hf' : Differentiable ℝ (deriv f)) (b c t : ℝ) :
    iteratedDeriv 2 (fun t ↦ t * (b + c * f t)) t =
      2 * c * deriv f t + c * (t * deriv (deriv f) t) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_mul_const_add_const_mul hf]
  refine ((((hf t).hasDerivAt.const_mul c).const_add b).add
    (((hasDerivAt_id' t).mul (hf' t).hasDerivAt).const_mul c)).deriv.trans ?_
  ring

/-- The closing estimate: if the main term `m` is at least `μ`, and `P = t ψ'` and
`Q = t² ψ''` are bounded by `c₀ / Λ` and `c₁ / Λ` with `Λ` large, then the error terms
`c P + 2 min (c (2 P + Q)) 0` do not bring `m` down to `1`. -/
private theorem one_lt_add_add_two_mul_min {μ m c P Q c₀ c₁ Λ : ℝ} (hΛ : 0 < Λ) (hm : μ ≤ m)
    (hP₀ : 0 ≤ P) (hP : P ≤ c₀ / Λ) (hQ : |Q| ≤ c₁ / Λ)
    (hΛc : |c| * (5 * c₀ + 2 * c₁) < (μ - 1) * Λ) :
    1 < m + c * P + 2 * min (c * (2 * P + Q)) 0 := by
  have hcP : |c * P| ≤ |c| * (c₀ / Λ) := by
    rw [abs_mul, abs_of_nonneg hP₀]
    gcongr
  have hce : |c * (2 * P + Q)| ≤ |c| * ((2 * c₀ + c₁) / Λ) := by
    rw [abs_mul]
    gcongr
    calc |2 * P + Q| ≤ |2 * P| + |Q| := abs_add_le _ _
      _ ≤ 2 * (c₀ / Λ) + c₁ / Λ := by
        rw [abs_mul, abs_two, abs_of_nonneg hP₀]
        linarith
      _ = (2 * c₀ + c₁) / Λ := by ring
  have hmin : -|c * (2 * P + Q)| ≤ min (c * (2 * P + Q)) 0 :=
    le_min (neg_abs_le _) (neg_nonpos.2 (abs_nonneg _))
  have hsmall : |c| * (c₀ / Λ) + 2 * (|c| * ((2 * c₀ + c₁) / Λ)) < μ - 1 := by
    have : |c| * (c₀ / Λ) + 2 * (|c| * ((2 * c₀ + c₁) / Λ)) = |c| * (5 * c₀ + 2 * c₁) / Λ := by
      field_simp
      ring
    rw [this, div_lt_iff₀ hΛ]
    exact hΛc
  linarith [neg_abs_le (c * P)]

/-- **The separable interpolation between two slopes.** For slopes `1 < b` and `1 < a` and
`0 < L`, for every small enough `t₀ > 0` there is a smooth `g : ℝ → ℝ` that is `b t` on
`(-∞, t₀]`, is `a t` on `[L, ∞)`, and satisfies `1 < g' t + 2 min(g'' t, 0) t` for every
`t ≥ 0`. -/
theorem eventually_exists_contDiff_eqOn_mul_Iic_eqOn_mul_Ici {a b L : ℝ} (ha : 1 < a)
    (hb : 1 < b) (hL : 0 < L) :
    ∀ᶠ t₀ in 𝓝[>] 0, ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ EqOn g (fun t ↦ b * t) (Iic t₀) ∧
      EqOn g (fun t ↦ a * t) (Ici L) ∧
      ∀ t, 0 ≤ t → 1 < deriv g t + 2 * min (iteratedDeriv 2 g t) 0 * t := by
  obtain ⟨c₁, hc₁⟩ := exists_abs_sq_mul_deriv_deriv_logCutoffProfile_le
  set c := a - b
  set μ := min a b
  have hμ : 0 < μ - 1 := sub_pos.2 (lt_min ha hb)
  -- Take `t₀ < L / 4` with `Λ = log (L / t₀)` larger than `Λ₀`.
  set Λ₀ := |c| * (5 * logCutoffConst + 2 * c₁) / (μ - 1)
  filter_upwards [Ioo_mem_nhdsGT (exp_pos (log L - Λ₀)), Ioo_mem_nhdsGT (by positivity : 0 < L / 4)]
    with t₀ ht₀ ht₀'
  have ht₀₀ : 0 < t₀ := ht₀.1
  have h4 : 4 * t₀ ≤ L := by linarith [ht₀'.2]
  have h2 : 2 * t₀ ≤ L := by linarith
  set ψ := logCutoffProfile t₀ L
  set Λ := log (L / t₀)
  have hΛ₀ : 0 < Λ := log_pos ((one_lt_div ht₀₀).2 (by linarith))
  have hΛc : |c| * (5 * logCutoffConst + 2 * c₁) < (μ - 1) * Λ := by
    have := (log_lt_iff_lt_exp ht₀₀).2 ht₀.2
    rw [← div_lt_iff₀' hμ, show Λ = log L - log t₀ from log_div hL.ne' ht₀₀.ne']
    linarith
  have hψ : ContDiff ℝ ∞ ψ := contDiff_logCutoffProfile hL.ne'
  have hψ₁ : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hψ₂ : Differentiable ℝ (deriv ψ) := by
    simpa using hψ.differentiable_iteratedDeriv 1 (by simp)
  -- The function is `g t = t (b + c ψ t)`.
  refine ⟨fun t ↦ t * (b + c * ψ t), contDiff_id.mul (contDiff_const.add (contDiff_const.mul hψ)),
    fun t ht ↦ ?_, fun t ht ↦ ?_, fun t ht ↦ ?_⟩
  · simp [ψ, logCutoffProfile_eq_zero_of_le h2 (mem_Iic.1 ht), mul_comm]
  · simp only [ψ, logCutoffProfile_eq_one_of_ge ht₀₀ h2 (mem_Ici.1 ht), c]
    ring
  rw [deriv_mul_const_add_const_mul hψ₁, iteratedDeriv_two_mul_const_add_const_mul hψ₁ hψ₂,
    mul_assoc, min_mul_of_nonneg _ _ ht, zero_mul]
  -- The main term `b + c ψ` lies between `a` and `b`.
  have hmain : μ ≤ b + c * ψ t := by
    have := logCutoffProfile_nonneg ht₀₀ h2 t
    have := logCutoffProfile_le_one ht₀₀ h2 t
    have h₁ : μ ≤ a := min_le_left a b
    have h₂ : μ ≤ b := min_le_right a b
    simp only [c]
    nlinarith
  -- `t ψ'` and `t² ψ''` are `O(1 / Λ)`.
  have H := one_lt_add_add_two_mul_min hΛ₀ hmain
    (mul_nonneg ht (deriv_logCutoffProfile_nonneg ht₀₀ h2 t))
    (mul_deriv_logCutoffProfile_le ht₀₀ h4 ht) (hc₁ ht₀₀ h4 t) hΛc
  convert H using 4
  ring

/-- If `g` is `C²` at `t = t p` and `1 < g' t + 2 min(g'' t, 0) t`, then
`q ↦ g (t q) - s q`, in the shape coordinates `s` and `t`, is strictly plurisubharmonic at
`p`. -/
theorem isStrictlyPlurisubharmonicAt_sub_shape_fst {g : ℝ → ℝ}
    {p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)}
    (hg : ContDiffAt ℝ 2 g (shape p).2)
    (h : 1 < deriv g (shape p).2 + 2 * min (iteratedDeriv 2 g (shape p).2) 0 * (shape p).2) :
    IsStrictlyPlurisubharmonicAt (fun q ↦ g (shape q).2 - (shape q).1) p := by
  have hf₁ (s : ℝ) : deriv (fun s : ℝ ↦ -s) s = -1 := by simp
  have hf₂ (s : ℝ) : iteratedDeriv 2 (fun s : ℝ ↦ -s) s = 0 := by simp [iteratedDeriv_succ]
  have H := isStrictlyPlurisubharmonicAt_shape (f := fun s ↦ -s) (g := g) (p := p)
    (by fun_prop) hg (by rw [hf₁, hf₂, min_self, mul_zero, zero_mul, add_zero]; linarith)
    (fun _ ↦ by linarith)
  convert H using 2 with q
  ring

/-- For `1 < a` and `0 < γ`, for every small enough `t₀ > 0` there is a smooth `g` that is
`64 t` on `(-∞, t₀]` and `a t` on `[γ², ∞)`, with `1 < g' t + 2 min(g'' t, 0) t` for `t ≥ 0`,
such that `q ↦ g (t q) - s q` is strictly plurisubharmonic at every point of `ℂᵏ × ℂᵐ`. It
joins `64 t - s` to the model handle function `a t - s`. -/
theorem eventually_exists_contDiff_isStrictlyPlurisubharmonicAt_sub_shape_fst {a γ : ℝ}
    (ha : 1 < a) (hγ : 0 < γ) :
    ∀ᶠ t₀ in 𝓝[>] 0, ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ EqOn g (fun t ↦ 64 * t) (Iic t₀) ∧
      EqOn g (fun t ↦ a * t) (Ici (γ ^ 2)) ∧
      (∀ t, 0 ≤ t → 1 < deriv g t + 2 * min (iteratedDeriv 2 g t) 0 * t) ∧
      ∀ p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m),
        IsStrictlyPlurisubharmonicAt (fun q ↦ g (shape q).2 - (shape q).1) p := by
  filter_upwards [eventually_exists_contDiff_eqOn_mul_Iic_eqOn_mul_Ici ha
    (by norm_num : (1 : ℝ) < 64)
    (pow_pos hγ 2)] with t₀ ⟨g, hg, h₁, h₂, h⟩
  exact ⟨g, hg, h₁, h₂, h, fun p ↦ isStrictlyPlurisubharmonicAt_sub_shape_fst
    (hg.contDiffAt.of_le (by norm_num)) (h _ (shape_snd_nonneg p))⟩

end SymplecticGeometry

end
