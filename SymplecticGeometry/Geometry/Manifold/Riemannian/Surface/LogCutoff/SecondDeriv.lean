/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import TauCeti.Geometry.Manifold.Riemannian.Surface.LogCutoff.Profile

import TauCeti.Analysis.Calculus.Deriv.Second
import TauCeti.Analysis.SpecialFunctions.Exp.Deriv
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import SymplecticGeometry.Analysis.SpecialFunctions.SmoothTransition.Deriv

/-!
# The second derivative of the logarithmic cutoff profile

Tau Ceti's `TauCeti.logCutoffProfile ε δ` is a smooth function `ψ` that vanishes up to `ε`,
equals `1` from `δ` on, and whose derivative is at most `c₀ / (r log (δ / ε))`
(`TauCeti.deriv_logCutoffProfile_le`). This file proves the companion bound for the second
derivative: there is an absolute constant `c₁` with

`|ψ''(r)| ≤ c₁ / (r ^ 2 log (δ / ε))`

for `0 < 4ε ≤ δ` and every `r` (`TauCeti.exists_abs_iteratedDeriv_two_logCutoffProfile_le`).

For `r > 0`, write `Λ = log (δ / ε)`, `a = log₂ (r / ε)` and `b = log₂ (δ / r)`, and let `τ` be
`Real.smoothTransition`. Then `Λ r ψ'(r) = N(log r)` with
`N = τ(a) + τ(b) - 1 + a τ'(a) + b τ'(b)`, read as a function of `log r`: on `(0, δ / 2]` and on
`[2ε, ∞)` this is Tau Ceti's `TauCeti.deriv_logCutoffProfile_of_le_half` and
`TauCeti.deriv_logCutoffProfile_of_two_mul_le`. So `v = ψ ∘ exp` has `Λ v' = N`
(`TauCeti.deriv_comp_exp`), and Tau Ceti's change of variables
`TauCeti.sq_mul_deriv_deriv_comp_log` gives `Λ r ^ 2 ψ''(r) = N'(log r) - N(log r)`, with
`log 2 · N' = 2 τ'(a) + a τ''(a) - 2 τ'(b) - b τ''(b)`. Both `N` and `N'` are bounded
independently of `ε` and `δ`, since `τ'` and `τ''` are bounded and vanish outside `[0, 1]`.
Working in the logarithmic variable follows the proof of `TauCeti.deriv_logCutoffProfile_le`.

The bound is meant for the logarithmic cutoff `1 - ψ ∘ ρ` with which this library interpolates
between two strictly plurisubharmonic functions near a totally real submanifold, for
Proposition 3.26 of [CieliebakEliashberg2012]. There `ρ` is comparable to the squared distance
to the submanifold, and the bounds on `ψ'` and `ψ''` make the error terms of the interpolation
of order `1 / log (δ / ε)`.

## Main results

* `TauCeti.deriv_logCutoffProfile_of_pos`: the formula `Λ r ψ'(r) = N(log r)` for `r > 0`.
* `TauCeti.exists_abs_iteratedDeriv_two_logCutoffProfile_le`: the bound above.
* `TauCeti.mul_deriv_logCutoffProfile_le` and
  `TauCeti.exists_abs_sq_mul_deriv_deriv_logCutoffProfile_le`: the bounds on `r ψ'(r)` and
  `r ^ 2 ψ''(r)` by multiples of `1 / log (δ / ε)`, with the powers of `r` cleared, so that they
  hold at `r = 0` too.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012]
-/

public section

open Real Filter
open scoped Topology

namespace TauCeti

variable {ε δ : ℝ}

/-- For `0 < 4ε ≤ δ` and `s > 0`, the derivative of the logarithmic cutoff profile at `s` is
`N / (log (δ / ε) s)`, where, with `τ = Real.smoothTransition`, `a = (log s - log ε) / log 2`
and `b = (log δ - log s) / log 2`, `N = τ(a) + τ(b) - 1 + a τ'(a) + b τ'(b)`. -/
theorem deriv_logCutoffProfile_of_pos (hε : 0 < ε) (h4 : 4 * ε ≤ δ) {s : ℝ}
    (hs : 0 < s) :
    deriv (logCutoffProfile ε δ) s =
      (smoothTransition ((log s - log ε) / log 2) + smoothTransition ((log δ - log s) / log 2) -
          1 + (log s - log ε) / log 2 * deriv smoothTransition ((log s - log ε) / log 2) +
          (log δ - log s) / log 2 * deriv smoothTransition ((log δ - log s) / log 2)) /
        log (δ / ε) / s := by
  have hδ : 0 < δ := by linarith
  have h2 : 0 < log 2 := Real.log_pos one_lt_two
  rcases le_total s (δ / 2) with hsδ | hsδ
  · have hb : 1 ≤ (log δ - log s) / log 2 := by
      rw [le_div_iff₀ h2, one_mul, ← Real.log_div hδ.ne' hs.ne']
      exact Real.log_le_log two_pos ((le_div_iff₀ hs).2 (by linarith))
    rw [deriv_logCutoffProfile_of_le_half hs hsδ, smoothTransition.one_of_one_le hb,
      smoothTransition.deriv_of_one_le hb, Real.logb, Real.log_div hs.ne' hε.ne']
    field_simp
    ring
  · have ha : 1 ≤ (log s - log ε) / log 2 := by
      rw [le_div_iff₀ h2, one_mul, ← Real.log_div hs.ne' hε.ne']
      exact Real.log_le_log two_pos ((le_div_iff₀ hε).2 (by linarith))
    rw [deriv_logCutoffProfile_of_two_mul_le hε (by linarith),
      smoothTransition.one_of_one_le ha, smoothTransition.deriv_of_one_le ha, Real.logb,
      Real.log_div hδ.ne' hs.ne']
    field_simp
    ring

/-- **The second derivative of the logarithmic cutoff profile.** There is an absolute constant
`c₁` such that, for `0 < 4ε ≤ δ`, the second derivative of `logCutoffProfile ε δ` is at most
`c₁ / (u ^ 2 log (δ / ε))` in absolute value at every `u` (at `u = 0` both sides are `0`, under
Lean's convention `x / 0 = 0`). This is the second-order companion of
`TauCeti.deriv_logCutoffProfile_le`. -/
theorem exists_abs_iteratedDeriv_two_logCutoffProfile_le :
    ∃ c₁ : ℝ, ∀ {ε δ : ℝ}, 0 < ε → 4 * ε ≤ δ → ∀ u : ℝ,
      |iteratedDeriv 2 (logCutoffProfile ε δ) u| ≤ c₁ / (u ^ 2 * Real.log (δ / ε)) := by
  obtain ⟨M₁, hM₁⟩ := smoothTransition.exists_forall_norm_deriv_le
  obtain ⟨M₂, hM₂⟩ := smoothTransition.exists_forall_norm_mul_deriv_deriv_le
  have h2 : 0 < log 2 := Real.log_pos one_lt_two
  have hM₁0 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ 0)
  have hM₂0 : 0 ≤ M₂ := (norm_nonneg _).trans (hM₂ 0)
  refine ⟨1 + 2 * M₁ + (4 * M₁ + 2 * M₂) / log 2, fun {ε δ} hε h4 u ↦ ?_⟩
  have hΛ : 0 < log (δ / ε) := Real.log_pos ((one_lt_div hε).2 (by linarith))
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  rcases lt_or_ge u ε with hu | hu
  · -- Below `ε` the profile vanishes near `u`, and so does its derivative.
    have h0 : deriv (logCutoffProfile ε δ) =ᶠ[𝓝 u] fun _ ↦ 0 := by
      filter_upwards [gt_mem_nhds hu] with s hs
      exact deriv_logCutoffProfile_eq_zero_of_le (by linarith) hs.le
    rw [h0.deriv_eq, deriv_const, abs_zero]
    positivity
  have hu0 : 0 < u := hε.trans_le hu
  -- The numerator `N` of `Λ s ψ'(s)` in the variable `t = log s`, and its derivative.
  set τ := smoothTransition
  set a : ℝ → ℝ := fun t ↦ (t - log ε) / log 2
  set b : ℝ → ℝ := fun t ↦ (log δ - t) / log 2
  set N : ℝ → ℝ := fun t ↦
    τ (a t) + τ (b t) - 1 + a t * deriv τ (a t) + b t * deriv τ (b t)
  set N' : ℝ → ℝ := fun t ↦ (2 * deriv τ (a t) + a t * deriv (deriv τ) (a t) -
    2 * deriv τ (b t) - b t * deriv (deriv τ) (b t)) / log 2
  have hN (t : ℝ) : HasDerivAt N (N' t) t := by
    have ha : HasDerivAt a (1 / log 2) t := ((hasDerivAt_id t).sub_const _).div_const _
    have hb : HasDerivAt b (-1 / log 2) t := ((hasDerivAt_id t).const_sub _).div_const _
    have hd := ((((ha.smoothTransition.add hb.smoothTransition).sub_const 1).add
      (ha.mul ha.deriv_smoothTransition)).add (hb.mul hb.deriv_smoothTransition))
    refine hd.congr_deriv ?_
    simp only [N']
    field_simp
    ring
  -- In the variable `t = log s`: `ψ = v ∘ log` on `(0, ∞)` for `v = ψ ∘ exp`, and `Λ v' = N`.
  set v : ℝ → ℝ := fun t ↦ logCutoffProfile ε δ (exp t)
  have hv : deriv v = fun t ↦ N t / log (δ / ε) := by
    funext t
    rw [deriv_comp_exp, deriv_logCutoffProfile_of_pos hε h4 (exp_pos t), log_exp, smul_eq_mul,
      mul_div_cancel₀ _ (exp_pos t).ne']
  have hv' : deriv (deriv v) = fun t ↦ N' t / log (δ / ε) := by
    rw [hv]
    funext t
    exact ((hN t).div_const _).deriv
  have hev : logCutoffProfile ε δ =ᶠ[𝓝 u] fun s ↦ v (log s) := by
    filter_upwards [lt_mem_nhds hu0] with s hs
    simp only [v, exp_log hs]
  have h := sq_mul_deriv_deriv_comp_log (v := v)
    (by rw [hv]; exact ((hN _).div_const _).differentiableAt) hu0.ne'
  rw [hv', hv] at h
  -- The bounds on `N` and `N'`.
  have hτ' (x : ℝ) : |deriv τ x| ≤ M₁ := by simpa only [Real.norm_eq_abs] using hM₁ x
  have hxτ' (x : ℝ) : |x * deriv τ x| ≤ M₁ :=
    (smoothTransition.abs_mul_deriv_le_deriv x).trans ((le_abs_self _).trans (hτ' x))
  have hxτ'' (x : ℝ) : |x * deriv (deriv τ) x| ≤ M₂ := by
    simpa only [Real.norm_eq_abs] using hM₂ x
  have hNle : |N (log u)| ≤ 1 + 2 * M₁ := by
    have ha := abs_le.1 (hxτ' (a (log u)))
    have hb := abs_le.1 (hxτ' (b (log u)))
    rw [abs_le]
    constructor <;> linarith [smoothTransition.nonneg (a (log u)),
      smoothTransition.nonneg (b (log u)), smoothTransition.le_one (a (log u)),
      smoothTransition.le_one (b (log u))]
  have hN'le : |N' (log u)| ≤ (4 * M₁ + 2 * M₂) / log 2 := by
    have ha := abs_le.1 (hτ' (a (log u)))
    have hb := abs_le.1 (hτ' (b (log u)))
    have ha' := abs_le.1 (hxτ'' (a (log u)))
    have hb' := abs_le.1 (hxτ'' (b (log u)))
    simp only [N']
    rw [abs_div, abs_of_pos h2]
    gcongr
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have heq : deriv (deriv fun s ↦ v (log s)) u =
      (N' (log u) - N (log u)) / (u ^ 2 * log (δ / ε)) := by
    rw [eq_div_iff (mul_pos (pow_pos hu0 2) hΛ).ne']
    field_simp at h
    linear_combination h
  rw [hev.deriv.deriv_eq, heq, abs_div, abs_of_pos (mul_pos (pow_pos hu0 2) hΛ)]
  gcongr
  calc |N' (log u) - N (log u)| ≤ |N' (log u)| + |N (log u)| := abs_sub _ _
    _ ≤ _ := by linarith

/-- For `0 < 4ε ≤ δ` and `r ≥ 0`, the logarithmic cutoff profile `ψ = logCutoffProfile ε δ`
satisfies `r ψ'(r) ≤ c₀ / log (δ / ε)`, where `c₀ = logCutoffConst`: the bound
`TauCeti.deriv_logCutoffProfile_le` with `r` cleared from the denominator. -/
theorem mul_deriv_logCutoffProfile_le (hε : 0 < ε) (h4 : 4 * ε ≤ δ) {r : ℝ} (hr : 0 ≤ r) :
    r * deriv (logCutoffProfile ε δ) r ≤ logCutoffConst / Real.log (δ / ε) := by
  have hΛ : 0 < log (δ / ε) := Real.log_pos ((one_lt_div hε).2 (by linarith))
  rcases hr.eq_or_lt with rfl | hr0
  · rw [zero_mul]
    exact div_nonneg (zero_le_one.trans one_le_logCutoffConst) hΛ.le
  have h := deriv_logCutoffProfile_le hε h4 hr
  rw [le_div_iff₀ (mul_pos hr0 hΛ)] at h
  rw [le_div_iff₀ hΛ]
  linarith

/-- There is an absolute constant `c₁` such that, for `0 < 4ε ≤ δ` and every `r`, the
logarithmic cutoff profile `ψ = logCutoffProfile ε δ` satisfies
`|r ^ 2 ψ''(r)| ≤ c₁ / log (δ / ε)`: the bound
`TauCeti.exists_abs_iteratedDeriv_two_logCutoffProfile_le` with `r ^ 2` cleared from the
denominator. -/
theorem exists_abs_sq_mul_deriv_deriv_logCutoffProfile_le :
    ∃ c₁ : ℝ, ∀ {ε δ : ℝ}, 0 < ε → 4 * ε ≤ δ → ∀ r : ℝ,
      |r ^ 2 * deriv (deriv (logCutoffProfile ε δ)) r| ≤ c₁ / Real.log (δ / ε) := by
  obtain ⟨c₁, hc₁⟩ := exists_abs_iteratedDeriv_two_logCutoffProfile_le
  -- `c₁ ≥ 0`, from the bound at `ε = r = 1` and `δ = 4`.
  have hc₁0 : 0 ≤ c₁ := by
    have h := (abs_nonneg _).trans (hc₁ one_pos (by norm_num : 4 * (1 : ℝ) ≤ 4) 1)
    rw [one_pow, one_mul, div_one] at h
    exact ((div_nonneg_iff.1 h).resolve_right fun h' ↦
      (Real.log_pos (by norm_num : (1 : ℝ) < 4)).not_ge h'.2).1
  refine ⟨c₁, fun {ε δ} hε h4 r ↦ ?_⟩
  have hΛ : 0 < log (δ / ε) := Real.log_pos ((one_lt_div hε).2 (by linarith))
  rcases eq_or_ne r 0 with rfl | hr0
  · simpa using div_nonneg hc₁0 hΛ.le
  have h := hc₁ hε h4 r
  have hr2 : 0 < r ^ 2 := by positivity
  rw [iteratedDeriv_succ, iteratedDeriv_one, le_div_iff₀ (mul_pos hr2 hΛ)] at h
  rw [le_div_iff₀ hΛ, abs_mul, abs_of_pos hr2]
  linarith

end TauCeti

end
