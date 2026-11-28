/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Sqrt

import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import TauCeti.Analysis.Calculus.Deriv.Second
import TauCeti.Analysis.Real.Sqrt

/-!
# Derivatives of the square root

* `Real.hasDerivAt_sqrt_sub` and `Real.deriv_sqrt_sub`: the map `r ↦ √(a r² - c)` has
  derivative `a r / √(a r² - c)` at each `r` with `a r² - c ≠ 0`.
* `Real.deriv_sqrt_mul_sq_add_le`: for `0 ≤ a` and `0 ≤ c`, the slope of `r ↦ √(a r² + c)` is at
  most `√a` at every `r`.
* `Real.iteratedDeriv_two_sqrt_sub`: its second derivative is `-a c / √(a r² - c)³` at each
  `r` with `a r² - c > 0`. `Real.iteratedDeriv_two_sqrt_quadratic` is the case `c = -ℓ²`:
  the second derivative of `r ↦ √(ℓ² + a r²)` is `a ℓ² / √(ℓ² + a r²)³` where
  `ℓ² + a r² > 0`. The first lemma is the case `b = 0` of Tau Ceti's
  `TauCeti.deriv_deriv_sqrt_quadratic`.
* `Real.iteratedDeriv_two_sqrt`: the second derivative of `√·` at `x > 0` is
  `-1 / (4 x √x)`. It is the case `a = c = 0`, `b = 1` of Tau Ceti's
  `TauCeti.deriv_deriv_sqrt_quadratic`.
* `Real.iteratedDeriv_two_comp_sqrt`: the second derivative of `f ∘ √·` at `t > 0`, for `f`
  that is `C²` at `√t`, by the chain rule `iteratedDeriv_comp_two`.
* `Real.tendsto_deriv_sqrt_sub`: for `0 < a` and `0 < δ`, the slope of `r ↦ √(a r² - a δ²)`
  tends to `+∞` at `δ`, by `Real.deriv_sqrt_sub`.
-/

public section

namespace Real

open TauCeti

/-- The map `r ↦ √(a r² - c)` has derivative `a r / √(a r² - c)` at each `r` with
`a r² - c ≠ 0`. -/
theorem hasDerivAt_sqrt_sub {a c r : ℝ} (h : a * r ^ 2 - c ≠ 0) :
    HasDerivAt (fun r ↦ √(a * r ^ 2 - c)) (a * r / √(a * r ^ 2 - c)) r := by
  have hq : HasDerivAt (fun r ↦ a * r ^ 2 - c) (a * (2 * r)) r := by
    simpa using ((hasDerivAt_pow 2 r).const_mul a).sub_const c
  convert hq.sqrt h using 1
  rcases h.lt_or_gt with h | h
  · simp [sqrt_eq_zero'.2 h.le]
  · field_simp

/-- The derivative of `r ↦ √(a r² - c)` at each `r` with `a r² - c ≠ 0` is
`a r / √(a r² - c)`. -/
theorem deriv_sqrt_sub {a c r : ℝ} (h : a * r ^ 2 - c ≠ 0) :
    deriv (fun r ↦ √(a * r ^ 2 - c)) r = a * r / √(a * r ^ 2 - c) :=
  (hasDerivAt_sqrt_sub h).deriv

/-- For `0 ≤ a` and `0 ≤ c`, the slope of `r ↦ √(a r² + c)` at each `r` is at most `√a`. -/
theorem deriv_sqrt_mul_sq_add_le {a c r : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) :
    deriv (fun r ↦ √(a * r ^ 2 + c)) r ≤ √a := by
  rcases (add_nonneg (mul_nonneg ha (sq_nonneg r)) hc).lt_or_eq with h | h
  · have e : (fun r ↦ √(a * r ^ 2 + c)) = fun r ↦ √(a * r ^ 2 - -c) := by
      simp only [sub_neg_eq_add]
    rw [e, deriv_sqrt_sub (by rw [sub_neg_eq_add]; exact h.ne'), sub_neg_eq_add,
      div_le_iff₀ (sqrt_pos.2 h), ← sqrt_mul ha]
    exact le_sqrt_of_sq_le (by nlinarith [mul_nonneg ha hc])
  · -- Where `a r² + c = 0` the map has a local minimum, so its slope there is `0`.
    have hmin : IsLocalMin (fun r ↦ √(a * r ^ 2 + c)) r :=
      Filter.Eventually.of_forall fun x ↦ by simp only [← h, sqrt_zero, sqrt_nonneg]
    by_cases hd : DifferentiableAt ℝ (fun r ↦ √(a * r ^ 2 + c)) r
    · rw [hmin.deriv_eq_zero]
      exact sqrt_nonneg a
    · rw [deriv_zero_of_not_differentiableAt hd]
      exact sqrt_nonneg a

/-- The second derivative of `r ↦ √(a r² - c)` at each `r` with `a r² - c > 0` is
`-a c / √(a r² - c)³`. -/
theorem iteratedDeriv_two_sqrt_sub {a c r : ℝ} (h : 0 < a * r ^ 2 - c) :
    iteratedDeriv 2 (fun r ↦ √(a * r ^ 2 - c)) r = -a * c / √(a * r ^ 2 - c) ^ 3 := by
  have e (s : ℝ) : a * s ^ 2 - c = -c + 0 * s + a * s ^ 2 := by ring
  simp only [e, iteratedDeriv_succ, iteratedDeriv_zero]
  rw [deriv_deriv_sqrt_quadratic (by linarith [e r]), ← e, pow_succ _ 2, sq_sqrt h.le]
  field_simp
  ring

/-- The second derivative of `r ↦ √(ℓ² + a r²)` at each `r` with `ℓ² + a r² > 0` is
`a ℓ² / √(ℓ² + a r²)³`. -/
theorem iteratedDeriv_two_sqrt_quadratic {a ℓ r : ℝ} (h : 0 < ℓ ^ 2 + a * r ^ 2) :
    iteratedDeriv 2 (fun r ↦ √(ℓ ^ 2 + a * r ^ 2)) r = a * ℓ ^ 2 / √(ℓ ^ 2 + a * r ^ 2) ^ 3 := by
  have e : ∀ r : ℝ, ℓ ^ 2 + a * r ^ 2 = a * r ^ 2 - -ℓ ^ 2 := fun r ↦ by ring
  simp only [e]
  rw [iteratedDeriv_two_sqrt_sub (by linarith [e r])]
  ring

/-- The second derivative of `√·` at `x > 0` is `-1 / (4 x √x)`. -/
theorem iteratedDeriv_two_sqrt {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 2 (√·) x = -1 / (4 * x * √x) := by
  simpa [iteratedDeriv_succ] using
    deriv_deriv_sqrt_quadratic (a := 0) (b := 1) (c := 0) (t := x) (by simpa using hx)

/-- The second derivative of `f ∘ √·` at `t > 0`, for `f` that is `C²` at `√t`:
`f''(√t) / (4 t) - f'(√t) / (4 t √t)`. -/
theorem iteratedDeriv_two_comp_sqrt {f : ℝ → ℝ} {t : ℝ}
    (hf : ContDiffAt ℝ 2 f (√t)) (ht : 0 < t) :
    iteratedDeriv 2 (f ∘ fun t ↦ √t) t =
      iteratedDeriv 2 f (√t) / (4 * t) - deriv f (√t) / (4 * t * √t) := by
  rw [iteratedDeriv_comp_two hf (contDiffAt_sqrt ht.ne'), iteratedDeriv_two_sqrt ht,
    (hasDerivAt_sqrt ht.ne').deriv]
  have hsq : √t ^ 2 = t := sq_sqrt ht.le
  have : 0 < √t := sqrt_pos.2 ht
  field_simp
  linear_combination (-4 * iteratedDeriv 2 f (√t)) * hsq

open Filter Set Topology in
/-- The slope of `r ↦ √(a r² - a δ²)` tends to `+∞` at `δ`, for `0 < a` and `0 < δ`: the
shape has a vertical tangent at `δ`. -/
theorem tendsto_deriv_sqrt_sub {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    Tendsto (deriv fun r ↦ √(a * r ^ 2 - a * δ ^ 2)) (𝓝[>] δ) atTop := by
  have hpos : ∀ r ∈ Ioi δ, 0 < a * r ^ 2 - a * δ ^ 2 := fun r (hr : δ < r) ↦ by
    have : δ ^ 2 < r ^ 2 := by gcongr
    nlinarith
  have hc : Continuous fun r ↦ a * r ^ 2 - a * δ ^ 2 := by fun_prop
  have h₀ : Tendsto (fun r ↦ √(a * r ^ 2 - a * δ ^ 2)) (𝓝[>] δ) (𝓝[>] 0) :=
    tendsto_sqrt_nhdsGT_zero.comp <| tendsto_nhdsWithin_iff.2
      ⟨(hc.tendsto' δ 0 (sub_self _)).mono_left nhdsWithin_le_nhds,
        eventually_nhdsWithin_of_forall hpos⟩
  have h₁ : Tendsto (fun r ↦ a * r) (𝓝[>] δ) (𝓝 (a * δ)) :=
    ((continuous_const.mul continuous_id).tendsto δ).mono_left nhdsWithin_le_nhds
  refine (h₁.pos_mul_atTop (mul_pos ha hδ) (tendsto_inv_nhdsGT_zero.comp h₀)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [deriv_sqrt_sub (hpos r hr).ne', Function.comp_apply, div_eq_mul_inv]

end Real

end
