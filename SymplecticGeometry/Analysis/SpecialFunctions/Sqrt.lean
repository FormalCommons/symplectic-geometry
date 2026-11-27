/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Sqrt

import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import TauCeti.Analysis.Calculus.Deriv.Second

/-!
# Derivatives of the square root

* `Real.hasDerivAt_sqrt_sub` and `Real.deriv_sqrt_sub`: the map `r ↦ √(a r² - c)` has
  derivative `a r / √(a r² - c)` at each `r` with `a r² - c ≠ 0`.
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

end Real

end
