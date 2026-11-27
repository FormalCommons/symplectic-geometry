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
# The second derivative of the square root

* `Real.iteratedDeriv_two_sqrt`: the second derivative of `√·` at `x > 0` is
  `-1 / (4 x √x)`. It is the case `a = c = 0`, `b = 1` of Tau Ceti's
  `TauCeti.deriv_deriv_sqrt_quadratic`.
* `Real.iteratedDeriv_two_comp_sqrt`: the second derivative of `f ∘ √·` at `t > 0`, for `f`
  that is `C²` at `√t`, by the chain rule `iteratedDeriv_comp_two`.
-/

public section

namespace Real

open TauCeti

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
