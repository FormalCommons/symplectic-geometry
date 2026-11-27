/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The second derivative of the square root

Mathlib gives the first derivative of `Real.sqrt` away from `0` (`Real.hasDerivAt_sqrt`). This
file adds the second one: `Real.iteratedDeriv_two_sqrt` says that at `x > 0` the second
derivative of `√·` is `-1 / (4 x √x)`.
-/

public section

open Filter Topology

namespace Real

/-- The second derivative of `√·` at `x > 0` is `-1 / (4 x √x)`. -/
theorem iteratedDeriv_two_sqrt {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 2 (√·) x = -1 / (4 * x * √x) := by
  have hev : deriv (√·) =ᶠ[𝓝 x] fun y ↦ (2 * √y)⁻¹ :=
    Filter.eventually_of_mem (Ioi_mem_nhds hx) fun y hy ↦ by
      rw [(hasDerivAt_sqrt (ne_of_gt hy)).deriv, one_div]
  have : 0 < √x := sqrt_pos.2 hx
  have h : HasDerivAt (fun y ↦ (2 * √y)⁻¹) _ x :=
    ((hasDerivAt_sqrt hx.ne').const_mul 2).fun_inv (by positivity)
  rw [iteratedDeriv_succ, iteratedDeriv_one, hev.deriv_eq, h.deriv]
  have hsq : √x ^ 2 = x := sq_sqrt hx.le
  field_simp
  rw [hsq]
  ring

end Real

end
