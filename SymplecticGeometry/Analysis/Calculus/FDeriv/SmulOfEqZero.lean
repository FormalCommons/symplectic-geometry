/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# The derivative of `c • f` at a zero of `f`

If `f` vanishes at `x` and has derivative `f'` there, then `y ↦ c y • f y` has derivative
`c x • f'` at `x` as soon as `c` is continuous at `x`: the term `(c y - c x) • f y` is the product
of a function tending to `0` with one that is `O(y - x)`. No differentiability of `c` is needed,
unlike in the product rule `HasFDerivAt.smul`.

## Main results

* `HasFDerivAt.smul_of_continuousAt_of_eq_zero`: the derivative of `c • f` at a zero of `f`,
  for `c` continuous there.
-/

public section

open Filter Asymptotics
open scoped Topology

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **The derivative of `c • f` at a zero of `f`.** If `f` has derivative `f'` at `x` and
vanishes there, and `c` is continuous at `x`, then `y ↦ c y • f y` has derivative `c x • f'`
at `x`. -/
theorem HasFDerivAt.smul_of_continuousAt_of_eq_zero {c : E → 𝕜} {f : E → F} {f' : E →L[𝕜] F}
    {x : E} (hc : ContinuousAt c x) (hf : HasFDerivAt f f' x) (hfx : f x = 0) :
    HasFDerivAt (fun y ↦ c y • f y) (c x • f') x := by
  have hc0 : (fun y ↦ c y - c x) =o[𝓝 x] fun _ ↦ (1 : 𝕜) :=
    (isLittleO_one_iff 𝕜).2 (tendsto_sub_nhds_zero_iff.2 hc)
  have hrem : (fun y ↦ (c y - c x) • f y) =o[𝓝 x] fun y ↦ y - x := by
    simpa [hfx] using hc0.smul_isBigO hf.isBigO_sub
  refine HasFDerivAt.of_isLittleO ((hf.const_smul (c x)).isLittleO.add hrem |>.congr_left ?_)
  intro y
  simp only [Pi.smul_apply, hfx, smul_zero, sub_zero, FunLike.coe_smul, sub_smul]
  abel

end
