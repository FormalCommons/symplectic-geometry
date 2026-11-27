/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Analytic.Order

/-!
# The order of vanishing of a line through the origin

For a nonzero vector `v` of a normed space `E` over a nontrivially normed field `𝕜`, the line
`t ↦ t • v` vanishes to order exactly one at `0`.

## Main results

* `analyticOrderAt_id_smul_const`: for `v ≠ 0`, `analyticOrderAt (fun t ↦ t • v) 0 = 1`.
-/

public section

/-- For a nonzero vector `v`, the line `t ↦ t • v` has a simple zero at `0`. -/
theorem analyticOrderAt_id_smul_const {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {v : E} (hv : v ≠ 0) :
    analyticOrderAt (fun t : 𝕜 ↦ t • v) 0 = 1 := by
  classical
  rw [analyticOrderAt_fun_smul_const (f := fun t : 𝕜 ↦ t) analyticAt_id, ite_eq_right hv]
  exact analyticOrderAt_id

end
