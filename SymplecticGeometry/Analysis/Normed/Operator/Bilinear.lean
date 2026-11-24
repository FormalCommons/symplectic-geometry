/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# The norm of evaluation at a vector

Evaluation at `v`, the continuous linear map `ContinuousLinearMap.apply 𝕜 F v` on `E →L[𝕜] F`,
has operator norm at most `‖v‖` (`ContinuousLinearMap.opNorm_apply_apply_le`).
-/

public section

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Evaluation at `v`, as a continuous linear map on `E →L[𝕜] F`, has operator norm at most
`‖v‖`. -/
theorem opNorm_apply_apply_le (v : E) : ‖apply 𝕜 F v‖ ≤ ‖v‖ :=
  opNorm_le_bound _ (norm_nonneg v) fun A => by
    rw [apply_apply, mul_comm]
    exact A.le_opNorm v

end ContinuousLinearMap

end
