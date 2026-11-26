/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Operator norm of a coordinate projection

For a finite family of seminormed spaces `φ i` over a nontrivially normed field, the product
`Π i, φ i` carries the sup norm, so each coordinate projection
`ContinuousLinearMap.proj i : (Π i, φ i) →L[𝕜] φ i` has operator norm at most `1`. This is the
analogue for finite Pi types of Mathlib's `ContinuousLinearMap.norm_fst_le` and
`ContinuousLinearMap.norm_snd_le` for binary products.

## Main results

* `ContinuousLinearMap.norm_proj_le`: `‖ContinuousLinearMap.proj i‖ ≤ 1`.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [Fintype ι] {φ : ι → Type*}
  [∀ i, SeminormedAddCommGroup (φ i)] [∀ i, NormedSpace 𝕜 (φ i)]

/-- A coordinate projection of a finite product, with the sup norm, has operator norm at
most `1`. -/
theorem norm_proj_le (i : ι) : ‖proj (R := 𝕜) (φ := φ) i‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one fun v ↦ by simpa using norm_le_pi_norm v i

end ContinuousLinearMap

end
