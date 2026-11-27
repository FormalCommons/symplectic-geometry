/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Multilinear.Basic

/-!
# The norm of a flipped multilinear map

`ContinuousLinearMap.norm_flipMultilinear_le`: moving the linear argument of
`f : G →L[𝕜] ContinuousMultilinearMap 𝕜 E G'` to the values
(`ContinuousLinearMap.flipMultilinear`) does not increase the norm. Mathlib proves this inside
the definition of `ContinuousLinearMap.flipMultilinearEquiv`, without stating it.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [Fintype ι] {E : ι → Type*}
  [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] {G G' : Type*}
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G] [SeminormedAddCommGroup G'] [NormedSpace 𝕜 G']

/-- Flipping the arguments of `f : G →L[𝕜] ContinuousMultilinearMap 𝕜 E G'` does not increase
its norm. -/
theorem norm_flipMultilinear_le (f : G →L[𝕜] ContinuousMultilinearMap 𝕜 E G') :
    ‖f.flipMultilinear‖ ≤ ‖f‖ :=
  MultilinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

end ContinuousLinearMap

end
