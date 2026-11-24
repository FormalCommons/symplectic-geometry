/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# Second countability of σ-compact manifolds

A σ-compact space with charts in `H`, for a model with corners `I : ModelWithCorners 𝕜 E H` on a
second countable space `E`, is second countable
(`ModelWithCorners.secondCountableTopology_of_sigmaCompact`). It combines Mathlib's
`ModelWithCorners.secondCountableTopology` and `ChartedSpace.secondCountable_of_sigmaCompact`.
It is not an instance, since `SecondCountableTopology M` does not determine `I`.
-/

public section

namespace ModelWithCorners

variable {𝕜 E H : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] [SecondCountableTopology E]

/-- A σ-compact space with charts in the model space `H` of a model with corners on a second
countable space is second countable. -/
theorem secondCountableTopology_of_sigmaCompact (I : ModelWithCorners 𝕜 E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [SigmaCompactSpace M] : SecondCountableTopology M :=
  haveI := I.secondCountableTopology
  ChartedSpace.secondCountable_of_sigmaCompact H M

end ModelWithCorners

end
