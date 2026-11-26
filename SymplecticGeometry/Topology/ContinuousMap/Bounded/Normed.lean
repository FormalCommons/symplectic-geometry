/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# The operator norm of evaluation on bounded continuous functions

Mathlib defines point evaluation `BoundedContinuousFunction.evalCLM 𝕜 x : (α →ᵇ β) →L[𝕜] β`
but gives no bound on its operator norm. This file adds that bound.

## Main results

* `BoundedContinuousFunction.norm_evalCLM_le_one`: evaluation at a point has operator norm at
  most `1`.

The statement and proof follow Tau Ceti's `ContinuousMap.norm_evalCLM_le_one`
(`TauCeti/Topology/ContinuousMap/Compact.lean`), stated there for `C(K, E)` with `K` compact.
-/

public section

namespace BoundedContinuousFunction

variable {α 𝕜 β : Type*} [TopologicalSpace α] [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup β] [NormedSpace 𝕜 β]

/-- Evaluation at a point, as a continuous linear map on bounded continuous functions, has
operator norm at most `1`. -/
theorem norm_evalCLM_le_one (x : α) : ‖evalCLM 𝕜 (β := β) x‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f ↦ by
    simpa only [evalCLM_apply, one_mul] using f.norm_coe_le_norm x

end BoundedContinuousFunction

end
