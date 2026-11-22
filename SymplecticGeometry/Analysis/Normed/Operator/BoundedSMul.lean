/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Bounded scalar multiplication on spaces of continuous linear maps

Scalar multiplication on the space `E →SL[σ₁₂] F` of continuous semilinear maps between
seminormed spaces, by a normed field `𝕜'` acting on `F`, is bounded for the operator norm:
`‖c • f‖ ≤ ‖c‖ * ‖f‖`. Mathlib gives this through `NormedSpace.toIsBoundedSMul` and
`ContinuousLinearMap.toNormedSpace`, but with Lean's default limit on nested instance problems,
instance search cannot use that route on iterated spaces such as `V →L[ℝ] V →L[ℝ] ℝ`.

The reason is that the operator-norm instances on `E →SL[σ₁₂] F` take `F`'s topology from a
`SeminormedAddCommGroup F` instance. Matching the conclusion of `NormedSpace.toIsBoundedSMul`
to the goal makes Lean solve a pending instance problem for the outer space, and that problem
needs a further pending one for the codomain `F` when `F` is itself a space of continuous
linear maps. Two levels of nesting are more than Lean allows by default.

The instance `ContinuousLinearMap.isBoundedSMul` states the conclusion on `E →SL[σ₁₂] F` itself,
so its pseudometric, zero and scalar action are syntactically those of the goal, and the outer
pending problem disappears. It is defined by the route above, so it agrees with it.

## Main results

* `ContinuousLinearMap.isBoundedSMul`: `IsBoundedSMul 𝕜' (E →SL[σ₁₂] F)`.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 𝕜₂ 𝕜' E F : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F]
  {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂] [NormedField 𝕜'] [NormedSpace 𝕜' F]
  [SMulCommClass 𝕜₂ 𝕜' F]

/-- Scalar multiplication by a normed field `𝕜'` acting on `F` is bounded on the space of
continuous semilinear maps `E →SL[σ₁₂] F` with the operator norm. -/
instance isBoundedSMul : IsBoundedSMul 𝕜' (E →SL[σ₁₂] F) :=
  NormedSpace.toIsBoundedSMul

end ContinuousLinearMap

end
