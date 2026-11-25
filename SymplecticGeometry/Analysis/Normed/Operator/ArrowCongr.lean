/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# The norm of conjugation by continuous linear equivalences

For continuous linear equivalences `e₁ : E ≃L[𝕜] F` and `e₂ : E' ≃L[𝕜] F'`, Mathlib's
`ContinuousLinearEquiv.arrowCongr e₁ e₂` sends `X : E →L[𝕜] E'` to `e₂ ∘ X ∘ e₁⁻¹`. This file
bounds its operator norm.

## Main results

* `ContinuousLinearEquiv.norm_arrowCongr_le`: the operator norm of `e₁.arrowCongr e₂` is at most
  `‖e₂‖ * ‖e₁⁻¹‖`.
-/

public section

namespace ContinuousLinearEquiv

variable {𝕜 E F E' F' : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']

/-- The map `X ↦ e₂ ∘ X ∘ e₁⁻¹` between spaces of continuous linear maps has operator norm at most
`‖e₂‖ * ‖e₁⁻¹‖`. -/
theorem norm_arrowCongr_le (e₁ : E ≃L[𝕜] F) (e₂ : E' ≃L[𝕜] F') :
    ‖((e₁.arrowCongr e₂ : (E →L[𝕜] E') ≃L[𝕜] (F →L[𝕜] F')) : (E →L[𝕜] E') →L[𝕜] (F →L[𝕜] F'))‖ ≤
      ‖(e₂ : E' →L[𝕜] F')‖ * ‖(e₁.symm : F →L[𝕜] E)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun X ↦ ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w ↦ ?_
  rw [ContinuousLinearEquiv.coe_coe, arrowCongr_apply]
  calc ‖e₂ (X (e₁.symm w))‖ ≤ ‖(e₂ : E' →L[𝕜] F')‖ * (‖X‖ * (‖(e₁.symm : F →L[𝕜] E)‖ * ‖w‖)) :=
        (e₂ : E' →L[𝕜] F').le_opNorm_of_le
          (X.le_opNorm_of_le ((e₁.symm : F →L[𝕜] E).le_opNorm w))
    _ = ‖(e₂ : E' →L[𝕜] F')‖ * ‖(e₁.symm : F →L[𝕜] E)‖ * ‖X‖ * ‖w‖ := by ring

end ContinuousLinearEquiv

end
