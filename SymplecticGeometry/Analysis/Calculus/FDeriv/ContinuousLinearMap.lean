/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Norm of the derivative of a field of linear maps applied to a fixed vector

For a field `c : E → F →L[𝕜] G` of continuous linear maps, differentiable at `x`, and a fixed
vector `v`, the derivative at `x` of `y ↦ c y v` is the derivative of `c` at `x` flipped and
applied to `v` (Mathlib's `fderiv_clm_apply`). Since flipping preserves the operator norm, its norm
is at most `‖fderiv 𝕜 c x‖ * ‖v‖`. Tau Ceti's `TauCeti.fderiv_clm_apply_const_apply` gives the
pointwise form of the identity behind this bound.

## Main results

* `SymplecticGeometry.norm_fderiv_clm_apply_const_le`: the bound
  `‖fderiv 𝕜 (fun y ↦ c y v) x‖ ≤ ‖fderiv 𝕜 c x‖ * ‖v‖`.
-/

public section

namespace SymplecticGeometry

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- If a field `c` of continuous linear maps is differentiable at `x`, then for each fixed vector
`v` the derivative at `x` of `y ↦ c y v` has norm at most `‖fderiv 𝕜 c x‖ * ‖v‖`. -/
theorem norm_fderiv_clm_apply_const_le {c : E → F →L[𝕜] G} {x : E}
    (hc : DifferentiableAt 𝕜 c x) (v : F) :
    ‖fderiv 𝕜 (fun y ↦ c y v) x‖ ≤ ‖fderiv 𝕜 c x‖ * ‖v‖ := by
  rw [fderiv_clm_apply hc (differentiableAt_const v), fderiv_const_apply,
    ContinuousLinearMap.comp_zero, zero_add, ← ContinuousLinearMap.opNorm_flip (fderiv 𝕜 c x)]
  exact (fderiv 𝕜 c x).flip.le_opNorm v

end SymplecticGeometry

end
