/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Data.Fin.Tuple.Reflection
public import Mathlib.Topology.Algebra.Module.Equiv.Pi

/-!
# Derivatives of functions on `Fin 1 → 𝕜`

The continuous linear equivalence `ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜` identifies
`Fin 1 → 𝕜` with `𝕜`; its inverse is `t ↦ ![t]`. So a function on `Fin 1 → 𝕜` can be
differentiated as the function of one variable `t ↦ f ![t]`.

## Main results

* `hasDerivAt_vecCons_fin_one`: the derivative of `t ↦ ![t]` is `![1]`.
* `differentiableAt_iff_differentiableAt_vecCons_fin_one`: `f` is differentiable at `x` exactly
  when `t ↦ f ![t]` is differentiable at `x 0`.
-/

public section

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The derivative of `t ↦ ![t]` is `![1]`. -/
theorem hasDerivAt_vecCons_fin_one (t : 𝕜) : HasDerivAt (fun t : 𝕜 ↦ ![t]) ![1] t := by
  simp only [Matrix.vec_single_eq_const]
  exact (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜).symm.hasFDerivAt.hasDerivAt

/-- A function `f` on `Fin 1 → 𝕜` is differentiable at `x` exactly when `t ↦ f ![t]` is
differentiable at `x 0`. -/
theorem differentiableAt_iff_differentiableAt_vecCons_fin_one {f : (Fin 1 → 𝕜) → F}
    {x : Fin 1 → 𝕜} :
    DifferentiableAt 𝕜 f x ↔ DifferentiableAt 𝕜 (fun t ↦ f ![t]) (x 0) := by
  conv_lhs => rw [← show ![x 0] = x from FinVec.etaExpand_eq x]
  simp only [Matrix.vec_single_eq_const]
  exact ((ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜).symm.comp_right_differentiableAt_iff).symm

end
