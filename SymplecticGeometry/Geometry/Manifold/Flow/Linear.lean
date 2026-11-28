/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.ODE.Linear
public import TauCeti.Geometry.Manifold.Flow.Basic
public import TauCeti.Geometry.Manifold.Flow.Complete
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Linear vector fields are complete

A bounded linear operator `A` on a real Banach space `X` is a vector field `x ↦ A x` on `X`, in the
model `𝓘(ℝ, X)`. Its orbits are the curves `t ↦ exp (t • A) x` of Tau Ceti's linear flow
`ContinuousLinearMap.flow`, so the field is complete and its maximal flow `TauCeti.flowOf` is that
linear flow.

The proofs follow Tau Ceti's `TauCeti.isCompleteVectorField_dilation` and
`TauCeti.flowOf_dilation` (`TauCeti/Geometry/Manifold/Flow/NormedSpace.lean`), which treat the
field `x ↦ c • x`, with the derivative `hasDerivAt_exp_smul_const'` of the operator exponential
in place of that of the real one.

## Main results

* `ContinuousLinearMap.contMDiff_tangent`: the field `x ↦ A x` is a smooth section.
* `ContinuousLinearMap.isMIntegralCurve_flow`: `t ↦ A.flow t x` is an integral curve of `A`.
* `ContinuousLinearMap.isCompleteVectorField`: the field `x ↦ A x` is complete.
* `ContinuousLinearMap.flowOf_eq_flow`: its maximal flow is `A.flow`.
* `ContinuousLinearMap.flow_eq_of_isMIntegralCurve`: so `A.flow` agrees with every integral
  curve of `A`, which computes it from an explicit solution.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 9 (integral curves and flows).
-/

public section

open NormedSpace TauCeti
open scoped Manifold

namespace ContinuousLinearMap

/-- The vector field `x ↦ A x` of a bounded linear operator is smooth, as a section of the tangent
bundle. -/
theorem contMDiff_tangent {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (A : X →L[ℝ] X)
    (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℝ, X) 𝓘(ℝ, X).tangent n (fun y : X ↦ (⟨y, A y⟩ : TangentBundle 𝓘(ℝ, X) X)) :=
  contMDiff_vectorSpace_iff_contDiff.mpr A.contDiff

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- The orbit `t ↦ exp (t • A) x` of the linear flow of `A` is an integral curve of the vector
field `x ↦ A x`. -/
theorem isMIntegralCurve_flow (A : X →L[ℝ] X) (x : X) :
    IsMIntegralCurve (I := 𝓘(ℝ, X)) (fun t ↦ A.flow t x) (fun y ↦ A y) := by
  intro t
  have h : HasDerivAt (fun s : ℝ ↦ A.flow s x) (A (A.flow t x)) t := by
    simp only [flow_apply]
    simpa using (hasDerivAt_exp_smul_const' A t).clm_apply (hasDerivAt_const t x)
  exact h.hasFDerivAt.hasMFDerivAt

/-- The vector field `x ↦ A x` of a bounded linear operator on a real Banach space is complete. -/
theorem isCompleteVectorField (A : X →L[ℝ] X) :
    IsCompleteVectorField (I := 𝓘(ℝ, X)) (fun y : X ↦ A y) :=
  isCompleteVectorField_of_forall_exists_isMIntegralCurve fun x ↦
    ⟨_, by simp, A.isMIntegralCurve_flow x⟩

/-- The maximal flow of the vector field `x ↦ A x` is the linear flow `exp (t • A)` of `A`. -/
@[simp]
theorem flowOf_eq_flow (A : X →L[ℝ] X) (t : ℝ) (x : X) :
    flowOf (I := 𝓘(ℝ, X)) (fun y : X ↦ A y) t x = A.flow t x := by
  simpa using flowOf_eq_of_isMIntegralCurve (A.contMDiff_tangent 1) (A.isMIntegralCurve_flow x) t

/-- The linear flow of `A` takes the value of any integral curve `γ` of `x ↦ A x` at time `0` to
its value at time `t`. -/
theorem flow_eq_of_isMIntegralCurve (A : X →L[ℝ] X) {γ : ℝ → X}
    (hγ : IsMIntegralCurve (I := 𝓘(ℝ, X)) γ (fun y ↦ A y)) (t : ℝ) :
    A.flow t (γ 0) = γ t := by
  rw [← A.flowOf_eq_flow]
  exact flowOf_eq_of_isMIntegralCurve (A.contMDiff_tangent 1) hγ t

end ContinuousLinearMap

end
