/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Lie.Exponential.Derivative.Basic
public import TauCeti.Geometry.Manifold.MFDeriv.Curve

/-!
# Derivatives of the exponential

For `g` in a Lie group `G` and `X` in its Lie algebra, the curve `s ↦ g * exp (s • X)` has at
every time `t` the velocity `X_{g exp (t X)}` of the left-invariant vector field of `X`, so that
its left-trivialized velocity is the constant `X`. At `0`, the exponential itself has derivative
the identity.

## Main results

* `curveVelocity_mul_mulInvariantExp_smul`: the velocity of `s ↦ g * exp (s • X)` at `t` is the
  value of the left-invariant vector field of `X` at `g * exp (t • X)`.
* `mfderiv_inv_mul_mfderiv_mul_mulInvariantExp_smul`: translated back to the identity by
  `(g * exp (t • X))⁻¹`, that velocity is `X`.
* `hasMFDerivAt_mulInvariantExp_modelSpace_zero`: read on the model space, the exponential has
  derivative the identity at `0`.

The first is Tau Ceti's `hasMFDerivAt_mulInvariantExp_smul` (the case `g = 1`) pushed forward by
left translation by `g`, which preserves left-invariant fields
(`mfderiv_mul_left_mulInvariantVectorField`); the second then applies Tau Ceti's
`TauCeti.mfderiv_inv_mul_mulInvariantVectorField`.

The third is Tau Ceti's `hasFDerivAt_extChartAt_mulInvariantExp_zero`, the same statement in the
identity chart of `G`, read as a manifold derivative.
-/

public section

noncomputable section

open Manifold TauCeti.Manifold
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [T2Space G]
  [BoundarylessManifold I G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- The velocity at `t` of the left-translated exponential line `s ↦ g * exp (s • X)` is the value
at `g * exp (t • X)` of the left-invariant vector field of `X`. -/
theorem curveVelocity_mul_mulInvariantExp_smul (g : G) (X : GroupLieAlgebra I G) (t : ℝ) :
    curveVelocity I (fun s : ℝ ↦ g * mulInvariantExp (s • X)) t =
      mulInvariantVectorField X (g * mulInvariantExp (t • X)) := by
  have he := hasMFDerivAt_mulInvariantExp_smul (I := I) X t
  rw [← curveVelocityWithin_univ, ← Function.comp_def (g * ·),
    curveVelocityWithin_map (mdifferentiableAt_mul_left (a := g)) uniqueDiffWithinAt_univ
      he.mdifferentiableAt.mdifferentiableWithinAt,
    curveVelocityWithin_eq_of_hasMFDerivWithinAt he.hasMFDerivWithinAt uniqueDiffWithinAt_univ,
    mfderiv_mul_left_mulInvariantVectorField]

/-- The left-trivialized velocity of the left-translated exponential line `s ↦ g * exp (s • X)`
is `X` at every time `t`. -/
theorem mfderiv_inv_mul_mfderiv_mul_mulInvariantExp_smul (g : G) (X : GroupLieAlgebra I G)
    (t : ℝ) :
    mfderiv I I ((g * mulInvariantExp (t • X))⁻¹ * ·) (g * mulInvariantExp (t • X))
      (mfderiv 𝓘(ℝ) I (fun s : ℝ ↦ g * mulInvariantExp (s • X)) t (1 : ℝ)) = X := by
  rw [← curveVelocity_apply, curveVelocity_mul_mulInvariantExp_smul,
    TauCeti.mfderiv_inv_mul_mulInvariantVectorField]

/-- **The derivative of the exponential at `0`.** Read on the model space `E` of `G`, the
exponential `v ↦ exp v` has derivative the identity at `0`. -/
theorem hasMFDerivAt_mulInvariantExp_modelSpace_zero [FiniteDimensional ℝ E] :
    HasMFDerivAt 𝓘(ℝ, E) I
      (fun v : E ↦ mulInvariantExp (I := I) (G := G) (v : GroupLieAlgebra I G)) 0
      (ContinuousLinearMap.id ℝ E) := by
  have h0 : mulInvariantExp (I := I) (G := G) ((0 : E) : GroupLieAlgebra I G) = 1 :=
    mulInvariantExp_zero
  refine ⟨(contMDiff_mulInvariantExp (I := I) (G := G)).continuous.continuousAt, ?_⟩
  rw [writtenInExtChartAt, extChartAt_self_eq, h0]
  simp only [hasFDerivWithinAt_univ, ModelWithCorners.range_eq_univ]
  -- The casts between the tangent spaces and the model spaces are identities.
  exact hasFDerivAt_extChartAt_mulInvariantExp_zero (I := I) (G := G)

end
