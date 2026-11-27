/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Lie.Exponential.Derivative.Formula
import SymplecticGeometry.Geometry.Lie.Tangent.LieEquiv
public import TauCeti.Geometry.Manifold.MFDeriv.Curve

/-!
# Derivatives of the exponential

For `g` in a Lie group `G` and `X` in its Lie algebra, the curve `s ↦ g * exp (s • X)` has at
every time `t` the velocity `X_{g exp (t X)}` of the left-invariant vector field of `X`, so that
its left-trivialized velocity is the constant `X`. At `0`, the exponential itself has derivative
the identity. At a general point `X`, read on the model space `E`, its derivative is left
translation by `exp X` after the series `oneSubExpNegDivSelf ℝ (ad X)`, that is
`(1 - exp (-ad X)) / ad X`; so the left-trivialized derivative of `z ↦ exp (X z)` is that series
applied to the derivative of `X`.

## Main results

* `curveVelocity_mul_mulInvariantExp_smul`: the velocity of `s ↦ g * exp (s • X)` at `t` is the
  value of the left-invariant vector field of `X` at `g * exp (t • X)`.
* `mfderiv_inv_mul_mfderiv_mul_mulInvariantExp_smul`: translated back to the identity by
  `(g * exp (t • X))⁻¹`, that velocity is `X`.
* `hasMFDerivAt_mulInvariantExp_modelSpace_zero`: read on the model space, the exponential has
  derivative the identity at `0`.
* `hasMFDerivAt_mulInvariantExp_modelSpace`: read on the model space, the exponential has at `X`
  the derivative `dL_{exp X} ∘ oneSubExpNegDivSelf ℝ (ad X)`.
* `mfderiv_inv_mul_mfderiv_mulInvariantExp_comp`: for `X : M → E` differentiable at `z`, the
  derivative of `z ↦ exp (X z)` translated back by `(exp (X z))⁻¹` is
  `oneSubExpNegDivSelf ℝ (ad (X z)) ∘ dX_z`.

The first is Tau Ceti's `hasMFDerivAt_mulInvariantExp_smul` (the case `g = 1`) pushed forward by
left translation by `g`, which preserves left-invariant fields
(`mfderiv_mul_left_mulInvariantVectorField`); the second then applies Tau Ceti's
`TauCeti.mfderiv_inv_mul_mulInvariantVectorField`.

The third is Tau Ceti's `hasFDerivAt_extChartAt_mulInvariantExp_zero`, the same statement in the
identity chart of `G`, read as a manifold derivative.

The fourth is Tau Ceti's `LeftInvariantDerivation.hasMFDerivAt_lieExp`, the same formula on
`LeftInvariantDerivation I G`, carried to `E` by `lieExp_eq_mulInvariantExp` and the isometric
identification `leftInvariantDerivationLinearIsometryEquivModelVectorSpace`, which conjugates
`ad` on derivations to `ad` on `GroupLieAlgebra I G`
(`conjContinuousAlgEquiv_leftInvariantDerivationLinearIsometryEquivModelVectorSpace_ad`) and so,
by `map_oneSubExpNegDivSelf`, the two series. The fifth is the chain rule, with
`TauCeti.mfderiv_inv_mul_mulInvariantVectorField` for the translation back.

## References

* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed., Springer GTM 222 (2015),
  Theorem 5.4, for the formula for matrix groups.
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

section Formula

variable [FiniteDimensional ℝ E]

/-- **The derivative of the exponential.** Read on the model space `E` of `G`, the exponential
`v ↦ exp v` has at `X` the derivative `w ↦ dL_{exp X} (oneSubExpNegDivSelf ℝ (ad X) w)`: left
translation by `exp X` composed with the series `(1 - exp (-ad X)) / ad X`, where `ad X` is the
adjoint map of `GroupLieAlgebra I G` read as an operator on `E`. -/
theorem hasMFDerivAt_mulInvariantExp_modelSpace (X : E) :
    HasMFDerivAt 𝓘(ℝ, E) I
      (fun v : E ↦ mulInvariantExp (I := I) (G := G) (v : GroupLieAlgebra I G)) X
      ((mfderiv I I (mulInvariantExp (I := I) (G := G) (X : GroupLieAlgebra I G) * ·)
        (1 : G)).comp
        (oneSubExpNegDivSelf ℝ (Module.End.toContinuousLinearMap E
          ((groupLieAlgebraEquivModelVectorSpace (I := I) (G := G)).conj
            (LieAlgebra.ad ℝ (GroupLieAlgebra I G) X))) : E →L[ℝ] E)) := by
  let eI := leftInvariantDerivationLinearIsometryEquivModelVectorSpace (I := I) (G := G)
  let e₀ := leftInvariantDerivationEquivGroupLieAlgebra (I := I) (G := G)
    BoundarylessManifold.isInteriorPoint
  have he (v : E) : e₀ (eI.symm v) = v :=
    (leftInvariantDerivationLinearIsometryEquivModelVectorSpace_apply (I := I) (G := G)
      (eI.symm v)).symm.trans
      (eI.apply_symm_apply v)
  have hd := LeftInvariantDerivation.hasMFDerivAt_lieExp (I := I) (G := G) (eI.symm X)
  dsimp only at hd
  have hL : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, LeftInvariantDerivation I G) eI.symm X
      (eI.symm.toContinuousLinearEquiv : E →L[ℝ] LeftInvariantDerivation I G) :=
    eI.symm.toContinuousLinearEquiv.hasFDerivAt.hasMFDerivAt
  refine ((hd.comp X hL).congr_of_eventuallyEq (f₁ := fun v : E ↦
      mulInvariantExp (I := I) (G := G) (v : GroupLieAlgebra I G))
    (Filter.Eventually.of_forall fun v ↦ by
      rw [Function.comp_apply, lieExp_eq_mulInvariantExp, he])).congr_mfderiv ?_
  have hX : lieExp (I := I) (G := G) (eI.symm X) =
      mulInvariantExp (I := I) (G := G) (X : GroupLieAlgebra I G) := by
    rw [lieExp_eq_mulInvariantExp, he]
  -- The series on derivations, conjugated by `eI`, is the series on `E`.
  have hS (w : E) : (e₀ (oneSubExpNegDivSelf ℝ (LinearMap.toContinuousLinearMap
        (LieAlgebra.ad ℝ (LeftInvariantDerivation I G) (eI.symm X))) (eI.symm w)) : E) =
      oneSubExpNegDivSelf ℝ (Module.End.toContinuousLinearMap E
        ((groupLieAlgebraEquivModelVectorSpace (I := I) (G := G)).conj
          (LieAlgebra.ad ℝ (GroupLieAlgebra I G) X))) w := by
    have h := congr($(map_oneSubExpNegDivSelf (𝕂 := ℝ)
      eI.toContinuousLinearEquiv.conjContinuousAlgEquiv
      eI.toContinuousLinearEquiv.conjContinuousAlgEquiv.continuous
      (LinearMap.toContinuousLinearMap
        (LieAlgebra.ad ℝ (LeftInvariantDerivation I G) (eI.symm X)))) w)
    rwa [conjContinuousAlgEquiv_leftInvariantDerivationLinearIsometryEquivModelVectorSpace_ad,
      ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv,
      leftInvariantDerivationLinearIsometryEquivModelVectorSpace_apply,
      he] at h
  ext w
  -- The composite derivatives are typed in tangent spaces that are all definitionally `E`
  -- (`tangentSpaceCast` and `NormedSpace.fromTangentSpace` are identities); evaluate them in
  -- the model space before rewriting the base point.
  change mfderiv I I (lieExp (I := I) (G := G) (eI.symm X) * ·) (1 : G)
      (e₀ (oneSubExpNegDivSelf ℝ (LinearMap.toContinuousLinearMap
        (LieAlgebra.ad ℝ (LeftInvariantDerivation I G) (eI.symm X))) (eI.symm w))) =
    mfderiv I I (mulInvariantExp (I := I) (G := G) (X : GroupLieAlgebra I G) * ·) (1 : G)
      (oneSubExpNegDivSelf ℝ (Module.End.toContinuousLinearMap E
        ((groupLieAlgebraEquivModelVectorSpace (I := I) (G := G)).conj
          (LieAlgebra.ad ℝ (GroupLieAlgebra I G) X))) w)
  rw [hS w, hX]

variable {E' H' M : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M] [ChartedSpace H' M]

/-- **The left-trivialized derivative of `exp ∘ X`.** For a map `X : M → E` into the Lie algebra
differentiable at `z`, the derivative of `z ↦ exp (X z)` in direction `v`, translated back to the
identity by `(exp (X z))⁻¹`, is `oneSubExpNegDivSelf ℝ (ad (X z)) (dX_z v)`. -/
theorem mfderiv_inv_mul_mfderiv_mulInvariantExp_comp {X : M → E} {z : M}
    (hX : MDifferentiableAt I' 𝓘(ℝ, E) X z) (v : TangentSpace I' z) :
    mfderiv I I ((mulInvariantExp (I := I) (G := G) (X z : GroupLieAlgebra I G))⁻¹ * ·)
        (mulInvariantExp (X z : GroupLieAlgebra I G))
        (mfderiv I' I (fun z ↦ mulInvariantExp (I := I) (G := G) (X z : GroupLieAlgebra I G))
          z v) =
      oneSubExpNegDivSelf ℝ (Module.End.toContinuousLinearMap E
        ((groupLieAlgebraEquivModelVectorSpace (I := I) (G := G)).conj
          (LieAlgebra.ad ℝ (GroupLieAlgebra I G) (X z)))) (mfderiv I' 𝓘(ℝ, E) X z v) := by
  have hc := (hasMFDerivAt_mulInvariantExp_modelSpace (I := I) (G := G) (X z)).comp z
    hX.hasMFDerivAt
  rw [Function.comp_def] at hc
  rw [hc.mfderiv]
  -- The base points `X z : E` of the composite are read in `GroupLieAlgebra I G`, so the
  -- evaluation lemmas of `ContinuousLinearMap.comp` do not rewrite; the composite evaluates to
  -- left translation of the series, which `(exp (X z))⁻¹` translates back.
  exact (congrArg _ (GroupLieAlgebra.mulInvariantVectorField_apply _ _).symm).trans
    (TauCeti.mfderiv_inv_mul_mulInvariantVectorField _ _)

end Formula

end
