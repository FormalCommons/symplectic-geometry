/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Lie.Tangent.LieEquiv
import SymplecticGeometry.Geometry.Lie.GroupLieAlgebra.Model
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# The adjoint map under the identification of left-invariant derivations with `E`

For a finite-dimensional real Lie group `G` without boundary, Tau Ceti identifies the Lie algebra
`LeftInvariantDerivation I G` isometrically with the model space `E`
(`leftInvariantDerivationLinearIsometryEquivModelVectorSpace`), by evaluation at the identity,
and this identification preserves brackets (`leftInvariantDerivationLieEquivGroupLieAlgebra`).
So conjugating the adjoint map `ad D` of a derivation by it gives the adjoint map of its value
at the identity in `GroupLieAlgebra I G`, read as an operator on `E`. This transports
statements about `ad` on derivations, such as Tau Ceti's derivative of `lieExp`, to
`GroupLieAlgebra I G`.

## Main results

* `conjContinuousAlgEquiv_leftInvariantDerivationLinearIsometryEquivModelVectorSpace_ad`: the
  conjugate of `ad D` is `ad` of the value of `D` at the identity.

The proof is the step `had` of Tau Ceti's proof of `LeftInvariantDerivation.Ad_lieExp`
(`TauCeti/Geometry/Lie/Adjoint/Exponential/Formula.lean`), stated on its own.
-/

public section

open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [T2Space G]
  [BoundarylessManifold I G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- Conjugating the adjoint map `ad D` of a left-invariant derivation by the identification of
`LeftInvariantDerivation I G` with the model space `E` gives the adjoint map of the value of `D`
at the identity, as an operator on `E`. -/
theorem conjContinuousAlgEquiv_leftInvariantDerivationLinearIsometryEquivModelVectorSpace_ad
    (D : LeftInvariantDerivation I G) :
    (leftInvariantDerivationLinearIsometryEquivModelVectorSpace (I := I)
      (G := G)).toContinuousLinearEquiv.conjContinuousAlgEquiv
      (LinearMap.toContinuousLinearMap (LieAlgebra.ad ℝ (LeftInvariantDerivation I G) D)) =
      Module.End.toContinuousLinearMap E
        ((groupLieAlgebraEquivModelVectorSpace (I := I) (G := G)).conj
          (LieAlgebra.ad ℝ (GroupLieAlgebra I G)
            (leftInvariantDerivationEquivGroupLieAlgebra BoundarylessManifold.isInteriorPoint
              D))) := by
  let e := leftInvariantDerivationLinearIsometryEquivModelVectorSpace (I := I) (G := G)
  let ε := leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
    BoundarylessManifold.isInteriorPoint
  have he (Z : LeftInvariantDerivation I G) : (e Z : E) = ε Z :=
    leftInvariantDerivationLinearIsometryEquivModelVectorSpace_apply_eq_lieEquiv_apply Z
  ext w
  rw [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply]
  simp only [LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv, LinearMap.coe_toContinuousLinearMap',
    LieAlgebra.ad_apply]
  rw [he, LieEquiv.map_lie, ← he (e.symm w), e.apply_symm_apply,
    leftInvariantDerivationLieEquivGroupLieAlgebra_apply, Module.End.toContinuousLinearMap_apply,
    LinearEquiv.conj_apply_apply, groupLieAlgebraEquivModelVectorSpace_apply,
    LieAlgebra.ad_apply, groupLieAlgebraEquivModelVectorSpace_symm_apply]

end
