/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Lie.Exponential.Basic
import TauCeti.Geometry.Lie.Adjoint.Exponential.Formula

/-!
# Exponentials of commuting elements of the Lie algebra

If `⁅X, Y⁆ = 0` in the Lie algebra `GroupLieAlgebra I G` of a finite-dimensional real Lie group,
then `exp X` and `exp Y` commute (`commute_mulInvariantExp_of_lie_eq_zero`).

This is Tau Ceti's `TauCeti.Lie.commute_lieExp_of_lie_eq_zero`, stated for left-invariant
derivations, carried to the tangent space at the identity along the Lie algebra isomorphism
`leftInvariantDerivationLieEquivGroupLieAlgebra`.
-/

public section

open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [T2Space G]
  [BoundarylessManifold I G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- **Elements of the Lie algebra that bracket to zero have commuting exponentials.** -/
theorem commute_mulInvariantExp_of_lie_eq_zero {X Y : GroupLieAlgebra I G} (h : ⁅X, Y⁆ = 0) :
    Commute (mulInvariantExp X) (mulInvariantExp Y) := by
  let e := leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
    (BoundarylessManifold.isInteriorPoint (x := (1 : G)))
  have := TauCeti.Lie.commute_lieExp_of_lie_eq_zero (I := I) (X := e.symm X) (Y := e.symm Y)
    (by rw [← LieEquiv.map_lie, h, map_zero])
  simpa only [lieExp_eq_mulInvariantExp, ← leftInvariantDerivationLieEquivGroupLieAlgebra_apply,
    e, LieEquiv.apply_symm_apply] using this
