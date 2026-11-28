/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Lie.Exponential.Basic
import TauCeti.Geometry.Lie.Adjoint.Exponential.Basic
import TauCeti.Geometry.Lie.Adjoint.Exponential.Formula

/-!
# Exponentials of commuting elements of the Lie algebra

If `⁅X, Y⁆ = 0` in the Lie algebra `GroupLieAlgebra I G` of a finite-dimensional real Lie group,
then `exp X` and `exp Y` commute (`commute_mulInvariantExp_of_lie_eq_zero`).

This is Tau Ceti's `TauCeti.Lie.commute_lieExp_of_lie_eq_zero`, stated for left-invariant
derivations, read on the tangent space at the identity, and proved the same way: conjugation by
`exp X` sends `exp Y` to `exp (Ad (exp X) Y)` (`TauCeti.Lie.conj_mulInvariantExp`), and
`Ad (exp X)` fixes `Y` (`TauCeti.Lie.tangentAd_mulInvariantExp_smul_apply_eq_self_of_lie_eq_zero`).
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
  have hAd := TauCeti.Lie.tangentAd_mulInvariantExp_smul_apply_eq_self_of_lie_eq_zero h 1
  have hconj := TauCeti.Lie.conj_mulInvariantExp (I := I) (mulInvariantExp X) Y
  simp only [one_smul] at hAd
  rw [hAd] at hconj
  exact mul_inv_eq_iff_eq_mul.mp hconj
