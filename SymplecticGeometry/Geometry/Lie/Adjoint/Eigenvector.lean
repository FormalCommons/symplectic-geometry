/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Exponential.Formula

/-!
# The adjoint action of an exponential on an eigenvector of `ad`

On a finite-dimensional real Lie group, if `Y` is an eigenvector of `ad X` with eigenvalue `μ`,
then `Ad (exp X)` multiplies `Y` by `Real.exp μ`. This reads Tau Ceti's
`TauCeti.Lie.tangentAd_mulInvariantExp_apply`, which writes `Ad (exp X)` as the operator
exponential of `ad X`, on an eigenvector with Tau Ceti's
`ContinuousLinearMap.exp_apply_of_apply_eq_smul`.

## Main results

* `TauCeti.Lie.tangentAd_mulInvariantExp_of_lie_eq_smul`: if `⁅X, Y⁆ = μ • Y`, then
  `Ad (exp X) Y = Real.exp μ • Y`.
-/

public section

open Manifold
open scoped Manifold ContDiff

namespace TauCeti.Lie

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [T2Space G] [BoundarylessManifold I G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- If `Y` is an eigenvector of `ad X` with eigenvalue `μ`, then `Ad (exp X)` multiplies `Y` by
`Real.exp μ`. -/
theorem tangentAd_mulInvariantExp_of_lie_eq_smul {X Y : GroupLieAlgebra I G} {μ : ℝ}
    (h : ⁅X, Y⁆ = μ • Y) :
    tangentAd (I := I) (mulInvariantExp (I := I) (G := G) X) Y = Real.exp μ • Y := by
  have h' := tangentAd_mulInvariantExp_apply (I := I) (G := G) X Y
  dsimp only at h'
  rw [Real.exp_eq_exp_ℝ]
  -- `h'` and `exp_apply_of_apply_eq_smul` are read in the model space `E`, which
  -- `GroupLieAlgebra I G` is by definition; there the operator `ad X` sends `Y` to `⁅X, Y⁆`.
  exact h'.trans (ContinuousLinearMap.exp_apply_of_apply_eq_smul _ h)

end TauCeti.Lie

end
