/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Basic
public import TauCeti.Geometry.Lie.Exponential.Basic
import TauCeti.Geometry.Lie.Adjoint.Exponential.Formula

/-!
# Exponentials of tangent vectors that bracket to zero

For a finite-dimensional real Lie group `G`, Tau Ceti proves on left-invariant derivations that
two elements with vanishing bracket have commuting exponentials, and that the exponential of
their sum is the product of their exponentials (`TauCeti.Lie.commute_lieExp_of_lie_eq_zero`,
`TauCeti.Lie.lieExp_add_of_lie_eq_zero`). This file states both on the tangent Lie algebra
`GroupLieAlgebra I G` and its exponential `mulInvariantExp`, transporting them along
`leftInvariantDerivationLieEquivGroupLieAlgebra`. It also gives the converse of Tau Ceti's
`TauCeti.Lie.tangentAd_mulInvariantExp_smul_apply_eq_self_of_lie_eq_zero` in a local form: if the
one-parameter subgroup of `X` fixes `Y` under `Ad` for all small times, then `⁅X, Y⁆ = 0`. Its
proof is that of Tau Ceti's `TauCeti.Lie.Ad_lieExp_smul_apply_eq_self_iff`, on the tangent Lie
algebra and with the hypothesis only near time `0`.

## Main results

* `TauCeti.Lie.commute_mulInvariantExp_of_lie_eq_zero`: tangent vectors with vanishing bracket
  have commuting exponentials.
* `TauCeti.Lie.mulInvariantExp_add_of_lie_eq_zero`: for them, `exp (X + Y) = exp X * exp Y`.
* `TauCeti.Lie.lie_eq_zero_of_eventually_tangentAd_mulInvariantExp_smul_apply_eq_self`: if
  `Ad (exp (s • X)) Y = Y` for all `s` near `0`, then `⁅X, Y⁆ = 0`.
-/

public section

open Filter
open scoped Topology ContDiff

namespace TauCeti.Lie

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [T2Space G]
  [BoundarylessManifold I G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- The exponential of a tangent vector is that of the corresponding left-invariant
derivation. -/
private theorem mulInvariantExp_eq_lieExp_symm (X : GroupLieAlgebra I G) :
    mulInvariantExp X = lieExp ((leftInvariantDerivationLieEquivGroupLieAlgebra (I := I)
      (G := G) BoundarylessManifold.isInteriorPoint).symm X) := by
  rw [lieExp_eq_mulInvariantExp, ← leftInvariantDerivationLieEquivGroupLieAlgebra_apply,
    LieEquiv.apply_symm_apply]

/-- Tangent vectors with vanishing bracket have commuting exponentials. -/
theorem commute_mulInvariantExp_of_lie_eq_zero {X Y : GroupLieAlgebra I G} (h : ⁅X, Y⁆ = 0) :
    Commute (mulInvariantExp X) (mulInvariantExp Y) := by
  rw [mulInvariantExp_eq_lieExp_symm, mulInvariantExp_eq_lieExp_symm]
  exact commute_lieExp_of_lie_eq_zero (by rw [← LieEquiv.map_lie, h, map_zero])

/-- The exponential of the sum of two tangent vectors with vanishing bracket is the product of
their exponentials. -/
theorem mulInvariantExp_add_of_lie_eq_zero {X Y : GroupLieAlgebra I G} (h : ⁅X, Y⁆ = 0) :
    mulInvariantExp (X + Y) = mulInvariantExp X * mulInvariantExp Y := by
  rw [mulInvariantExp_eq_lieExp_symm, mulInvariantExp_eq_lieExp_symm,
    mulInvariantExp_eq_lieExp_symm, map_add]
  exact lieExp_add_of_lie_eq_zero (by rw [← LieEquiv.map_lie, h, map_zero])

/-- If the one-parameter subgroup of `X` fixes `Y` under the adjoint action for all times near
`0`, then `⁅X, Y⁆ = 0`. -/
theorem lie_eq_zero_of_eventually_tangentAd_mulInvariantExp_smul_apply_eq_self
    {X Y : GroupLieAlgebra I G}
    (h : ∀ᶠ s in 𝓝 (0 : ℝ), tangentAd (I := I) (mulInvariantExp (s • X)) Y = Y) :
    ⁅X, Y⁆ = 0 := by
  -- The curve `s ↦ Ad (exp (s • X)) Y` has derivative `⁅X, Y⁆` at `0`, and is constant near `0`.
  have hderiv := hasDerivAt_tangentAd_mulInvariantExp_smul_apply_zero (I := I) X Y
  exact (hderiv.congr_of_eventuallyEq (h.mono fun s hs ↦ hs.symm)).unique (hasDerivAt_const 0 _)

end TauCeti.Lie

end
