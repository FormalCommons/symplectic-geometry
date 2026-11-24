/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Lie.Exponential.CommutativeGroup.Character

/-!
# Trivial circle characters and their weights

Tau Ceti's `ContinuousMonoidHom.lieWeight` is the real weight of a circle character `χ` on a Lie
group `G`, a functional on left-invariant derivations. Here the weight is read on the tangent
space `𝔤 = T₁G`, through the exponential `mulInvariantExp`: on a connected Lie group, if a
functional `α` on `𝔤` satisfies `χ (exp ξ) = Circle.exp (α ξ)` for every `ξ`, then `χ` is the
trivial character exactly when `α = 0`.

## Main results

* `ContinuousMonoidHom.eq_one_iff_of_forall_mulInvariantExp`: `χ = 1 ↔ α = 0` for a functional
  `α` on `T₁G` with `χ (exp ξ) = Circle.exp (α ξ)`.

The proof combines Tau Ceti's `ContinuousMonoidHom.eq_lieWeight`,
`ContinuousMonoidHom.lieWeight_injective` and `ContinuousMonoidHom.lieWeight_one`.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter I, § 3.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace ContinuousMonoidHom

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- **A circle character on a connected Lie group is trivial exactly when its weight vanishes.**
If a real-linear functional `α` on the tangent space `T₁G` satisfies
`χ (exp ξ) = Circle.exp (α ξ)` for every `ξ`, then `χ = 1` if and only if `α = 0`. -/
theorem eq_one_iff_of_forall_mulInvariantExp [PreconnectedSpace G] {χ : G →ₜ* Circle}
    {α : Module.Dual ℝ (GroupLieAlgebra I G)}
    (h : ∀ ξ, χ (mulInvariantExp (I := I) ξ) = Circle.exp (α ξ)) : χ = 1 ↔ α = 0 := by
  let ε := leftInvariantDerivationEquivGroupLieAlgebra (I := I) (G := G)
    BoundarylessManifold.isInteriorPoint
  have hw : α ∘ₗ ε.toLinearMap = lieWeight χ := eq_lieWeight fun X ↦ by
    rw [lieExp_eq_mulInvariantExp, h, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [← (lieWeight_injective (I := I)).eq_iff, lieWeight_one, ← hw]
  exact ⟨fun h0 ↦ LinearMap.ext fun ξ ↦ by simpa using LinearMap.congr_fun h0 (ε.symm ξ),
    fun h0 ↦ by simp [h0]⟩

end ContinuousMonoidHom
