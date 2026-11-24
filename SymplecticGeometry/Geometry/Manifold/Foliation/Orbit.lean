/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Lie.Exponential.Generation
public import TauCeti.Geometry.Lie.FundamentalVectorField
public import TauCeti.Geometry.Manifold.Foliation.Leaf
import TauCeti.GroupTheory.GroupAction.Closure

/-!
# Orbits of a group action inside the leaves of a foliation

Let a Lie group `G` act smoothly on a manifold `Z` with a `C¹` foliation `F`, and suppose that
every fundamental vector field of the action is tangent to `F`. This file shows that the orbits
of `G` then lie in the leaves of `F`, when `G` is connected.

* `TauCeti.Foliation.mulInvariantExp_smul_mem_leaf`: for `ξ` in the Lie algebra of `G` and `z`
  in `Z`, the point `exp ξ • z` lies on the leaf through `z`. The curve `t ↦ exp (t ξ) • z` is an
  integral curve of the fundamental vector field of `ξ`
  (Tau Ceti's `TauCeti.isMIntegralCurve_mulInvariantExp_smul_smul`), so it is tangent to `F`, and
  `TauCeti.Foliation.sameLeaf_of_contMDiffOn_of_tangent` applies.
* `TauCeti.Foliation.orbit_subset_leaf`: for connected `G`, each orbit lies in a leaf. The
  exponential image generates `G` (Tau Ceti's `TauCeti.closure_range_lieExp_eq_top`), and a
  function invariant under generators is invariant under the group they generate
  (Tau Ceti's `TauCeti.apply_eq_of_mem_closure`), applied to `F.leaf`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

namespace Foliation

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'}
  {Z : Type*} [TopologicalSpace Z] [ChartedSpace H' Z] [IsManifold J (1 + 1) Z]
  [MulAction G Z] [ContMDiffSMul I J ∞ G Z] {k : ℕ} (F : Foliation J 1 Z k)

/-- **Exponential translates stay on a leaf.** If every fundamental vector field of the action of
`G` on `Z` is tangent to the foliation `F`, then for every `ξ` in the Lie algebra of `G` and every
`z : Z`, the point `exp ξ • z` lies on the leaf of `F` through `z`. -/
theorem mulInvariantExp_smul_mem_leaf [T2Space G] [BoundarylessManifold I G]
    (hF : ∀ (ξ : GroupLieAlgebra I G) (z : Z), fundamentalVectorField J ξ z ∈ F.distribution z)
    (ξ : GroupLieAlgebra I G) (z : Z) : mulInvariantExp ξ • z ∈ F.leaf z := by
  have hγ : IsMIntegralCurve (fun t : ℝ ↦ mulInvariantExp (t • ξ) • z)
      (fundamentalVectorField J ξ) :=
    isMIntegralCurve_mulInvariantExp_smul_smul ξ z
  have key := F.sameLeaf_of_contMDiffOn_of_tangent (γ := fun t : ℝ ↦ mulInvariantExp (t • ξ) • z)
    (a := 0) (b := 1)
    (((ContMDiffSMul.contMDiff_smul_const (I := I) (n := ∞) z).comp
      (contMDiff_mulInvariantExp_smul ξ)).contMDiffOn.of_le ENat.LEInfty.out)
    (fun u hu ↦ by
      rw [Manifold.curveVelocityWithin_eq_of_hasMFDerivWithinAt (hγ u).hasMFDerivWithinAt
        (uniqueDiffOn_Icc zero_lt_one u hu)]
      exact hF ξ _)
    (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one)
  simpa using key

/-- **Orbits lie in leaves.** If `G` is connected and every fundamental vector field of its action
on `Z` is tangent to the foliation `F`, then the orbit of each `z : Z` is contained in the leaf of
`F` through `z`. -/
theorem orbit_subset_leaf [FiniteDimensional ℝ E] [ConnectedSpace G]
    (hF : ∀ (ξ : GroupLieAlgebra I G) (z : Z), fundamentalVectorField J ξ z ∈ F.distribution z)
    (z : Z) : MulAction.orbit G z ⊆ F.leaf z := by
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have : BoundarylessManifold I G := ContMDiffMul.boundarylessManifold
  rintro _ ⟨g, rfl⟩
  have hg : g ∈ Subgroup.closure (Set.range (lieExp (I := I) (G := G))) := by
    rw [closure_range_lieExp_eq_top]
    exact Subgroup.mem_top g
  have hS : ∀ g ∈ Set.range (lieExp (I := I) (G := G)), ∀ y : Z, F.leaf (g • y) = F.leaf y := by
    rintro _ ⟨X, rfl⟩ y
    rw [lieExp_eq_mulInvariantExp]
    exact F.leaf_eq_of_mem (F.mulInvariantExp_smul_mem_leaf hF _ y)
  have := apply_eq_of_mem_closure hS hg z
  rw [← this]
  exact F.mem_leaf_self _

end Foliation

end TauCeti

end
