/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Lie.Exponential.Basic
import TauCeti.Geometry.Lie.Exponential.ProductChart

/-!
# Products of exponentials of two spanning subspaces

For subspaces `V` and `W` of the Lie algebra of a finite-dimensional Lie group `G` with
`V ⊔ W = ⊤`, the products `exp x * exp y` with `x ∈ V` and `y ∈ W` form a neighbourhood of `1`.

## Main results

* `mulInvariantExp_image_mul_mulInvariantExp_image_mem_nhds_one`: if `V ⊔ W = ⊤`, then
  `mulInvariantExp '' V * mulInvariantExp '' W ∈ 𝓝 1`.

Inside `W` there is a complement `W'` of `V` (`Codisjoint.exists_isCompl`). Carried to
left-invariant derivations by `leftInvariantDerivationEquivGroupLieAlgebra`, the map
`(x, y) ↦ exp x * exp y` on `V × W'` is Tau Ceti's `Submodule.lieExpMulLieExp`, a local
diffeomorphism at `0` by `Submodule.isLocalDiffeomorphAt_lieExpMulLieExp_zero_of_isCompl`; so
the image of its domain is a neighbourhood of `1`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd edition (2013), Theorem 20.12, for the
  local product chart.
-/

public section

open Manifold Topology
open scoped Pointwise ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [T2Space G]
  [BoundarylessManifold I G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- If two subspaces `V` and `W` of the Lie algebra of a finite-dimensional Lie group span it,
the products `exp x * exp y` with `x ∈ V` and `y ∈ W` form a neighbourhood of `1`. -/
theorem mulInvariantExp_image_mul_mulInvariantExp_image_mem_nhds_one [FiniteDimensional ℝ E]
    (V W : Submodule ℝ (GroupLieAlgebra I G)) (h : V ⊔ W = ⊤) :
    mulInvariantExp '' (V : Set (GroupLieAlgebra I G)) *
      mulInvariantExp '' (W : Set (GroupLieAlgebra I G)) ∈ 𝓝 (1 : G) := by
  obtain ⟨W', hW', hc⟩ := (codisjoint_iff.2 (sup_comm V W ▸ h)).exists_isCompl
  let e := leftInvariantDerivationEquivGroupLieAlgebra (I := I) (G := G)
    BoundarylessManifold.isInteriorPoint
  have hpq : IsCompl (V.map e.symm.toLinearMap) (W'.map e.symm.toLinearMap) :=
    (Submodule.orderIsoMapComap e.symm).isCompl hc.symm
  have hd := Submodule.isLocalDiffeomorphAt_lieExpMulLieExp_zero_of_isCompl _ _ hpq
  dsimp only at hd
  have h0 := hd.localInverse_mem_source
  rw [Submodule.lieExpMulLieExp_zero] at h0
  refine Filter.mem_of_superset (hd.localInverse_open_source.mem_nhds h0) fun y hy ↦ ?_
  rw [← hd.localInverse_right_inv hy, Submodule.lieExpMulLieExp_apply,
    lieExp_eq_mulInvariantExp, lieExp_eq_mulInvariantExp]
  set z := hd.localInverse y
  refine Set.mul_mem_mul ⟨_, ?_, rfl⟩ ⟨_, hW' ?_, rfl⟩
  · simpa only [SetLike.mem_coe, Submodule.mem_map_equiv, LinearEquiv.symm_symm] using z.1.property
  · simpa only [SetLike.mem_coe, Submodule.mem_map_equiv, LinearEquiv.symm_symm] using z.2.property
