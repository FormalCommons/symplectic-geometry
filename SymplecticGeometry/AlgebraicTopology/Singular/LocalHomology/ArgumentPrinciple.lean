/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.DiscComplement.BoundaryClass
public import TauCeti.Topology.Circle.Normalize

/-!
# The argument principle for coordinate discs

Let `φ i`, `i : ι` finite, be coordinate discs (`SymplecticGeometry.CoordinateDisc`) of a compact
surface `M` homologically oriented by `o`, with pairwise disjoint closed discs, and let `u` be a
continuous function with values in `ℂ` that has no zero on the complement `discComplement φ` of
the open discs. Then the winding numbers of `u` around the boundary circles of the discs add up
to `0`: the degrees of the loops `t ↦ u(cᵢ(t)) / |u(cᵢ(t))|`, for `cᵢ` the counterclockwise
boundary loop `(φ i).boundaryLoop` of the `i`-th disc, have sum `0`
(`SymplecticGeometry.sum_degree_boundary_eq_zero`).

## Proof

The complement `X` of the open discs is a compact surface with collared boundary
(`SymplecticGeometry.isCollared_discComplementBoundary`), and `u / |u|` is a map `X → S¹`, so the
boundary degree of its restriction to `∂X` vanishes
(`TauCeti.HomologicalOrientation.boundaryDegree_eq_zero_of_extend`). The boundary class of `X`
is the sum of the classes of the reversed boundary loops of the discs
(`SymplecticGeometry.sum_map_toCircle_discComplementBoundaryLoop_eq_boundaryClass`), so that
boundary degree is the sum of the degrees of `u / |u|` along the reversed loops
(`TauCeti.HomologicalOrientation.boundaryDegree_eq_sum_degree`), which is minus the sum along the
boundary loops themselves (`Circle.degree_symm`).

## Main results

* `SymplecticGeometry.sum_degree_boundary_eq_zero`: the argument principle for coordinate discs.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.7,
  Lemma 2.7.3, of which this is the half needed for discs.
-/

public section

noncomputable section

open Set Topology Module TauCeti Function

namespace SymplecticGeometry

variable {M : Type} [TopologicalSpace M] [T2Space M] {E : Type} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M] {o : HomologicalOrientation M E 2}
  {ι : Type} [Fintype ι]

/-- **The argument principle for coordinate discs.** Let `φ i`, `i : ι` finite, be coordinate
discs of a compact surface `M` homologically oriented by `o`, with pairwise disjoint closed discs,
and let `u : M → ℂ` be continuous and nowhere zero on the complement of the open discs. Let
`γ i` be the loop of directions `t ↦ u(c(t)) / |u(c(t))|` of `u` along the counterclockwise
boundary loop `c = (φ i).boundaryLoop` of the `i`-th disc. Then the degrees of the loops `γ i`
add up to `0`. -/
theorem sum_degree_boundary_eq_zero [CompactSpace M] (hn : finrank ℝ E = 2)
    (φ : ι → CoordinateDisc o) (hφ : Pairwise (Disjoint on fun i ↦ (φ i).disc)) {u : M → ℂ}
    (hu : ContinuousOn u (discComplement φ)) (hu₀ : ∀ x ∈ discComplement φ, u x ≠ 0)
    {x : ι → Circle} (γ : ∀ i, Path (x i) (x i))
    (hγ : ∀ i t, (γ i t : ℂ) = u ((φ i).boundaryLoop t) / ‖u ((φ i).boundaryLoop t)‖) :
    ∑ i, Circle.degree (γ i) = 0 := by
  let _ : TopologicalSpace ι := ⊥
  have : DiscreteTopology ι := ⟨rfl⟩
  -- `u / |u|` as a map from the complement of the open discs to the circle
  let v : C(discComplement φ, Circle) :=
    (⟨(discComplement φ).domRestrict u, hu.domRestrict⟩ : C(discComplement φ, ℂ)).normalizeToCircle
      fun y ↦ hu₀ y y.property
  have hv (y : discComplement φ) : (v y : ℂ) = u y / ‖u y‖ :=
    ContinuousMap.coe_normalizeToCircle_apply _ _ y
  let w : C(↥(range (inclusion (discComplementInterior_subset φ)))ᶜ, Circle) :=
    v.restrict _
  have h₀ := (o.comap (discComplementInterior φ).isOpenEmbedding').boundaryDegree_eq_zero_of_extend
    hn (isOpenEmbedding_inclusion_discComplementInterior φ)
    (range_inclusion_discComplementInterior φ hφ) (isCollared_discComplementBoundary φ hφ)
    (u := w) v fun z ↦ (v.restrict_apply _ z).symm
  rw [HomologicalOrientation.boundaryDegree_eq_sum_degree _ _ _ _ _
    (discComplementBoundaryLoop φ hφ)
    (sum_map_toCircle_discComplementBoundaryLoop_eq_boundaryClass φ hφ hn)] at h₀
  -- along the reversed boundary loop of a disc, `u / |u|` traces the reverse of `γ i`
  have hdeg (i : ι) : Circle.degree ((discComplementBoundaryLoop φ hφ i).map w.continuous) =
      -Circle.degree (γ i) := by
    rw [← Circle.degree_symm]
    refine Circle.degree_congr _ _ fun t ↦ Circle.ext ?_
    have h := hv (discComplementBoundaryLoop φ hφ i t)
    rw [coe_coe_discComplementBoundaryLoop_apply, Path.symm_apply, Function.comp_apply] at h
    rw [Path.map_coe, Function.comp_apply, Path.symm_apply, Function.comp_apply, hγ,
      ContinuousMap.restrict_apply]
    exact h
  rw [Finset.sum_congr rfl fun i _ ↦ hdeg i, Finset.sum_neg_distrib, neg_eq_zero] at h₀
  exact h₀

end SymplecticGeometry
