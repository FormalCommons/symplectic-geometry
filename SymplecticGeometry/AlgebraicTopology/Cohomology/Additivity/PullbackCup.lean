/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Additivity.Relative
public import TauCeti.AlgebraicTopology.Cohomology.Cup.Pullback
public import TauCeti.AlgebraicTopology.Singular.Additivity
import SymplecticGeometry.AlgebraicTopology.Cohomology.Additivity.Opens
import SymplecticGeometry.Topology.Homeomorph.Sigma

/-!
# Additivity of the map `a ↦ π^*a ⌣ u` over disjoint open sets

Let `π : X ⟶ Y` be a map, `Z ⊆ X` and `u ∈ Hⁿ(X, Z; K)`. Over a subset `S` of `Y`, Tau Ceti's
`TopCat.pullbackCupRestrict` is the map `Hᵖ(S; M) ⟶ Hᵐ(π⁻¹ S, π⁻¹ S ∩ Z; M)`, `a ↦ π^*a ⌣ u|`.
This file proves that if the `V i` are pairwise disjoint open subsets of `Y` and this map is
bijective over each `V i`, then it is bijective over `⋃ i, V i`
(`TopCat.bijective_pullbackCupRestrict_iUnion_of_pairwiseDisjoint`). This is the step for
countable disjoint unions in the Mayer–Vietoris induction `TauCeti.mayerVietoris_induction` that
proves the Thom isomorphism over a second-countable base, following the proof of Theorem 10.4 of
Milnor and Stasheff.

The union `⋃ i, V i` is the disjoint union of the `V i`, and the pair over it is the disjoint union
of the pairs over the `V i`, since their preimages are again disjoint and open
(`Set.isHomeomorph_sigma_inclusion`, `TopCat.isColimitCofanPreimagePairIUnion`). Singular
cohomology carries these disjoint unions to products (`TauCeti.isLimitFanSingularCohomologyIUnion`
and Tau Ceti's `TauCeti.TopPair.isLimitFanSingularCohomologyOfIsColimit`), and the map over the
union is compatible with the restrictions to the `V i` (`TopCat.pullbackCupRestrict_naturality`).
So it is the product of the maps over the `V i`, which are isomorphisms. Tau Ceti's
`TauCeti.HomologicalOrientation.bijective_dualityMap_comap_iSup_of_pairwise_disjoint` is the same
step for Poincaré duality; there it goes through finite and directed unions, here directly through
the product decompositions. The index type of the main result is arbitrary: the proof first
reindexes the family by its range, a type in the universe of the spaces.

## Main results

* `TopCat.isColimitCofanPreimagePairIUnion`: the pair over a union of pairwise disjoint open sets
  is the coproduct of the pairs over its members.
* `TopCat.isZero_singularHomology_ofInclusion_iUnion_of_pairwiseDisjoint`: the relative homology of
  the pair over such a union vanishes if it does over each member, by Tau Ceti's
  `TopPair.isColimitCofanSingularHomologyOfIsColimit`.
* `TopCat.bijective_pullbackCupRestrict_iUnion_of_pairwiseDisjoint`: the map over a union of
  pairwise disjoint open sets is bijective if it is over each of them.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, proof of Theorem 10.4.
-/

public section

noncomputable section

open CategoryTheory Limits Set Function

universe w

namespace TopCat

variable {K : Type w} [CommRing K] {X Y : TopCat.{w}} (π : X ⟶ Y) (Z : Set X)
  (M : ModuleCat.{w} K)

/-- For a map `π : X ⟶ Y` and `Z ⊆ X`, the pair `(π⁻¹ W, π⁻¹ W ∩ Z)` over the union `W` of
pairwise disjoint open sets `V i` of `Y` is the coproduct in `TopPair` of the pairs
`(π⁻¹ (V i), π⁻¹ (V i) ∩ Z)`, with the inclusions as the cofan legs. -/
def isColimitCofanPreimagePairIUnion {ι : Type w} {V : ι → Set Y} (hV : ∀ i, IsOpen (V i))
    (hd : Pairwise (Disjoint on V)) :
    IsColimit (Cofan.mk (TopPair.ofInclusion
        (inter_subset_left : π ⁻¹' (⋃ i, V i) ∩ Z ⊆ π ⁻¹' (⋃ i, V i)))
      fun i ↦ TopPair.ofInclusionMap (inter_subset_left : π ⁻¹' V i ∩ Z ⊆ π ⁻¹' V i)
        inter_subset_left (ContinuousMap.inclusion (preimage_mono (subset_iUnion V i)))
        fun _ hx ↦ ⟨mem_iUnion_of_mem i hx.1, hx.2⟩) := by
  refine TopPair.isColimitCofanOfIsHomeomorph _ ?_ fun y ↦ ?_
  · refine (congrArg IsHomeomorph (funext fun x : Σ i, ↥(π ⁻¹' V i) ↦
      TopPair.ofInclusionMap_fst_apply _ _ x.2)).mpr ?_
    exact isHomeomorph_sigma_inclusion (fun i ↦ (hV i).preimage π.hom.continuous)
      (fun _ _ hij ↦ (hd hij).preimage π) (fun i ↦ preimage_mono (subset_iUnion V i))
      (preimage_iUnion (f := π)).subset
  · obtain ⟨i, hi⟩ := mem_iUnion.1 y.property.1
    exact ⟨i, ⟨y.val, hi, y.property.2⟩, TopPair.ofInclusionMap_fst_apply _ _ _⟩

/-- **Vanishing of relative homology over disjoint open sets.** For a map `π : X ⟶ Y`, `Z ⊆ X`
and pairwise disjoint open subsets `V i` of `Y`, indexed by any type, if the relative homology of
each pair `(π⁻¹ (V i), π⁻¹ (V i) ∩ Z)` vanishes in degree `n`, then so does that of the pair over
`⋃ i, V i`, since it is the coproduct of the relative homologies over the `V i`. -/
theorem isZero_singularHomology_ofInclusion_iUnion_of_pairwiseDisjoint {C : Type*} [Category C]
    [HasCoproducts.{w} C] [Abelian C] [AB4OfSize.{w} C] (R : C) {ι : Type*} {V : ι → Set Y}
    (hV : ∀ i, IsOpen (V i)) (hd : Pairwise (Disjoint on V)) {n : ℕ}
    (hn : ∀ i, IsZero ((TopPair.ofInclusion (inter_subset_left :
      π ⁻¹' V i ∩ Z ⊆ π ⁻¹' V i)).singularHomology R n)) :
    IsZero ((TopPair.ofInclusion (inter_subset_left :
      π ⁻¹' (⋃ i, V i) ∩ Z ⊆ π ⁻¹' (⋃ i, V i))).singularHomology R n) := by
  -- Reindex by the range of `V`, a type in the universe `w`; its distinct members are disjoint.
  rw [← sUnion_range, sUnion_eq_iUnion]
  exact (TopPair.isColimitCofanSingularHomologyOfIsColimit C R n
    (isColimitCofanPreimagePairIUnion π Z (V := ((↑) : range V → Set Y))
      (fun s ↦ by obtain ⟨_, i, rfl⟩ := s; exact hV i)
      ((pairwise_subtype_iff_pairwise_set _ _).2 hd.range_pairwise))).isZero_pt
    (Functor.isZero _ fun ⟨⟨_, i, rfl⟩⟩ ↦ hn i)

/-- The main result below, for an index type in the universe of the spaces. -/
private theorem bijective_pullbackCupRestrict_iUnion_aux {ι : Type w} {V : ι → Set Y}
    (hV : ∀ i, IsOpen (V i)) (hd : Pairwise (Disjoint on V)) {n p m : ℕ} (h : p + n = m)
    (u : (TopPair.ofSubset Z).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (hu : ∀ i, Bijective (pullbackCupRestrict π Z M (V i) n p m h u)) :
    Bijective (pullbackCupRestrict π Z M (⋃ i, V i) n p m h u) := by
  -- Both sides are products over `ι`, and the maps over the `V i` form an isomorphism of the
  -- diagrams.
  have hA := TauCeti.isLimitFanSingularCohomologyIUnion (ModuleCat.{w} K) (ModuleCat.of K K) K M
    hV hd p
  have hB := TauCeti.TopPair.isLimitFanSingularCohomologyOfIsColimit (ModuleCat.{w} K)
    (ModuleCat.of K K) K M (isColimitCofanPreimagePairIUnion π Z hV hd) m
  let α : Discrete.functor (fun i ↦ (of (V i)).singularCohomology (ModuleCat.of K K) K M p) ≅
      Discrete.functor fun i ↦ (TopPair.ofInclusion (inter_subset_left :
        π ⁻¹' V i ∩ Z ⊆ π ⁻¹' V i)).singularCohomology (ModuleCat.of K K) K M m :=
    Discrete.natIso fun i ↦ (LinearEquiv.ofBijective _ (hu i.as)).toModuleIso
  have hA' := (IsLimit.postcomposeHomEquiv α _).symm hA
  -- The map over the union is the comparison of the two limits, by naturality in the subset.
  have he : ModuleCat.ofHom (pullbackCupRestrict π Z M (⋃ i, V i) n p m h u) =
      (hA'.conePointUniqueUpToIso hB).hom := hB.hom_ext fun i ↦ by
    rw [IsLimit.conePointUniqueUpToIso_hom_comp]
    ext a
    exact (pullbackCupRestrict_naturality π Z M (subset_iUnion V i.as) h u a).symm
  have : IsIso (ModuleCat.ofHom (pullbackCupRestrict π Z M (⋃ i, V i) n p m h u)) := by
    rw [he]
    infer_instance
  exact ConcreteCategory.bijective_of_isIso
    (ModuleCat.ofHom (pullbackCupRestrict π Z M (⋃ i, V i) n p m h u))

/-- **Additivity of `a ↦ π^*a ⌣ u` over disjoint open sets.** Let `π : X ⟶ Y` be a map, `Z ⊆ X`,
`u ∈ Hⁿ(X, Z; K)`, and let `V i` be pairwise disjoint open subsets of `Y`, indexed by any type. If
the maps `TopCat.pullbackCupRestrict` of `u` over the `V i` are bijective in degree `p`, then so is
the map of `u` over `⋃ i, V i`. -/
theorem bijective_pullbackCupRestrict_iUnion_of_pairwiseDisjoint {ι : Type*} {V : ι → Set Y}
    (hV : ∀ i, IsOpen (V i)) (hd : Pairwise (Disjoint on V)) {n p m : ℕ} (h : p + n = m)
    (u : (TopPair.ofSubset Z).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (hu : ∀ i, Bijective (pullbackCupRestrict π Z M (V i) n p m h u)) :
    Bijective (pullbackCupRestrict π Z M (⋃ i, V i) n p m h u) := by
  -- Reindex by the range of `V`, a type in the universe `w`; its distinct members are disjoint.
  rw [← sUnion_range, sUnion_eq_iUnion]
  refine bijective_pullbackCupRestrict_iUnion_aux π Z M (V := ((↑) : range V → Set Y))
    (fun s ↦ ?_) (fun s t hst ↦ ?_) h u fun s ↦ ?_
  · obtain ⟨_, i, rfl⟩ := s
    exact hV i
  · obtain ⟨_, i, rfl⟩ := s
    obtain ⟨_, j, rfl⟩ := t
    exact hd fun hij ↦ hst (by subst hij; rfl)
  · obtain ⟨_, i, rfl⟩ := s
    exact hu i

end TopCat
