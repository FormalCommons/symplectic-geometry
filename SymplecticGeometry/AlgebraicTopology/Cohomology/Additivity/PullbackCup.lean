/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Additivity.Basic
public import TauCeti.AlgebraicTopology.Cohomology.Additivity.Relative
public import TauCeti.AlgebraicTopology.Cohomology.Cup.Pullback

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
cohomology carries these disjoint unions to products (`TauCeti.isLimitFanSingularCohomologyIUnion`,
from Tau Ceti's `TauCeti.isLimitFanSingularCohomology`, and Tau Ceti's
`TauCeti.TopPair.isLimitFanSingularCohomologyOfIsColimit`), and the map over the union is
compatible with the restrictions to the `V i` (`TopCat.pullbackCupRestrict_naturality`). So it is
the product of the maps over the `V i`, which are isomorphisms. Tau Ceti's
`TauCeti.HomologicalOrientation.bijective_dualityMap_comap_iSup_of_pairwise_disjoint` is the same
step for Poincaré duality; there it goes through finite and directed unions, here directly through
the product decompositions.

## Main results

* `Set.isHomeomorph_sigma_inclusion`: a set covered by pairwise disjoint open subsets is
  homeomorphic to their disjoint union.
* `TauCeti.isLimitFanSingularCohomologyIUnion`: the singular cohomology of a union of pairwise
  disjoint open sets is the product of their cohomologies.
* `TopCat.isColimitCofanPreimagePairIUnion`: the pair over such a union is the coproduct of the
  pairs over its members.
* `TopCat.bijective_pullbackCupRestrict_iUnion_of_pairwiseDisjoint`: the map over a union of
  pairwise disjoint open sets is bijective if it is over each of them.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, proof of Theorem 10.4.
-/

public section

noncomputable section

open CategoryTheory Limits Set Function

universe w v u

/-- A subset `t` of a space that is the union of pairwise disjoint open subsets `s i ⊆ t` is
homeomorphic to their disjoint union, by the map that includes each `s i` into `t`. For
`t = ⋃ i, s i` this is the inverse of Mathlib's `Homeomorph.Set.iUnion`. -/
theorem Set.isHomeomorph_sigma_inclusion {X : Type*} [TopologicalSpace X] {ι : Type*}
    {s : ι → Set X} {t : Set X} (hs : ∀ i, IsOpen (s i)) (hd : Pairwise (Disjoint on s))
    (hst : ∀ i, s i ⊆ t) (ht : t ⊆ ⋃ i, s i) :
    IsHomeomorph fun x : Σ i, s i ↦ inclusion (hst x.1) x.2 := by
  refine ⟨continuous_sigma fun i ↦ continuous_inclusion (hst i),
    isOpenMap_sigma.2 fun i ↦ (hs i).isOpenMap_inclusion (hst i), ?_, fun y ↦ ?_⟩
  · rintro ⟨i, x⟩ ⟨j, y⟩ hxy
    have hxy' : (x : X) = y := congrArg Subtype.val hxy
    obtain rfl : i = j := by
      by_contra hij
      exact (hd hij).ne_of_mem x.property y.property hxy'
    exact Sigma.ext rfl (heq_of_eq (Subtype.ext hxy'))
  · obtain ⟨i, hi⟩ := mem_iUnion.1 (ht y.property)
    exact ⟨⟨i, ⟨y, hi⟩⟩, rfl⟩

namespace TauCeti

variable {ι : Type w} {X : TopCat.{w}} {V : ι → Set X}
  (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  (k : Type*) [Ring k] [Linear k C] (M : C)

/-- **Additivity of singular cohomology over disjoint open sets.** In every degree, the singular
cohomology of a union of pairwise disjoint open sets `V i` is the product of the singular
cohomologies of the `V i`, with the restrictions to the `V i` as projections. -/
def isLimitFanSingularCohomologyIUnion [Small.{v} ι] (hV : ∀ i, IsOpen (V i))
    (hd : Pairwise (Disjoint on V)) (n : ℕ) :
    IsLimit (Fan.mk ((TopCat.of ↥(⋃ i, V i)).singularCohomology R k M n)
      (fun i ↦ TopCat.singularCohomologyMap
        (TopCat.ofHom (ContinuousMap.inclusion (subset_iUnion V i))) n) :
      Fan fun i ↦ (TopCat.of (V i)).singularCohomology R k M n) :=
  -- The disjoint union of the `V i` maps homeomorphically onto their union.
  let σ : TopCat.of (Σ i, V i) ⟶ TopCat.of ↥(⋃ i, V i) :=
    TopCat.ofHom ⟨_, (isHomeomorph_sigma_inclusion hV hd (subset_iUnion V) subset_rfl).continuous⟩
  have : IsIso σ := (TopCat.isIso_iff_isHomeomorph σ).2
    (isHomeomorph_sigma_inclusion hV hd (subset_iUnion V) subset_rfl)
  -- `singularCohomologyFunctor` is exposed and sends `σ.op` to `singularCohomologyMap σ n` by
  -- definition; its `simps` lemmas cannot rewrite here, since the source and target of the map
  -- depend on `obj`.
  have : IsIso (TopCat.singularCohomologyMap (R := R) (k := k) (M := M) σ n) :=
    (inferInstance : IsIso ((singularCohomologyFunctor R k M n).map σ.op))
  IsLimit.ofIsoLimit (isLimitFanSingularCohomology (fun i ↦ TopCat.of (V i)) C R k M n)
    (Fan.ext (asIso (TopCat.singularCohomologyMap σ n)).symm fun i ↦ by
      rw [Iso.symm_hom, asIso_inv, IsIso.eq_inv_comp]
      exact (TopCat.singularCohomologyMap_comp _ _ n).symm)

end TauCeti

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

/-- **Additivity of `a ↦ π^*a ⌣ u` over disjoint open sets.** Let `π : X ⟶ Y` be a map, `Z ⊆ X`,
`u ∈ Hⁿ(X, Z; K)`, and let `V i` be pairwise disjoint open subsets of `Y`. If the maps
`TopCat.pullbackCupRestrict` of `u` over the `V i` are bijective in degree `p`, then so is the map
of `u` over `⋃ i, V i`. -/
theorem bijective_pullbackCupRestrict_iUnion_of_pairwiseDisjoint {ι : Type w} {V : ι → Set Y}
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

end TopCat
