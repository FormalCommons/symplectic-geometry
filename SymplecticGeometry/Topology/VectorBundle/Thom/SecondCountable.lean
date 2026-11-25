/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.PullbackCup
public import TauCeti.Topology.MayerVietoris
public import TauCeti.Topology.VectorBundle.Thom.Isomorphism
public import TauCeti.Topology.VectorBundle.MayerVietoris.Basic
public import SymplecticGeometry.AlgebraicTopology.Cohomology.Additivity.PullbackCup

/-!
# The Thom isomorphism over a second-countable base

Let `E → B` be a real vector bundle of finite rank `r = finrank ℝ F` over a Hausdorff, locally
compact, second-countable space `B`, and let `u ∈ Hʳ(E, E₀; K)` be a Thom class, with coefficients
in a commutative ring `K`. This file proves that for every `K`-module `M` the Thom map
`Hᵖ(B; M) ⟶ Hᵖ⁺ʳ(E, E₀; M)`, `a ↦ π^*a ⌣ u`, is bijective
(`TauCeti.bijective_thomMap_of_secondCountableTopology`), and bundles it as a linear equivalence
(`TauCeti.thomEquivOfSecondCountableTopology`). Tau Ceti proves this over a compact base
(`TauCeti.thomEquivOfCompactSpace`), and over any base when `K` is a field.

The proof is the Mayer–Vietoris argument of Milnor and Stasheff, Theorem 10.4, arranged by Tau
Ceti's `TauCeti.mayerVietoris_induction`, which needs no finite trivializing cover. The property
of an open set `U` of `B` that the induction carries is that the map `a ↦ π^*a ⌣ u` over `U`
(`TopCat.pullbackCupRestrict`) is bijective in every degree and that the relative homology of the
Thom pair `(E|_U, E₀|_U)` vanishes below the rank:

* on the open sets inside the base set of a linear trivialization, by Tau Ceti's
  `TauCeti.IsThomClass.bijective_pullbackCupRestrict_of_subset_baseSet` and
  `Bundle.Trivialization.isZero_singularHomology_thomPairOver`;
* on the empty set, by `TopCat.bijective_pullbackCupRestrict_empty` and
  `TauCeti.isZero_singularHomology_thomPairOver_empty`;
* on a union of two open sets, by `TopCat.bijective_pullbackCupRestrict_union`, which needs the
  vanishing of the relative cohomology below the rank over the intersection (it follows from that
  of the homology), and `TauCeti.isZero_singularHomology_thomPairOver_union`;
* on a union of pairwise disjoint open sets, by
  `TopCat.bijective_pullbackCupRestrict_iUnion_of_pairwiseDisjoint` and
  `TauCeti.isZero_singularHomology_thomPairOver_iUnion_of_pairwiseDisjoint`.

The step for two open sets is that of Tau Ceti's
`TauCeti.bijective_pullbackCupRestrict_thomPair_biUnion`,
and the global statements follow `TauCeti.bijective_thomMap_of_compactSpace` and
`TauCeti.thomEquivOfCompactSpace`.

## Main results

* `TauCeti.isZero_singularHomology_thomPairOver_iUnion_of_pairwiseDisjoint`: the relative homology
  of the Thom pair over a union of pairwise disjoint open sets vanishes if it does over each.
* `TauCeti.bijective_thomMap_of_secondCountableTopology`: the Thom map of a Thom class over a
  Hausdorff, locally compact, second-countable base is bijective in every degree.
* `TauCeti.thomEquivOfSecondCountableTopology`: the Thom isomorphism
  `Hᵖ(B; M) ≃ₗ[K] Hᵐ(E, E₀; M)`, `p + r = m`, with `thomEquivOfSecondCountableTopology_apply`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Theorem 10.4 and its proof.
-/

public section

noncomputable section

open Bundle CategoryTheory Function Limits Module Set TopologicalSpace

universe w

namespace TauCeti

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  {K : Type w} [CommRing K] (M : ModuleCat.{w} K)

omit [NormedSpace ℝ F] [∀ b, Module ℝ (E b)] in
/-- The pair over `W` of `TopCat.pullbackCupRestrict` along `TauCeti.thomPairProj` is the Thom pair
`TauCeti.thomPairOver F E W`, so the vanishing of the homology of the latter gives that of the
cohomology of the former. -/
private theorem isZero_singularCohomology_thomPairProj_of_isZero_singularHomology (W : Set B)
    {j : ℕ} (hW : ∀ i ≤ j, IsZero ((thomPairOver F E W).singularHomology (ModuleCat.of K K) i)) :
    IsZero ((TopPair.ofInclusion (inter_subset_left :
      thomPairProj F E ⁻¹' W ∩ zeroSectionCompl F E ⊆ thomPairProj F E ⁻¹' W)).singularCohomology
        (ModuleCat.of K K) K M j) := by
  suffices ∀ π' : TopCat.of (TotalSpace F E) ⟶ TopCat.of B, π' = thomPairProj F E →
      IsZero ((TopPair.ofInclusion (inter_subset_left :
        π' ⁻¹' W ∩ zeroSectionCompl F E ⊆ π' ⁻¹' W)).singularCohomology
          (ModuleCat.of K K) K M j) from
    this _ rfl
  intro π' hπ'
  rw [thomPairProj_def] at hπ'
  subst hπ'
  exact TopPair.isZero_singularCohomology_of_isZero_singularHomology _ (ModuleCat.of K K) M j hW

omit [NormedSpace ℝ F] [∀ b, Module ℝ (E b)] in
/-- **The relative homology of the Thom pair over a disjoint union.** For pairwise disjoint open
sets `V i` of the base, indexed by any type, if `Hⱼ(E|_{V i}, E₀|_{V i})` vanishes for every `i`,
then so does `Hⱼ(E|_{⋃ i, V i}, E₀|_{⋃ i, V i})`. -/
theorem isZero_singularHomology_thomPairOver_iUnion_of_pairwiseDisjoint {C : Type*} [Category C]
    [HasCoproducts.{w} C] [Abelian C] [AB4OfSize.{w} C] (R : C) {ι : Type*} {V : ι → Set B}
    (hV : ∀ i, IsOpen (V i)) (hd : Pairwise (Disjoint on V)) {j : ℕ}
    (hj : ∀ i, IsZero ((thomPairOver F E (V i)).singularHomology R j)) :
    IsZero ((thomPairOver F E (⋃ i, V i)).singularHomology R j) := by
  suffices ∀ π' : TopCat.of (TotalSpace F E) ⟶ TopCat.of B, π' = thomPairProj F E →
      IsZero ((TopPair.ofInclusion (inter_subset_left :
        π' ⁻¹' (⋃ i, V i) ∩ zeroSectionCompl F E ⊆ π' ⁻¹' (⋃ i, V i))).singularHomology R j) by
    have h := this _ rfl
    rw [thomPairProj_def] at h
    exact h
  intro π' hπ'
  refine TopCat.isZero_singularHomology_ofInclusion_iUnion_of_pairwiseDisjoint π'
    (zeroSectionCompl F E) R hV hd fun i ↦ ?_
  rw [hπ', thomPairProj_def]
  exact hj i

variable [VectorBundle ℝ F E] [FiniteDimensional ℝ F]

/-- The property that the Mayer–Vietoris induction carries holds on every open set `U` of the
base: the map `a ↦ π^*a ⌣ u` over `U` is bijective in every degree, and the relative homology of
the Thom pair over `U` vanishes below the rank. -/
private theorem bijective_pullbackCupRestrict_and_isZero_of_secondCountableTopology
    [T2Space B] [LocallyCompactSpace B] [SecondCountableTopology B]
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) (U : Opens B) :
    (∀ q, Function.Bijective (TopCat.pullbackCupRestrict (thomPairProj F E)
      (zeroSectionCompl F E) M U (finrank ℝ F) q (q + finrank ℝ F) rfl u)) ∧
    ∀ j < finrank ℝ F, IsZero ((thomPairOver F E U).singularHomology (ModuleCat.of K K) j) := by
  revert U
  refine mayerVietoris_induction _
    {U | ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), (U : Set B) ⊆ e.baseSet}
    (Opens.isBasis_iff_nbhd.2 fun {U x} hx ↦ ?_) ?_ ?_ ?_ ?_ ?_
  · -- The basis: the open sets inside the base set of a linear trivialization.
    refine ⟨U ⊓ ⟨_, (trivializationAt F E x).open_baseSet⟩,
      ⟨trivializationAt F E x, inferInstance, inter_subset_right⟩,
      ⟨hx, mem_baseSet_trivializationAt F E x⟩, inf_le_left⟩
  · rintro U ⟨e, he, hU⟩ V - -
    exact ⟨e, he, inter_subset_left.trans hU⟩
  · -- The empty set.
    exact ⟨fun q ↦ TopCat.bijective_pullbackCupRestrict_empty _ _ M rfl u,
      fun j _ ↦ isZero_singularHomology_thomPairOver_empty _ j⟩
  · -- The basic open sets.
    rintro U ⟨e, he, hU⟩ -
    exact ⟨fun q ↦ hu.bijective_pullbackCupRestrict_of_subset_baseSet M e hU rfl,
      fun j hj ↦ e.isZero_singularHomology_thomPairOver hU _ hj⟩
  · -- Unions of two open sets.
    rintro U V ⟨hU, hU₀⟩ ⟨hV, hV₀⟩ ⟨hUV, hUV₀⟩
    refine ⟨fun q ↦ TopCat.bijective_pullbackCupRestrict_union (thomPairProj F E)
      (zeroSectionCompl F E) M U.isOpen V.isOpen u (fun q _ ↦ hU q) (fun q _ ↦ hV q)
      (fun q _ ↦ hUV q) (fun j hj ↦ ?_) rfl, fun j hj ↦ ?_⟩
    · exact isZero_singularCohomology_thomPairProj_of_isZero_singularHomology M _ (j := j)
        fun i hi ↦ hUV₀ i (by omega)
    · exact isZero_singularHomology_thomPairOver_union _ U.isOpen V.isOpen (hU₀ j hj) (hV₀ j hj)
        fun i hi ↦ hUV₀ i (by omega)
  · -- Countable unions of pairwise disjoint open sets.
    intro s hd hs
    have hd' : Pairwise (Disjoint on fun n ↦ (s n : Set B)) := fun i j hij ↦
      Opens.coe_disjoint.2 (hd i j hij)
    rw [Opens.coe_iSup]
    exact ⟨fun q ↦ TopCat.bijective_pullbackCupRestrict_iUnion_of_pairwiseDisjoint _ _ M
        (fun n ↦ (s n).isOpen) hd' rfl u fun n ↦ (hs n).1 q,
      fun j hj ↦ isZero_singularHomology_thomPairOver_iUnion_of_pairwiseDisjoint _
        (fun n ↦ (s n).isOpen) hd' fun n ↦ (hs n).2 j hj⟩

/-- **The Thom isomorphism over a second-countable base** (Milnor–Stasheff, Theorem 10.4): for a
real vector bundle `E → B` of finite rank `r` over a Hausdorff, locally compact, second-countable
space `B` and a Thom class `u ∈ Hʳ(E, E₀; K)`, the Thom map `Hᵖ(B; M) ⟶ Hᵐ(E, E₀; M)`,
`a ↦ π^*a ⌣ u`, `p + r = m`, is bijective for every `K`-module `M`. -/
theorem bijective_thomMap_of_secondCountableTopology [T2Space B] [LocallyCompactSpace B]
    [SecondCountableTopology B] (p m : ℕ) (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    Function.Bijective (thomMap F E M (finrank ℝ F) p m h u) := by
  subst h
  rw [thomMap_def]
  refine (TopCat.bijective_pullbackCupRestrict_univ_iff _ _ M rfl u).1 ?_
  rw [← Opens.coe_top]
  exact (bijective_pullbackCupRestrict_and_isZero_of_secondCountableTopology M hu ⊤).1 p

variable (F E) in
/-- **The Thom isomorphism over a second-countable base**, bundled as
`Hᵖ(B; M) ≃ₗ[K] Hᵐ(E, E₀; M)`. -/
def thomEquivOfSecondCountableTopology [T2Space B] [LocallyCompactSpace B]
    [SecondCountableTopology B] (p m : ℕ) (h : p + finrank ℝ F = m := by lia)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (hu : IsThomClass F E u) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPair F E).singularCohomology (ModuleCat.of K K) K M m :=
  LinearEquiv.ofBijective _ (bijective_thomMap_of_secondCountableTopology M p m h hu)

/-- `TauCeti.thomEquivOfSecondCountableTopology` applies `TauCeti.thomMap`. -/
@[simp]
theorem thomEquivOfSecondCountableTopology_apply [T2Space B] [LocallyCompactSpace B]
    [SecondCountableTopology B] (p m : ℕ) (h : p + finrank ℝ F = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (hu : IsThomClass F E u) (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    thomEquivOfSecondCountableTopology F E M p m h u hu a =
      thomMap F E M (finrank ℝ F) p m h u a := (rfl)

end TauCeti
