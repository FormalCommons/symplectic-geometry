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
import SymplecticGeometry.AlgebraicTopology.Cohomology.Additivity.PullbackCup

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
Ceti's `TauCeti.mayerVietoris_induction`, which needs no finite trivializing cover. It is run
twice over the open sets inside the base set of a linear trivialization. The first run shows that
the relative homology of the Thom pair `(E|_U, E₀|_U)` vanishes below the rank over every open
set `U` of `B`, with coefficients in any abelian category with exact coproducts:

* on the basic open sets by Tau Ceti's `Bundle.Trivialization.isZero_singularHomology_thomPairOver`,
  on the empty set by `TauCeti.isZero_singularHomology_thomPairOver_empty`, on a union of two
  open sets by `TauCeti.isZero_singularHomology_thomPairOver_union`, and on a union of pairwise
  disjoint open sets by `TopCat.isZero_singularHomology_ofInclusion_iUnion_of_pairwiseDisjoint`.

The second run shows that the map `a ↦ π^*a ⌣ u` over `U` (`TopCat.pullbackCupRestrict`) is
bijective in every degree:

* on the basic open sets by Tau Ceti's
  `TauCeti.IsThomClass.bijective_pullbackCupRestrict_of_subset_baseSet`, on the empty set by
  `TopCat.bijective_pullbackCupRestrict_empty`, on a union of two open sets by
  `TopCat.bijective_pullbackCupRestrict_union`, which needs the vanishing of the relative
  cohomology below the rank over the intersection (it follows from that of the homology), and on
  a union of pairwise disjoint open sets by
  `TopCat.bijective_pullbackCupRestrict_iUnion_of_pairwiseDisjoint`.

The step for two open sets is that of Tau Ceti's
`TauCeti.bijective_pullbackCupRestrict_thomPair_biUnion`,
and the global statements follow `TauCeti.bijective_thomMap_of_compactSpace` and
`TauCeti.thomEquivOfCompactSpace`.

## Main results

* `TauCeti.bijective_pullbackCupRestrict_thomPair_of_secondCountableTopology`: over every open set
  `U` of the base, the map `a ↦ π^*a ⌣ u` over `U` is bijective in every degree.
* `TauCeti.isZero_singularHomology_thomPairOver_of_secondCountableTopology`: over every open set
  `U` of the base, the relative homology of the Thom pair over `U` vanishes below the rank.
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

universe w v u

namespace TauCeti

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  {K : Type w} [CommRing K] (M : ModuleCat.{w} K)

variable [VectorBundle ℝ F E]

/-- The open sets of the base that lie in the base set of a linear trivialization: the basis of
the Mayer–Vietoris inductions of this file. -/
private def trivializingOpens : Set (Opens B) :=
  {U | ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), (U : Set B) ⊆ e.baseSet}

private theorem isBasis_trivializingOpens : Opens.IsBasis (trivializingOpens (F := F) (E := E)) :=
  Opens.isBasis_iff_nbhd.2 fun {U x} hx ↦
    ⟨U ⊓ ⟨_, (trivializationAt F E x).open_baseSet⟩,
      ⟨trivializationAt F E x, inferInstance, inter_subset_right⟩,
      ⟨hx, mem_baseSet_trivializationAt F E x⟩, inf_le_left⟩

omit [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E] in
private theorem inf_mem_trivializingOpens {U V : Opens B}
    (hU : U ∈ trivializingOpens (F := F) (E := E)) (_ : V ∈ trivializingOpens (F := F) (E := E))
    (_ : ((U ⊓ V : Opens B) : Set B).Nonempty) : U ⊓ V ∈ trivializingOpens (F := F) (E := E) :=
  let ⟨e, he, hU⟩ := hU
  ⟨e, he, inter_subset_left.trans hU⟩

/-- **The relative homology of the Thom pair over an open set below the rank.** For a real vector
bundle `E → B` of finite rank `r` over a Hausdorff, locally compact, second-countable space `B`,
every open set `U` of `B` and every coefficient object `R` of an abelian category with exact
coproducts, the relative homology `Hⱼ(E|_U, E₀|_U; R)` vanishes for `j < r`. -/
theorem isZero_singularHomology_thomPairOver_of_secondCountableTopology
    [T2Space B] [LocallyCompactSpace B] [SecondCountableTopology B] [FiniteDimensional ℝ F]
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] [AB4OfSize.{w} C] (R : C)
    (U : Opens B) {j : ℕ} (hj : j < finrank ℝ F) :
    IsZero ((thomPairOver F E U).singularHomology R j) := by
  revert U j
  refine mayerVietoris_induction _ _ (isBasis_trivializingOpens (F := F) (E := E))
    (fun _ hU _ hV ↦ inf_mem_trivializingOpens hU hV) ?_ ?_ ?_ ?_
  · -- The empty set.
    exact fun _ ↦ isZero_singularHomology_thomPairOver_empty _ _
  · -- The basic open sets.
    rintro U ⟨e, he, hU⟩ - j hj
    exact e.isZero_singularHomology_thomPairOver hU _ hj
  · -- Unions of two open sets.
    intro U V hU hV hUV j hj
    exact isZero_singularHomology_thomPairOver_union _ U.isOpen V.isOpen (hU hj) (hV hj)
      fun i hi ↦ hUV (by omega)
  · -- Countable unions of pairwise disjoint open sets.
    intro s hd hs j hj
    have h := TopCat.isZero_singularHomology_ofInclusion_iUnion_of_pairwiseDisjoint
      (thomPairProj F E) (zeroSectionCompl F E) R (fun n ↦ (s n).isOpen)
      (fun i j hij ↦ Opens.coe_disjoint.2 (hd i j hij))
      fun n ↦ by rw [thomPairProj_def]; exact hs n hj
    rw [Opens.coe_iSup]
    rwa [thomPairProj_def] at h

/-- **The Thom map over an open set of a second-countable base.** For a Thom class `u` of a
real vector bundle `E → B` of finite rank `r` over a Hausdorff, locally compact, second-countable
space `B`, and every open set `U` of `B`, the map `Hᵖ(U; M) ⟶ Hᵖ⁺ʳ(E|_U, E₀|_U; M)`,
`a ↦ π^*a ⌣ u`, is bijective in every degree `p`. -/
theorem bijective_pullbackCupRestrict_thomPair_of_secondCountableTopology
    [T2Space B] [LocallyCompactSpace B] [SecondCountableTopology B]
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) (U : Opens B) (p : ℕ) :
    Function.Bijective (TopCat.pullbackCupRestrict (thomPairProj F E)
      (zeroSectionCompl F E) M U (finrank ℝ F) p (p + finrank ℝ F) rfl u) := by
  have := (isThomClass_iff.1 hu).1
  revert U p
  refine mayerVietoris_induction _ _ (isBasis_trivializingOpens (F := F) (E := E))
    (fun _ hU _ hV ↦ inf_mem_trivializingOpens hU hV) ?_ ?_ ?_ ?_
  · -- The empty set.
    exact fun p ↦ TopCat.bijective_pullbackCupRestrict_empty _ _ M rfl u
  · -- The basic open sets.
    rintro U ⟨e, he, hU⟩ - p
    exact hu.bijective_pullbackCupRestrict_of_subset_baseSet M e hU rfl
  · -- Unions of two open sets: the relative cohomology over `U ∩ V` vanishes below the rank, since
    -- its homology does.
    intro U V hU hV hUV p
    refine TopCat.bijective_pullbackCupRestrict_union (thomPairProj F E)
      (zeroSectionCompl F E) M U.isOpen V.isOpen u (fun q _ ↦ hU q) (fun q _ ↦ hV q)
      (fun q _ ↦ hUV q) (fun j hj ↦ ?_) rfl
    exact TopPair.isZero_singularCohomology_of_isZero_singularHomology _ (ModuleCat.of K K) M j
      fun i hi ↦ by
        rw [thomPairProj_def]
        exact isZero_singularHomology_thomPairOver_of_secondCountableTopology (ModuleCat.of K K)
          (U ⊓ V) (by omega)
  · -- Countable unions of pairwise disjoint open sets.
    intro s hd hs p
    rw [Opens.coe_iSup]
    exact TopCat.bijective_pullbackCupRestrict_iUnion_of_pairwiseDisjoint _ _ M
      (fun n ↦ (s n).isOpen) (fun i j hij ↦ Opens.coe_disjoint.2 (hd i j hij)) rfl u
      fun n ↦ hs n p

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
  exact bijective_pullbackCupRestrict_thomPair_of_secondCountableTopology M hu ⊤ p

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
