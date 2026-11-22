/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.Compl
public import SymplecticGeometry.Algebra.Homology.ModuleCat.Basic

/-!
# Cochain representatives of the Mayer–Vietoris connecting map for two closed sets

For closed sets `K` and `N` of a space `X`, Tau Ceti's
`TopCat.singularCohomologyComplMayerVietorisδ` is the connecting map
`Hᵖ(X, X ∖ (K ∪ N)) ⟶ Hᵖ⁺¹(X, X ∖ (K ∩ N))` of the Mayer–Vietoris sequence of the pairs
`(X, X ∖ K)` and `(X, X ∖ N)`. Given a class `a` in the source and a cocycle `ζ` representing its
image, `TopCat.exists_singularCohomologyComplMayerVietorisδ_representatives` gives cochains `u` of
`(X, X ∖ K)` and `v` of `(X, X ∖ N)` with coboundaries the restrictions of `ζ`, and a cocycle `α`
of `(X, X ∖ (K ∪ N))` representing `a`, with `u - v = α` after restriction. These are cochains of
the pairs themselves, not of the pairs of small chains through which the sequence is built.

This lemma is from Tau Ceti's main branch
(`TauCeti/AlgebraicTopology/Cohomology/MayerVietoris/Compl.lean`, same name), as of the commit
`e48a7f81a81426270765022681d165be592a3231`, not yet in the pinned release; it is stated here under
its Tau Ceti name, so that moving Tau Ceti past it deletes this file without renames. Its proof
uses three steps of its own, private as there.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3, the proof of
  Lemma 3.36.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex Topology

universe w v u

namespace TopCat

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] {R : C}
  {k : Type*} [Ring k] [Linear k C] {M : C} {X : TopCat.{w}}

/-! ### Exact cochain representatives of the complement connecting morphism -/

variable (R k M)

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts
attribute [local instance] TopPair.mono_toSSetPair_map_ofInclusionMap_inclusion_right

/-- A chosen cocycle for the native connecting class is the exact coboundary of a lift. -/
private lemma exists_complMayerVietoris_cochains
    {K N : Set X} (hK : IsClosed K) (hN : IsClosed N) (p : ℕ)
    (a : (TopPair.ofSubset (K ∪ N)ᶜ).singularCohomology R k M p)
    (ζ : ((TopPair.ofSubset (K ∩ N)ᶜ).singularCochainComplex R k M).cycles (p + 1))
    (hζ : ((TopPair.ofSubset (K ∩ N)ᶜ).singularCochainComplex R k M).homologyπ (p + 1) ζ =
      TopCat.singularCohomologyComplMayerVietorisδ R k M
        hK hN p (p + 1) rfl a) :
    let C := SSetPair.mayerVietorisCochainShortComplex R k M
      (MorphismProperty.Arrow.Hom.ext (TopCat.isPushout_toSmallSingularPair_left
          (Set.subset_univ Kᶜ) (Set.subset_univ Nᶜ)).w (TopCat.isPushout_toSmallSingularPair_right
          (Set.subset_univ Kᶜ) (Set.subset_univ Nᶜ)).w)
    let g := TopPair.singularCochainComplexMap
      (R := R) (k := k) (M := M) (TopCat.unionComplPairIso K N).hom ≫
        SSetPair.cochainComplexMap
          (TopCat.smallSingularPairToUnion (Set.subset_univ Kᶜ) (Set.subset_univ Nᶜ))
    ∃ (x₂ : C.X₂.X p) (α : C.X₃.cycles p),
      (C.X₂.d p (p + 1)).hom x₂ = (C.f.f (p + 1)).hom
          ((C.X₁.iCycles (p + 1)).hom (cyclesMap g (p + 1) ζ)) ∧
        (C.g.f p).hom x₂ = (C.X₃.iCycles p).hom α ∧
          (C.X₃.homologyπ p).hom α =
            TopPair.singularCohomologyMap (TopCat.interComplPairIso K N).hom p a := by
  dsimp only
  have hS := SSetPair.shortExact_mayerVietorisCochainShortComplex R k M
    (TopCat.isPushout_toSmallSingularPair_left (Set.subset_univ Kᶜ) (Set.subset_univ Nᶜ))
    (TopCat.isPushout_toSmallSingularPair_right (Set.subset_univ Kᶜ) (Set.subset_univ Nᶜ))
  apply hS.moduleCat_exists_d_eq_of_δ_eq p (p + 1) rfl
  have hc := ConcreteCategory.congr_hom
    (TopCat.singularCohomologyPairMayerVietorisδ_comp_homologyMap
      R k M (Set.subset_univ Kᶜ) (Set.subset_univ Nᶜ)
      isOpen_univ isOpen_univ (hK.isOpen_compl.preimage continuous_subtypeVal)
      (hN.isOpen_compl.preimage continuous_subtypeVal) p (p + 1) rfl)
    (TopPair.singularCohomologyMap (TopCat.interComplPairIso K N).hom p a)
  rw [SSetPair.mayerVietorisCochainδ_def R k M
    (TopCat.isPushout_toSmallSingularPair_left (Set.subset_univ Kᶜ) (Set.subset_univ Nᶜ))
    (TopCat.isPushout_toSmallSingularPair_right (Set.subset_univ Kᶜ) (Set.subset_univ Nᶜ))
    p (p + 1) rfl] at hc
  rw [← hc]
  have hpair := congrArg
    (TopPair.singularCohomologyMap (TopCat.unionComplPairIso K N).hom (p + 1)) hζ
  rw [TopCat.singularCohomologyComplMayerVietorisδ_def R k M hK hN p (p + 1) rfl] at hpair
  simp only [ConcreteCategory.comp_apply] at hpair
  conv_rhs at hpair =>
    rw [← ConcreteCategory.comp_apply, ← TopPair.singularCohomologyMap_comp,
      Iso.hom_inv_id, TopPair.singularCohomologyMap_id, ConcreteCategory.id_apply]
  rw [ConcreteCategory.comp_apply, ← hpair]
  rw [moduleCat_homologyMap_homologyπ, moduleCat_homologyMap_homologyπ]
  simp only [cyclesMap_comp, ConcreteCategory.comp_apply]

private lemma complement_cochain_square (K N S : Set X) (i : Fin 2)
    (hS : Sᶜ ⊆ ![Kᶜ, Nᶜ] i) (hIS : K ∩ N ⊆ S) :
    TopPair.singularCochainComplexMap
        (R := R) (k := k) (M := M) (TopCat.unionComplPairIso K N).hom ≫
      SSetPair.cochainComplexMap
        (TopCat.smallSingularPairToUnion (Set.subset_univ Kᶜ) (Set.subset_univ Nᶜ)) ≫
      SSetPair.cochainComplexMap
        (TopCat.toSmallSingularPair (Set.subset_univ Kᶜ) (Set.subset_univ Nᶜ)
          (Set.subset_univ Sᶜ) (i := i) (by fin_cases i <;> simp) hS) ≫
      TopPair.singularCochainComplexMap (TopCat.univComplPairIso S).inv =
    TopPair.singularCochainComplexMap (TopPair.ofSubsetMap (𝟙 X) (TopCat.mapsTo_id_compl hIS)) := by
  let r := TopCat.toSmallSingularPair (Set.subset_univ Kᶜ) (Set.subset_univ Nᶜ)
    (Set.subset_univ Sᶜ) (i := i) (by fin_cases i <;> simp) hS
  let j := TopCat.smallSingularPairToUnion (Set.subset_univ Kᶜ) (Set.subset_univ Nᶜ)
  have hc : Sᶜ ⊆ Kᶜ ∪ Nᶜ := by simpa only [← Set.compl_inter] using Set.compl_subset_compl.mpr hIS
  have hsmall : SSetPair.cochainComplexMap (R := R)
      (k := k) (M := M) j ≫ SSetPair.cochainComplexMap r =
      TopPair.singularCochainComplexMap (TopPair.ofInclusionMap (Set.subset_univ Sᶜ)
        (Set.union_subset_union (Set.subset_univ Kᶜ) (Set.subset_univ Nᶜ))
        (ContinuousMap.inclusion (by simp : Set.univ ⊆ (Set.univ : Set X) ∪ Set.univ))
        (fun _ hx ↦ hc hx)) := by
    rw [← SSetPair.cochainComplexMap_comp]
    erw [TopCat.toSmallSingularPair_comp_smallSingularPairToUnion
      (Set.subset_univ Kᶜ) (Set.subset_univ Nᶜ) (Set.subset_univ Sᶜ)
      (i := i) (by fin_cases i <;> simp) hS (by simp) hc]
  erw [← Category.assoc (SSetPair.cochainComplexMap
      (R := R) (k := k) (M := M) j)
    (SSetPair.cochainComplexMap (R := R) (k := k) (M := M) r) (TopPair.singularCochainComplexMap
      (R := R) (k := k) (M := M) (TopCat.univComplPairIso S).inv), hsmall]
  rw [← Category.assoc, ← TopPair.singularCochainComplexMap_comp]
  erw [TopPair.ofInclusionMap_inclusion_comp_ofInclusionIsoOfSubset_hom
    Set.mem_univ (fun x ↦ Set.mem_union_left _ (Set.mem_univ x))
    (fun _ ↦ Iff.rfl) (fun _ ↦ by rw [Set.compl_inter]) (by simp)
    (fun _ hx ↦ hc hx) (TopCat.mapsTo_id_compl hIS),
    TopPair.singularCochainComplexMap_comp]
  rw [Category.assoc, ← TopPair.singularCochainComplexMap_comp,
    Iso.inv_hom_id, TopPair.singularCochainComplexMap_id, Category.comp_id]

private lemma complement_inter_cochain_square (K N S : Set X) (hS : S ⊆ K ∪ N) :
    let hmaps : ∀ x : (Set.univ ∩ Set.univ : Set X),
        (x : X) ∈ Kᶜ ∩ Nᶜ → (x : X) ∈ Sᶜ :=
      fun _ hx ↦ Set.compl_subset_compl.mpr hS (by simpa only [Set.compl_union] using hx)
    TopPair.singularCochainComplexMap
        (R := R) (k := k) (M := M) (TopPair.ofInclusionMap
          (Set.inter_subset_inter (Set.subset_univ Kᶜ) (Set.subset_univ Nᶜ))
          (Set.subset_univ Sᶜ) (ContinuousMap.inclusion Set.inter_subset_left)
          hmaps) ≫
      TopPair.singularCochainComplexMap (TopCat.interComplPairIso K N).inv =
      TopPair.singularCochainComplexMap (TopCat.univComplPairIso S).inv ≫
        TopPair.singularCochainComplexMap
          (TopPair.ofSubsetMap (𝟙 X) (TopCat.mapsTo_id_compl hS)) := by
  intro hmaps
  rw [← TopPair.singularCochainComplexMap_comp, ← TopPair.singularCochainComplexMap_comp]
  apply congrArg (fun f ↦ TopPair.singularCochainComplexMap
    (R := R) (k := k) (M := M) f)
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  exact TopPair.ofInclusionMap_inclusion_comp_ofInclusionIsoOfSubset_hom
    (fun x ↦ Set.mem_inter (Set.mem_univ x) (Set.mem_univ x)) Set.mem_univ
    (fun _ ↦ by rw [Set.compl_union]) (fun _ ↦ Iff.rfl) Set.inter_subset_left
    hmaps
    (TopCat.mapsTo_id_compl hS)

/-- Exact original-pair representatives of the native complement connecting class. -/
lemma exists_singularCohomologyComplMayerVietorisδ_representatives
        {K N : Set X} (hK : IsClosed K) (hN : IsClosed N) (p : ℕ)
    (a : (TopPair.ofSubset (K ∪ N)ᶜ).singularCohomology R k M p)
    (ζ : ((TopPair.ofSubset (K ∩ N)ᶜ).singularCochainComplex R k M).cycles (p + 1))
    (hζ : ((TopPair.ofSubset (K ∩ N)ᶜ).singularCochainComplex R k M).homologyπ (p + 1) ζ =
      TopCat.singularCohomologyComplMayerVietorisδ R k M
        hK hN p (p + 1) rfl a) :
    ∃ (u : ((TopPair.ofSubset Kᶜ).singularCochainComplex R k M).X p)
      (v : ((TopPair.ofSubset Nᶜ).singularCochainComplex R k M).X p)
      (α : ((TopPair.ofSubset (K ∪ N)ᶜ).singularCochainComplex R k M).cycles p),
      ((TopPair.ofSubset Kᶜ).singularCochainComplex R k M).d p (p + 1) u =
        (TopPair.singularCochainComplexMap
          (TopPair.ofSubsetMap (𝟙 X) (TopCat.mapsTo_id_compl Set.inter_subset_left))).f (p + 1)
          (((TopPair.ofSubset (K ∩ N)ᶜ).singularCochainComplex R k M).iCycles (p + 1) ζ) ∧
      ((TopPair.ofSubset Nᶜ).singularCochainComplex R k M).d p (p + 1) v =
        (TopPair.singularCochainComplexMap
          (TopPair.ofSubsetMap (𝟙 X) (TopCat.mapsTo_id_compl Set.inter_subset_right))).f (p + 1)
          (((TopPair.ofSubset (K ∩ N)ᶜ).singularCochainComplex R k M).iCycles (p + 1) ζ) ∧
      (TopPair.singularCochainComplexMap
          (TopPair.ofSubsetMap (𝟙 X) (TopCat.mapsTo_id_compl Set.subset_union_left))).f p u -
        (TopPair.singularCochainComplexMap
          (TopPair.ofSubsetMap (𝟙 X) (TopCat.mapsTo_id_compl Set.subset_union_right))).f p v =
        ((TopPair.ofSubset (K ∪ N)ᶜ).singularCochainComplex R k M).iCycles p α ∧
      ((TopPair.ofSubset (K ∪ N)ᶜ).singularCochainComplex R k M).homologyπ p α = a := by
  obtain ⟨x, α, hx, ha, hα⟩ := exists_complMayerVietoris_cochains R k M hK hN p a ζ hζ
  obtain ⟨u, v, hu, hv, huv⟩ := HomologicalComplex.moduleCat_exists_components_of_biprod_lift
    (SSetPair.cochainComplexMap _) (SSetPair.cochainComplexMap _)
    (TopPair.singularCochainComplexMap _) (TopPair.singularCochainComplexMap _)
    p x _ _ hx ha
  let iK := TopPair.singularCochainComplexMap
    (R := R) (k := k) (M := M) (TopCat.univComplPairIso K).inv
  let iN := TopPair.singularCochainComplexMap
    (R := R) (k := k) (M := M) (TopCat.univComplPairIso N).inv
  let iU := TopPair.singularCochainComplexMap
    (R := R) (k := k) (M := M) (TopCat.interComplPairIso K N).inv
  refine ⟨iK.f p u, iN.f p v, cyclesMap iU p α, ?_, ?_, ?_, ?_⟩
  · rw [HomologicalComplex.Hom.comm_apply, hu, moduleCat_iCycles_cyclesMap_apply]
    have hs := ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f.f (p + 1)) (complement_cochain_square
        R k M K N K 0 (by simp) Set.inter_subset_left))
      (((TopPair.ofSubset (K ∩ N)ᶜ).singularCochainComplex R k M).iCycles (p + 1) ζ)
    simpa only [HomologicalComplex.comp_f, ConcreteCategory.comp_apply] using hs
  · rw [HomologicalComplex.Hom.comm_apply, hv, moduleCat_iCycles_cyclesMap_apply]
    have hs := ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f.f (p + 1)) (complement_cochain_square
        R k M K N N 1 (by simp) Set.inter_subset_right))
      (((TopPair.ofSubset (K ∩ N)ᶜ).singularCochainComplex R k M).iCycles (p + 1) ζ)
    simpa only [HomologicalComplex.comp_f, ConcreteCategory.comp_apply] using hs
  · rw [moduleCat_iCycles_cyclesMap_apply, ← huv, map_sub]
    have hk := ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f.f p) (complement_inter_cochain_square
        R k M K N K Set.subset_union_left)) u
    have hn := ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f.f p) (complement_inter_cochain_square
        R k M K N N Set.subset_union_right)) v
    simp only [HomologicalComplex.comp_f, ConcreteCategory.comp_apply] at hk hn
    rw [hk, hn]
  · rw [← moduleCat_homologyMap_homologyπ, hα]
    -- The native cochain functor reverses the same original pair isomorphism.
    change TopPair.singularCohomologyMap (TopCat.interComplPairIso K N).inv p
      (TopPair.singularCohomologyMap (TopCat.interComplPairIso K N).hom p a) = a
    rw [← ConcreteCategory.comp_apply, ← TopPair.singularCohomologyMap_comp,
      Iso.inv_hom_id, TopPair.singularCohomologyMap_id, ConcreteCategory.id_apply]

end TopCat

end
