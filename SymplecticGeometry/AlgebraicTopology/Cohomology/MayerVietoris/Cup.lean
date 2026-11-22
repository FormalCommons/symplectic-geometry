/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.Cup
public import SymplecticGeometry.AlgebraicTopology.Cohomology.MayerVietoris.Pair

/-!
# The absolute Mayer–Vietoris connecting morphism and cup products

Let `U` and `V` be open subsets of a space `X` with `U ∪ V = X`. For `a ∈ Hᵖ(U ∩ V)` and
`b ∈ H^q(X)`, the connecting morphism of the Mayer–Vietoris sequence of the cover `{U, V}` sends
`a ⌣ b|_{U ∩ V}` to `δ a ⌣ b` (`TopCat.singularCohomologyMayerVietorisδ_singularCup`). It is
deduced from the corresponding statement for two pairs,
`TopCat.singularCohomologyPairMayerVietorisδ_singularCup`, applied to `(U, ∅)` and `(V, ∅)`,
through `TopCat.singularCohomologyPairMayerVietorisδ_comp_singularCohomologyπ`.

This theorem is from Tau Ceti's main branch
(`TauCeti/AlgebraicTopology/Cohomology/MayerVietoris/Cup.lean`, same name), as of the commit
`ee1e8aa575ea963edb293ab50d8dc372809e6abb`, not yet in the pinned release.
It is stated here under its Tau Ceti name and namespace, so that moving Tau Ceti past it deletes
this file without renames.
This file is a part of that file, with only these declarations. Its proof uses two
steps of its own, private as there.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1 (the Mayer–Vietoris sequences in cohomology), Section 3.2 (cup products) and
  Section 4.D (the Leray–Hirsch theorem).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, proof of Theorem 10.4.
-/


public section

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex
open TauCeti.ChainComplex (cupCochain cupCycles iCycles_cupCycles d_comp_cupCochain
  iCycles_cyclesMap_linearYonedaFunctor_map_apply d_comp_linearYonedaObj_iCycles)

universe w v u

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {R S T M N L : C}


namespace TopCat

attribute [local instance] TopPair.mono_toSSetPair_map_ofInclusionMap_inclusion_right

/-! ### The connecting morphism and the cup product -/

variable (k : Type*) [CommRing k] [Linear k C] [MonoidalLinear k C] {X : TopCat.{w}}
  {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
  {A B : Set X} (hAU : A ⊆ U) (hBV : B ⊆ V)
  (hA : IsOpen ((↑) ⁻¹' A : Set ↥(A ∪ B))) (hB : IsOpen ((↑) ⁻¹' B : Set ↥(A ∪ B)))


/-! ### The absolute connecting morphism and the cup product -/

private instance isEmpty_snd_ofInclusion_empty_union :
    IsEmpty (TopPair.ofInclusion (Set.union_subset_union (Set.empty_subset U)
      (Set.empty_subset V))).snd :=
  ⟨fun x ↦ by simpa using x.property⟩

omit [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C] in
include hUV in
/-- For `U ∪ V = X`, restriction from `X` to `U ∪ V` is injective on cohomology. -/
private lemma singularCohomologyMap_subtypeVal_union_injective {R M : C} (n : ℕ) :
    Function.Injective (TopCat.singularCohomologyMap (R := R) (k := k) (M := M)
      (ofHom (ContinuousMap.subtypeVal (U ∪ V))) n) := by
  let σ : X ⟶ of ↥(U ∪ V) := ofHom ⟨fun x ↦ ⟨x, hUV ▸ Set.mem_univ x⟩, by fun_prop⟩
  have hσ : σ ≫ ofHom (ContinuousMap.subtypeVal (U ∪ V)) = 𝟙 X := rfl
  refine Function.LeftInverse.injective (g := TopCat.singularCohomologyMap σ n) fun x ↦ ?_
  rw [← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, hσ,
    TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply]

/-- **The Mayer–Vietoris connecting morphism and the cup product.** Let `U` and `V` be open
subsets covering `X`. For `a ∈ Hᵖ(U ∩ V)` and `b ∈ H^q(X)`, the connecting morphism of the
Mayer–Vietoris sequence of the cover `{U, V}` sends `a ⌣ b|_{U ∩ V}` to `δ a ⌣ b`. -/
theorem singularCohomologyMayerVietorisδ_singularCup (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ L)
    {p q n p' m : ℕ} (h : p + q = n) (hp : p + 1 = p') (hm : n + 1 = m) (h' : p' + q = m)
    (a : (of ↥(U ∩ V)).singularCohomology R k M p) (b : X.singularCohomology S k N q) :
    singularCohomologyMayerVietorisδ T k L hU hV hUV n m hm
        ((of ↥(U ∩ V)).singularCup k u μ p q n h a
          (TopCat.singularCohomologyMap (ofHom (ContinuousMap.subtypeVal (U ∩ V))) q b)) =
      X.singularCup k u μ p' q m h'
        (singularCohomologyMayerVietorisδ R k M hU hV hUV p p' hp a) b := by
  -- Work with the pairs `(U, ∅)` and `(V, ∅)`, whose relative cohomology is absolute cohomology.
  have hAU : (∅ : Set X) ⊆ U := Set.empty_subset U
  have hBV : (∅ : Set X) ⊆ V := Set.empty_subset V
  let j : of ↥(U ∪ V) ⟶ X := ofHom (ContinuousMap.subtypeVal (U ∪ V))
  let πU := (TopPair.ofInclusion (Set.union_subset_union hAU hBV)).singularCohomologyπ S k N q
  let ι := interToUnionMap hAU hBV
  -- The class `b` restricted to `U ∪ V`, as a class of the pair `(U ∪ V, ∅)`.
  let b' := inv πU (TopCat.singularCohomologyMap j q b)
  have hb' : πU b' = TopCat.singularCohomologyMap j q b := IsIso.inv_hom_id_apply πU _
  have hfst : TopPair.Hom.fst ι ≫ j = ofHom (ContinuousMap.subtypeVal (U ∩ V)) := by
    ext x
    exact congrArg Subtype.val (TopPair.ofInclusionMap_fst_apply _ _ x)
  -- Its restriction to `(U ∩ V, ∅)` maps to the restriction of `b` to `U ∩ V`.
  have hι : (TopPair.ofInclusion (Set.inter_subset_inter hAU hBV)).singularCohomologyπ S k N q
      (TopPair.singularCohomologyMap ι q b') =
      TopCat.singularCohomologyMap (ofHom (ContinuousMap.subtypeVal (U ∩ V))) q b := by
    rw [← ConcreteCategory.comp_apply, ← TopPair.singularCohomologyπ_naturality,
      ConcreteCategory.comp_apply, hb']
    -- The domain of `TopPair.Hom.fst ι` is `U ∪ V` only after unfolding `TopPair.ofInclusion`, so
    -- the composite with `j` is formed by `singularCohomologyMap_comp` rather than by `rw`.
    exact (ConcreteCategory.comp_apply _ _ _).symm.trans (ConcreteCategory.congr_hom
      ((TopCat.singularCohomologyMap_comp _ j q).symm.trans
        (congrArg (TopCat.singularCohomologyMap · q) hfst)) b)
  apply singularCohomologyMap_subtypeVal_union_injective k hUV
  -- Both sides are the images of the two sides of the corresponding identity for the pairs.
  have hpair := singularCohomologyPairMayerVietorisδ_singularCup (A := ∅) (B := ∅) k hU hV hUV
    hAU hBV
    (by simp) (by simp) u μ h hp hm h' a b'
  have hcomp := ConcreteCategory.congr_hom
    (singularCohomologyPairMayerVietorisδ_comp_singularCohomologyπ T k L hAU hBV
      (by simp) (by simp) hU hV hUV n m hm)
    ((TopPair.ofInclusion (Set.inter_subset_inter hAU hBV)).singularCup k u μ p q n h a
      (TopPair.singularCohomologyMap ι q b'))
  -- The steps below rewrite by `hι`, pass to the pairs, apply `hpair` and return to absolute
  -- classes. The absolute cup products live on `U ∩ V` and `U ∪ V`, while the lemmas relating them
  -- to the pairs are stated on `TopPair.fst` of the pairs, which agree only after unfolding
  -- `TopPair.ofInclusion`; so `rw` cannot match them and each step is an explicit `Eq.trans`.
  refine (congrArg (fun z ↦ TopCat.singularCohomologyMap j m
    (singularCohomologyMayerVietorisδ T k L hU hV hUV n m hm
      ((of ↥(U ∩ V)).singularCup k u μ p q n h a z))) hι.symm).trans ?_
  refine (congrArg (fun z ↦ TopCat.singularCohomologyMap j m
    (singularCohomologyMayerVietorisδ T k L hU hV hUV n m hm z))
    (TopPair.singularCohomologyπ_singularCup k
      (TopPair.ofInclusion (Set.inter_subset_inter hAU hBV)) u μ p q n h a
      (TopPair.singularCohomologyMap ι q b')).symm).trans ?_
  refine hcomp.symm.trans ?_
  refine (congrArg _ hpair).trans ?_
  refine (TopPair.singularCohomologyπ_singularCup k
    (TopPair.ofInclusion (Set.union_subset_union hAU hBV)) u μ p' q m h'
    (TopCat.singularCohomologyMap j p' (singularCohomologyMayerVietorisδ R k M hU hV hUV p p' hp a))
    b').trans ?_
  refine (congrArg _ hb').trans ?_
  exact singularCup_naturality j k u μ p' q m h' _ _

end TopCat

end
