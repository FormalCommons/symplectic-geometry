/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.Pair
public import SymplecticGeometry.AlgebraicTopology.Cohomology.MayerVietoris.Basic
public import SymplecticGeometry.AlgebraicTopology.Cohomology.Relative

/-!
# The Mayer–Vietoris connecting morphism of two pairs and the absolute one

The maps from relative to absolute cohomology carry the Mayer–Vietoris connecting morphism of two
pairs to the absolute one:

* `SSetPair.mayerVietorisCochainδ_comp_homologyMap_cochainComplexπ`: for a square of pairs of
  simplicial sets whose squares of subobjects and of ambient simplicial sets are pushouts, the
  maps induced by `SSetPair.cochainComplexπ` carry the relative cochain connecting morphism to
  the one of the square of ambient simplicial sets.
* `TopCat.singularCohomologyPairMayerVietorisδ_comp_singularCohomologyπ`: for an open cover of
  `X` by `A` and `B` and subsets `C ⊆ A`, `D ⊆ B` open in `C ∪ D`, the maps
  `Hⁿ(-, -) ⟶ Hⁿ(-)` carry the connecting morphism of the pairs `(A, C)` and `(B, D)` to the
  connecting morphism of the cover `{A, B}`, followed by the restriction to `A ∪ B`.

These two lemmas are from Tau Ceti's main branch
(`TauCeti/AlgebraicTopology/Cohomology/MayerVietoris/Pair.lean`, same names), as of the commit
`ee1e8aa575ea963edb293ab50d8dc372809e6abb`, not yet in the pinned release.
They are stated here under their Tau Ceti names and namespaces, so that moving Tau Ceti past them
deletes this file without renames. This file is a part of that file, with only these
declarations. Their proofs use `SSetPair.cochainComplexπ` and
`SSet.mayerVietorisCochainδ_congr`, taken from the same commit into
`SymplecticGeometry.AlgebraicTopology.Cohomology.Relative` and
`SymplecticGeometry.AlgebraicTopology.Cohomology.MayerVietoris.Basic`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1, the Mayer–Vietoris sequences in cohomology, including the relative ones.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, where the cohomological sequence of two pairs over open sets of a base is
  used to construct the Thom class.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite TauCeti.ChainComplex

attribute [local instance] preservesBinaryBiproduct_of_preservesBiproduct

universe w v u

namespace SSetPair

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] {R : C}
  {k : Type*} [Ring k] [Linear k C] {M : C}

variable (R k M) {P₁ P₂ P₃ P₄ : SSetPair.{w}} {t : P₁ ⟶ P₂} {l : P₁ ⟶ P₃} {r : P₂ ⟶ P₄}
  {b : P₃ ⟶ P₄}

variable (sqL : IsPushout t.left l.left r.left b.left)
  (sqR : IsPushout t.right l.right r.right b.right) [Mono t.right]

/-! ### Relative and absolute connecting morphisms -/

/-- **The relative and absolute cochain Mayer–Vietoris connecting morphisms.** For a square of
pairs of simplicial sets whose squares of subobjects and of ambient simplicial sets are pushouts
with monomorphic top maps, the maps from relative to absolute cohomology induced by the quotient
maps from ambient to relative chains carry the relative connecting morphism `Hⁿ(P₁) ⟶ Hᵐ(P₄)` to
the absolute one of the square of ambient simplicial sets. -/
@[reassoc]
lemma mayerVietorisCochainδ_comp_homologyMap_cochainComplexπ (n m : ℕ) (h : n + 1 = m := by lia) :
    mayerVietorisCochainδ R k M sqL sqR n m h ≫
        HomologicalComplex.homologyMap (cochainComplexπ R k M P₄) m =
      HomologicalComplex.homologyMap (cochainComplexπ R k M P₁) n ≫
        SSet.mayerVietorisCochainδ R k M sqR n m h := by
  let ψ : mayerVietorisCochainShortComplex R k M (MorphismProperty.Arrow.Hom.ext sqL.w sqR.w) ⟶
      SSet.mayerVietorisCochainShortComplex R k M sqR.toCommSq :=
    { τ₁ := cochainComplexπ R k M P₄
      τ₂ := biprod.map (cochainComplexπ R k M P₂) (cochainComplexπ R k M P₃)
      τ₃ := cochainComplexπ R k M P₁
      comm₁₂ := by apply biprod.hom_ext <;> simp [cochainComplexπ_naturality]
      comm₂₃ := by apply biprod.hom_ext' <;> simp [cochainComplexπ_naturality] }
  rw [mayerVietorisCochainδ_def R k M sqL sqR n m h, SSet.mayerVietorisCochainδ_def R k M sqR n m h]
  exact HomologicalComplex.HomologySequence.δ_naturality ψ _ _ n m (by simpa)

end SSetPair

namespace TopCat

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  (k : Type*) [Ring k] [Linear k C] (M : C) {X : TopCat.{w}}

variable {A B C D : Set X} (hCA : C ⊆ A) (hDB : D ⊆ B)

attribute [local instance] TopPair.mono_toSSetPair_map_ofInclusionMap_inclusion_right

variable (hA : IsOpen ((↑) ⁻¹' A : Set ↥(A ∪ B)))
  (hB : IsOpen ((↑) ⁻¹' B : Set ↥(A ∪ B))) (hC : IsOpen ((↑) ⁻¹' C : Set ↥(C ∪ D)))
  (hD : IsOpen ((↑) ⁻¹' D : Set ↥(C ∪ D)))



/-! ### The connecting morphism of two pairs and the absolute one -/

/-- **The connecting morphism of two pairs and the absolute one.** For an open cover of `X` by `A`
and `B` and subsets `C ⊆ A` and `D ⊆ B` open in `C ∪ D`, the maps from relative to absolute
cohomology carry the connecting morphism `Hⁿ(A ∩ B, C ∩ D) ⟶ Hᵐ(A ∪ B, C ∪ D)` of the
Mayer–Vietoris sequence of the pairs `(A, C)` and `(B, D)` to the connecting morphism
`Hⁿ(A ∩ B) ⟶ Hᵐ(X)` of the cover `{A, B}`, followed by the restriction to `A ∪ B`. -/
@[reassoc]
lemma singularCohomologyPairMayerVietorisδ_comp_singularCohomologyπ (hAX : IsOpen A)
    (hBX : IsOpen B) (hAB : A ∪ B = Set.univ) (n m : ℕ) (h : n + 1 = m := by lia) :
    singularCohomologyPairMayerVietorisδ R k M hCA hDB (hAX.preimage continuous_subtypeVal)
        (hBX.preimage continuous_subtypeVal) hC hD n m h ≫
      (TopPair.ofInclusion (Set.union_subset_union hCA hDB)).singularCohomologyπ R k M m =
    (TopPair.ofInclusion (Set.inter_subset_inter hCA hDB)).singularCohomologyπ R k M n ≫
      singularCohomologyMayerVietorisδ R k M hAX hBX hAB n m h ≫
        TopCat.singularCohomologyMap (ofHom (ContinuousMap.subtypeVal (A ∪ B))) m := by
  -- Both sides are compared after restriction to the singular simplices lying in `A` or in `B`,
  -- which is an isomorphism from the cohomology of `A ∪ B`.
  have := quasiIso_cochainComplexMap_smallSingularSubcomplexToUnion R k M A B
    (hAX.preimage continuous_subtypeVal) (hBX.preimage continuous_subtypeVal)
  refine (cancel_mono (HomologicalComplex.homologyMap (SSet.cochainComplexMap (R := R) (k := k)
    (M := M) (smallSingularSubcomplexToUnion A B)) m)).1 ?_
  -- The left side: naturality of the quotient map from ambient to relative chains.
  have hπ : (TopPair.ofInclusion (Set.union_subset_union hCA hDB)).singularCohomologyπ R k M m ≫
      HomologicalComplex.homologyMap (SSet.cochainComplexMap (R := R) (k := k) (M := M)
        (smallSingularSubcomplexToUnion A B)) m =
      HomologicalComplex.homologyMap (SSetPair.cochainComplexMap (R := R) (k := k) (M := M)
          (smallSingularPairToUnion hCA hDB)) m ≫
        HomologicalComplex.homologyMap (SSetPair.cochainComplexπ R k M
          (smallSingularPair hCA hDB)) m := by
    have hc : ((TopPair.ofInclusion
        (Set.union_subset_union hCA hDB)).singularCochainComplexShortComplex R k M).f ≫
        SSet.cochainComplexMap (R := R) (k := k) (M := M)
          (smallSingularSubcomplexToUnion A B) =
        SSetPair.cochainComplexMap (R := R) (k := k) (M := M) (smallSingularPairToUnion hCA hDB) ≫
          SSetPair.cochainComplexπ R k M (smallSingularPair hCA hDB) := by
      rw [TopPair.singularCochainComplexShortComplex_f_eq]
      exact SSetPair.cochainComplexπ_naturality R k M (smallSingularPairToUnion hCA hDB)
    exact (HomologicalComplex.homologyMap_comp _ _ m).symm.trans
      ((congrArg (HomologicalComplex.homologyMap · m) hc).trans
        (HomologicalComplex.homologyMap_comp _ _ m))
  -- The right side: restricting from `X` to `A ∪ B` and then to the small simplices is restricting
  -- from `X` to the small simplices.
  have hres : TopCat.singularCohomologyMap (R := R) (k := k) (M := M)
      (ofHom (ContinuousMap.subtypeVal (A ∪ B))) m ≫
      HomologicalComplex.homologyMap (SSet.cochainComplexMap (R := R) (k := k) (M := M)
        (smallSingularSubcomplexToUnion A B)) m =
      HomologicalComplex.homologyMap
        (SSet.cochainComplexMap (X.smallSingularSubcomplex ![A, B]).ι) m := by
    rw [TopCat.singularCohomologyMap, ← HomologicalComplex.homologyMap_comp,
      ← SSet.cochainComplexMap_comp, smallSingularSubcomplexToUnion_comp]
  -- The intermediate cohomology objects agree with each other only up to unfolding
  -- `TopPair.ofInclusion` and `TopPair.toSSetPair`, which `rw` and `simp` do not do, so the two
  -- sides are connected by explicit `Eq.trans` steps.
  have h₁ := singularCohomologyPairMayerVietorisδ_comp_homologyMap R k M hCA hDB
    (hAX.preimage continuous_subtypeVal) (hBX.preimage continuous_subtypeVal) hC hD n m h
  have h₂ := SSetPair.mayerVietorisCochainδ_comp_homologyMap_cochainComplexπ R k M
    (isPushout_toSmallSingularPair_left hCA hDB) (isPushout_toSmallSingularPair_right hCA hDB) n m h
  have h₃ : SSet.mayerVietorisCochainδ R k M (isPushout_toSmallSingularPair_right hCA hDB) n m h =
      SSet.mayerVietorisCochainδ R k M (isPushout_toSSet_inter_smallSingularSubcomplex A B) n m h :=
    SSet.mayerVietorisCochainδ_congr R k M (isPushout_toSmallSingularPair_right hCA hDB)
      (isPushout_toSSet_inter_smallSingularSubcomplex A B)
      (TopPair.toSSetPair_map_ofInclusionMap_inclusion_right _ _ _ _)
      (TopPair.toSSetPair_map_ofInclusionMap_inclusion_right _ _ _ _) rfl rfl n m h
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) hπ).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) h₁).trans ?_
  refine h₂.trans ?_
  refine (congrArg (_ ≫ ·) h₃).trans ?_
  refine (congrArg (_ ≫ ·)
    (singularCohomologyMayerVietorisδ_comp_homologyMap R k M hAX hBX hAB n m h).symm).trans ?_
  refine (congrArg (fun φ ↦ _ ≫ _ ≫ φ) hres.symm).trans ?_
  simp only [Category.assoc]
  -- `TopPair.singularCohomologyπ` is by definition the map induced by `SSetPair.cochainComplexπ`
  -- of the pair of simplicial sets of `(A ∩ B, C ∩ D)`.
  rfl

end TopCat

end
