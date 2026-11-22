/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.Kunneth.RelativePair

/-!
# The connecting morphism on the cross product of two pairs

Let `A ⊆ X` and `B ⊆ Y` be subsets of topological spaces, and write `A × Y` and `X × B` for
their preimages under the projections of `X × Y`. This file shows that the cross product of the
pairs `(X, A)` and `(Y, B)` (`TopCat.singularHomologyCrossRelPair`) meets the connecting morphism
of `(Y, B)` with the Koszul sign: for `a ∈ Hₚ(X, A; R)` and `b ∈ H_q(Y, B; S)`, the connecting
morphism of `(X × Y, A × Y ∪ X × B)`, read in `Hₙ'(A × Y ∪ X × B, A × Y)`, sends `a × b` to
`(-1) ^ p` times the image of the relative cross product `a × δ b ∈ Hₙ'(X × B, A × B)` under the
inclusion of pairs `(X × B, A × B) ⟶ (A × Y ∪ X × B, A × Y)` (`TopPair.prodExcisionFst`). This is
the formula `∂(a × b) = ∂a × b + (-1) ^ p a × ∂b` on chains, whose first term vanishes modulo
`A × Y`.

The relative shuffle maps and the shuffle map of the pairs form a morphism from
`C(X, A; R) ⊗ (C(B; S) ⟶ C(Y; S) ⟶ C(Y, B; S))` to the singular chain sequence of the triple
`(X × Y, A × Y ∪ X × B, A × Y)`, so they commute with the connecting morphisms. The connecting
morphism of the tensored sequence is computed by Tau Ceti's
`HomologicalComplex.homologyCross_comp_δ`, and that of the triple is the connecting morphism of
the pair followed by the map to relative homology
(`TauCeti.TopTriple.singularHomologyδ_eq_comp_singularHomologyπ`).

## Main results

* `TopCat.singularHomologyCrossRelPair_comp_singularHomologyδ_comp_singularHomologyπ`: the
  connecting morphism on the cross product of two pairs, in the second factor.

The proof adapts that of `TopCat.singularHomologyCrossRel_comp_singularHomologyδ` (Tau Ceti's main
branch, `TauCeti/AlgebraicTopology/Singular/Kunneth/Relative.lean`, commit `96e3aa29d7`), where the
pair is the first factor, and that of
`TauCeti.homologyCross_comp_homologyMap_cubicalCrossProductRel_comp_cubicalHomologyδ` (Tau Ceti,
`TauCeti/AlgebraicTopology/Singular/Cubical/Kunneth/Relative.lean`), its cubical analogue with the
pair in the second factor. The commutation of the first square adapts Tau Ceti's private
`TopCat.shufflePair_comm₁₂` (`TauCeti/AlgebraicTopology/Singular/Kunneth/Pair.lean`, of which the
library's `Kunneth/Pair.lean` is a copy), which is not visible from this file.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.B, the relative cross product and its boundary formula.
* C. A. Weibel, *An Introduction to Homological Algebra*, Section 3.6.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory HomologicalComplex Limits
  AlgebraicTopology

universe w v u

namespace TopCat

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCoproducts.{w} C]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)]
  (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (R S : C)

/-- The relative shuffle map of `(X, A)` and `B`, followed by the inclusion of pairs
`(X × B, A × B) ⟶ (A × Y ∪ X × B, A × Y)`, and the relative shuffle map of `(X, A)` and `Y`
commute with the maps `C(X, A; R) ⊗ C(B; S) ⟶ C(X, A; R) ⊗ C(Y; S)` and
`C(A × Y ∪ X × B, A × Y) ⟶ C(X × Y, A × Y)`. -/
private theorem shuffleRel_comp_innerToTotal :
    (𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
        (SSet.chainComplexMap (toSSet.map (TopPair.ofSubset B).map) S :
          (toSSet.obj (TopPair.ofSubset B).snd).chainComplex S ⟶ (toSSet.obj Y).chainComplex S)) ≫
        shuffleRel X Y A R S =
      (shuffleRel X (TopPair.ofSubset B).snd A R S ≫
        TopPair.singularChainComplexMap (TopPair.prodExcisionFst A B) (R ⊗ S)) ≫
          TopPair.singularChainComplexMap
            (TauCeti.TopTriple.innerToTotal.app (TopPair.prodUnionTripleFst A B)) (R ⊗ S) := by
  have := (shortExact_tensorRightShortComplex_singularChainComplexShortComplex X
    (TopPair.ofSubset B).snd A R S).epi_g
  refine (cancel_epi ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
      𝟙 ((toSSet.obj (TopPair.ofSubset B).snd).chainComplex S))).1 ?_
  have hfst : TopPair.Hom.fst (TopPair.prodExcisionFst A B ≫
        TauCeti.TopTriple.innerToTotal.app (TopPair.prodUnionTripleFst A B)) =
      𝟙 X ⊗ₘ ((TopPair.ofSubset B).map : (TopPair.ofSubset B).snd ⟶ Y) := by
    rw [TopPair.Hom.fst_comp, TopPair.prodExcisionFst_fst, TauCeti.TopTriple.innerToTotal_app_fst]
    -- both maps send `(x, y)` to `(x, y)`, read in `X × Y`
    ext; rfl
  have hx : ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
        𝟙 ((toSSet.obj (TopPair.ofSubset B).snd).chainComplex S)) ≫
      (𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
        (SSet.chainComplexMap (toSSet.map (TopPair.ofSubset B).map) S :
          (toSSet.obj (TopPair.ofSubset B).snd).chainComplex S ⟶ (toSSet.obj Y).chainComplex S)) =
    (𝟙 ((toSSet.obj X).chainComplex R) ⊗ₘ
        (SSet.chainComplexMap (toSSet.map (TopPair.ofSubset B).map) S :
          (toSSet.obj (TopPair.ofSubset B).snd).chainComplex S ⟶ (toSSet.obj Y).chainComplex S)) ≫
      ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ 𝟙 ((toSSet.obj Y).chainComplex S)) :=
    (mapBifunctorMap_comp _ _ _ _ _ _).symm.trans <|
      (congrArg₂ (fun f g ↦ mapBifunctorMap f g (curriedTensor C) (ComplexShape.down ℕ))
        ((Category.comp_id _).trans (Category.id_comp _).symm)
        ((Category.id_comp _).trans (Category.comp_id _).symm)).trans
          (mapBifunctorMap_comp _ _ _ _ _ _)
  have hs := shuffle_naturality (𝟙 X) ((TopPair.ofSubset B).map : (TopPair.ofSubset B).snd ⟶ Y)
    R S
  simp only [CategoryTheory.Functor.map_id] at hs
  have h₁ := singularChainComplexπ_tensorHom_id_shuffleRel X Y A R S
  have h₂ := singularChainComplexπ_tensorHom_id_shuffleRel X (TopPair.ofSubset B).snd A R S
  have h₃ := TopPair.singularChainComplexπ_pair_naturality (TopPair.prodExcisionFst A B ≫
      TauCeti.TopTriple.innerToTotal.app (TopPair.prodUnionTripleFst A B)) (R ⊗ S)
  rw [hfst, TopPair.singularChainComplexMap_comp] at h₃
  -- Both sides are the shuffle map of `X` and `B`, followed by the map induced by `X × B ⟶ X × Y`
  -- and the projection to the relative chains of `(X × Y, A × Y)`. The chain complexes appear in
  -- several forms that agree only up to unfolding, so the composites are reassociated by hand.
  exact (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) hx).trans <|
    (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) h₁).trans <|
    (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) hs).trans <|
    (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) h₃).trans <|
    (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) h₂.symm).trans <|
    (Category.assoc _ _ _).trans <|
    congrArg (_ ≫ ·) (Category.assoc _ _ _).symm

/-- The morphism from `C(X, A; R) ⊗ (C(B; S) ⟶ C(Y; S) ⟶ C(Y, B; S))` to the singular chain
sequence of the triple `(X × Y, A × Y ∪ X × B, A × Y)` given by the relative shuffle maps, the
first one followed by the inclusion of pairs `(X × B, A × B) ⟶ (A × Y ∪ X × B, A × Y)`, and the
shuffle map of the product of the pairs. -/
private def shufflePairShortComplexMap :
    tensorLeftShortComplex ((TopPair.ofSubset A).singularChainComplex R)
        ((TopPair.ofSubset B).singularChainComplexShortComplex S) ⟶
      (TopPair.prodUnionTripleFst A B).singularChainComplexShortComplex (R ⊗ S) where
  τ₁ := shuffleRel X (TopPair.ofSubset B).snd A R S ≫
    TopPair.singularChainComplexMap (TopPair.prodExcisionFst A B) (R ⊗ S)
  τ₂ := shuffleRel X Y A R S
  τ₃ := shufflePair X Y A B R S
  comm₁₂ := (shuffleRel_comp_innerToTotal X Y A B R S).symm
  comm₂₃ := ((id_tensorHom_singularChainComplexπ_shufflePair X Y A B R S).trans
    (congrArg (fun f ↦ shuffleRel X Y A R S ≫ TopPair.singularChainComplexMap f (R ⊗ S))
      (TauCeti.TopTriple.totalToOuter_app_ofSubset _).symm)).symm

variable (p q n : ℕ) (h : p + q = n)
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorLeft (((TopPair.ofSubset A).singularChainComplex R).homology p))]
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorRight (((TopPair.ofSubset B).singularChainComplex S).cycles q))]
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorRight (((TopPair.ofSubset B).singularChainComplex S).X ((ComplexShape.down ℕ).prev q)))]

/-- **The connecting morphism on the cross product of two pairs, in the second factor.** For
`a ∈ Hₚ(X, A; R)` and `b ∈ H_q(Y, B; S)` with `q' + 1 = q`, the connecting morphism of the pair
`(X × Y, A × Y ∪ X × B)`, followed by the map `Hₙ'(A × Y ∪ X × B) ⟶ Hₙ'(A × Y ∪ X × B, A × Y)`,
sends the cross product `a × b` of the pairs to `(-1) ^ p` times the image of the relative cross
product `a × δ b ∈ Hₙ'(X × B, A × B)` under the inclusion of pairs
`(X × B, A × B) ⟶ (A × Y ∪ X × B, A × Y)`, where `δ b ∈ H_q'(B; S)` is the connecting morphism
of `(Y, B)`. -/
@[reassoc]
theorem singularHomologyCrossRelPair_comp_singularHomologyδ_comp_singularHomologyπ {q' n' : ℕ}
    (hq : q' + 1 = q) (h' : p + q' = n')
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj (TopPair.ofSubset B).snd).chainComplex S).cycles q'))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj (TopPair.ofSubset B).snd).chainComplex S).X
        ((ComplexShape.down ℕ).prev q')))]
    [(tensorLeft (((TopPair.ofSubset A).singularChainComplex R).cycles p)).PreservesEpimorphisms] :
    singularHomologyCrossRelPair X Y A B R S p q n h ≫
        (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularHomologyδ (R ⊗ S) n n'
          (by omega) ≫
          (TauCeti.TopTriple.innerPair.obj (TopPair.prodUnionTripleFst A B)).singularHomologyπ
            (R ⊗ S) n' =
      ((-1 : ℤ) ^ p) • (((TopPair.ofSubset A).singularHomology R p ◁
          (TopPair.ofSubset B).singularHomologyδ S q q' hq) ≫
        singularHomologyCrossRel X (TopPair.ofSubset B).snd A R S p q' n' h' ≫
          TopPair.singularHomologyMap (TopPair.prodExcisionFst A B) (R ⊗ S) n') := by
  have hS := (TopPair.ofSubset B).shortExact_singularChainComplexShortComplex S
  have hKS := shortExact_tensorLeftShortComplex_singularChainComplexShortComplex X Y A B R S
  have hT := (TopPair.prodUnionTripleFst A B).shortExact_singularChainComplexShortComplex (R ⊗ S)
  have hrel : (ComplexShape.down ℕ).Rel q q' := by simp [hq]
  have hδ := HomologySequence.δ_naturality (shufflePairShortComplexMap X Y A B R S) hKS hT n n'
    (by simp; omega)
  -- the instances on the first term of the short exact sequence of `(Y, B)`, which instance
  -- search does not identify with those on the singular chain complex of `B`
  have : PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset B).singularChainComplexShortComplex S).X₁.cycles q')) :=
    ‹PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj (TopPair.ofSubset B).snd).chainComplex S).cycles q'))›
  have : PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset B).singularChainComplexShortComplex S).X₁.X
        ((ComplexShape.down ℕ).prev q'))) :=
    ‹PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj (TopPair.ofSubset B).snd).chainComplex S).X
        ((ComplexShape.down ℕ).prev q')))›
  have hc := homologyCross_comp_δ ((TopPair.ofSubset A).singularChainComplex R) hS hKS hrel h h'
  -- `hδ`, with the components of `shufflePairShortComplexMap` written out
  have key : homologyMap (shufflePair X Y A B R S) n ≫
      hT.δ n n' (by simp; omega) =
        hKS.δ n n' (by simp; omega) ≫ homologyMap (shuffleRel X (TopPair.ofSubset B).snd A R S ≫
          TopPair.singularChainComplexMap (TopPair.prodExcisionFst A B) (R ⊗ S)) n' :=
    hδ.symm
  have e : (homologyCross ((TopPair.ofSubset A).singularChainComplex R)
        ((toSSet.obj (TopPair.ofSubset B).snd).chainComplex S) p q' n' h' ≫
          homologyMap (shuffleRel X (TopPair.ofSubset B).snd A R S ≫
            TopPair.singularChainComplexMap (TopPair.prodExcisionFst A B) (R ⊗ S)) n') =
      singularHomologyCrossRel X (TopPair.ofSubset B).snd A R S p q' n' h' ≫
        TopPair.singularHomologyMap (TopPair.prodExcisionFst A B) (R ⊗ S) n' :=
    (congrArg (_ ≫ ·) (homologyMap_comp _ _ n')).trans <| (Category.assoc _ _ _).symm.trans <|
      congrArg (· ≫ _) (singularHomologyCrossRel_def X _ A R S p q' n' h').symm
  refine (congrArg (_ ≫ ·)
    ((TopPair.prodUnionTripleFst A B).singularHomologyδ_eq_comp_singularHomologyπ (R ⊗ S) n n'
      (by omega)).symm).trans <| (congrArg (_ ≫ ·)
    ((TopPair.prodUnionTripleFst A B).singularHomologyδ_def (R ⊗ S) n n' (by omega))).trans ?_
  -- the objects here are the singular complexes, which agree with the terms of the short exact
  -- sequences only up to unfolding, so the composites are reassociated by hand
  refine (congrArg (· ≫ _) (singularHomologyCrossRelPair_def X Y A B R S p q n h)).trans <|
    (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) key).trans <|
    (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) hc).trans <|
    (Preadditive.zsmul_comp _ _ _).trans ?_
  rw [ComplexShape.ε_down_ℕ]
  push_cast
  exact congrArg (_ • ·) ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) e))

end TopCat
