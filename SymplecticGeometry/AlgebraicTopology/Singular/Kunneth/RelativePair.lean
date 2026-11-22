/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.Kunneth.Pair
public import TauCeti.AlgebraicTopology.Singular.CrossProduct

/-!
# The homology cross product of two pairs

Let `A ⊆ X` and `B ⊆ Y` be subsets of topological spaces, and write `A × Y` and `X × B` for
their preimages under the projections of `X × Y`. This file defines the **cross product of the
pairs** `(X, A)` and `(Y, B)` in singular homology (`TopCat.singularHomologyCrossRelPair`),

`Hₚ(X, A; R) ⊗ H_q(Y, B; S) ⟶ Hₙ(X × Y, A × Y ∪ X × B; R ⊗ S)`, for `p + q = n`,

as the cross product of the relative chain complexes `C(X, A; R)` and `C(Y, B; S)`, followed by
the map induced on homology by the shuffle map of the product of the pairs
(`TopCat.shufflePair`). The coefficients `R` and `S` are objects of any abelian monoidal category
with the coproducts that the singular chains use, as for Tau Ceti's relative cross product
`TopCat.singularHomologyCrossRel`, which has a pair in the first factor only.

## Main definitions

* `TopCat.singularHomologyCrossRelPair`: the cross product of two pairs in singular homology.

## Main results

* `TopCat.singularHomologyCrossRelPair_naturality`: naturality in maps of pairs on both sides.
* `TopCat.whiskerLeft_singularHomologyπ_comp_singularHomologyCrossRelPair`: on the relative
  cross product `Hₚ(X, A) ⊗ H_q(Y) ⟶ Hₙ(X × Y, A × Y)`, the cross product of the pairs is the
  map of pairs `(X × Y, A × Y) ⟶ (X × Y, A × Y ∪ X × B)` applied after it.
* `TopCat.singularHomologyCross_comp_singularHomologyπ_eq_singularHomologyCrossRelPair`: on
  absolute classes, the cross product of the pairs is the absolute cross product followed by the
  map to relative homology.

The proofs adapt those of `TopCat.singularHomologyCrossRel_naturality` and
`TopCat.singularHomologyCross_comp_singularHomologyπ` (Tau Ceti,
`TauCeti/AlgebraicTopology/Singular/Kunneth/Relative.lean`) from the relative shuffle map
`TopCat.shuffleRel` to the shuffle map of a product of pairs.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.B, the relative cross product `Hₚ(X, A) ⊗ H_q(Y, B) ⟶ Hₙ(X × Y, A × Y ∪ X × B)`.
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
  (p q n : ℕ) (h : p + q = n)
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorLeft (((TopPair.ofSubset A).singularChainComplex R).homology p))]
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorRight (((TopPair.ofSubset B).singularChainComplex S).cycles q))]
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorRight (((TopPair.ofSubset B).singularChainComplex S).X ((ComplexShape.down ℕ).prev q)))]

/-- **The homology cross product of two pairs**
`Hₚ(X, A; R) ⊗ H_q(Y, B; S) ⟶ Hₙ(X × Y, A × Y ∪ X × B; R ⊗ S)` for `p + q = n`, where `A × Y` and
`X × B` are the preimages of `A` and `B` under the projections: the cross product of the chain
complexes `C(X, A; R)` and `C(Y, B; S)` followed by the map induced by the shuffle map of the
product of the pairs. -/
def singularHomologyCrossRelPair :
    (TopPair.ofSubset A).singularHomology R p ⊗ (TopPair.ofSubset B).singularHomology S q ⟶
      (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularHomology (R ⊗ S) n :=
  homologyCross ((TopPair.ofSubset A).singularChainComplex R)
    ((TopPair.ofSubset B).singularChainComplex S) p q n h ≫
      homologyMap (shufflePair X Y A B R S) n

/-- The cross product of two pairs is the cross product of the relative chain complexes followed
by the map induced by the shuffle map of the product of the pairs. -/
theorem singularHomologyCrossRelPair_def :
    singularHomologyCrossRelPair X Y A B R S p q n h =
      homologyCross ((TopPair.ofSubset A).singularChainComplex R)
        ((TopPair.ofSubset B).singularChainComplex S) p q n h ≫
          homologyMap (shufflePair X Y A B R S) n :=
  (rfl)

/-- **Naturality of the cross product of two pairs** in maps of pairs `(X, A) ⟶ (X', A')` and
`(Y, B) ⟶ (Y', B')`: `f_* a × g_* b = (f × g)_* (a × b)`. -/
@[reassoc]
theorem singularHomologyCrossRelPair_naturality {X' Y' : TopCat.{w}} {A' : Set X'} {B' : Set Y'}
    (f : X ⟶ X') (hf : Set.MapsTo f A A') (g : Y ⟶ Y') (hg : Set.MapsTo g B B')
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((TopPair.ofSubset A').singularChainComplex R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset B').singularChainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight
        (((TopPair.ofSubset B').singularChainComplex S).X ((ComplexShape.down ℕ).prev q)))] :
    (TopPair.singularHomologyMap (TopPair.ofSubsetMap f hf) R p ⊗ₘ
        TopPair.singularHomologyMap (TopPair.ofSubsetMap g hg) S q) ≫
          singularHomologyCrossRelPair X' Y' A' B' R S p q n h =
      singularHomologyCrossRelPair X Y A B R S p q n h ≫ TopPair.singularHomologyMap
        (TopPair.ofSubsetMap (f ⊗ₘ g) (mapsTo_tensorHom_preimage_union f g hf hg)) (R ⊗ S) n :=
  -- The relative singular homology maps are by definition the maps induced on the homology of
  -- the relative singular chain complexes, so the algebraic naturality applies; the composites
  -- are reassociated by hand, as in `TopCat.singularHomologyCrossRel_naturality`.
  (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ homologyMap (shufflePair X' Y' A' B' R S) n)
      (homologyCross_naturality (TopPair.singularChainComplexMap (TopPair.ofSubsetMap f hf) R)
        (TopPair.singularChainComplexMap (TopPair.ofSubsetMap g hg) S) p q n h)).trans <|
    (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) ((homologyMap_comp _ _ n).symm.trans
      ((congrArg (homologyMap · n) (shufflePair_naturality X Y A B R S f hf g hg)).trans
        (homologyMap_comp _ _ n)))).trans (Category.assoc _ _ _).symm

/-- **The cross product of two pairs extends the relative cross product.** For
`a ∈ Hₚ(X, A; R)` and `b ∈ H_q(Y; S)`, the relative cross product `a × b ∈ Hₙ(X × Y, A × Y)`,
mapped to `Hₙ(X × Y, A × Y ∪ X × B)`, is the cross product of `a` with the image of `b` in
`H_q(Y, B; S)`. -/
@[reassoc]
theorem whiskerLeft_singularHomologyπ_comp_singularHomologyCrossRelPair
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y).chainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y).chainComplex S).X ((ComplexShape.down ℕ).prev q)))] :
    ((TopPair.ofSubset A).singularHomology R p ◁ (TopPair.ofSubset B).singularHomologyπ S q) ≫
        singularHomologyCrossRelPair X Y A B R S p q n h =
      singularHomologyCrossRel X Y A R S p q n h ≫
        TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 _) fun _ hz ↦ Or.inl hz) (R ⊗ S) n := by
  -- Naturality of the algebraic cross product along `𝟙 ⊗ π`, and the restriction of the shuffle
  -- map of the pairs to `C(X, A; R) ⊗ C(Y; S)`; the singular homology maps are by definition maps
  -- on homology.
  have hn := homologyCross_naturality (L := (toSSet.obj Y).chainComplex S)
    (𝟙 ((TopPair.ofSubset A).singularChainComplex R)) ((TopPair.ofSubset B).singularChainComplexπ S)
    p q n h
  rw [homologyMap_id, id_tensorHom] at hn
  refine (congrArg (_ ≫ ·) (singularHomologyCrossRelPair_def X Y A B R S p q n h)).trans ?_
  exact (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ homologyMap (shufflePair X Y A B R S) n) hn).trans <|
    (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) (homologyMap_comp _ _ n).symm).trans <|
    (congrArg (fun φ ↦ _ ≫ homologyMap φ n)
      (id_tensorHom_singularChainComplexπ_shufflePair X Y A B R S)).trans <|
    (congrArg (_ ≫ ·) (homologyMap_comp _ _ n)).trans <| (Category.assoc _ _ _).symm.trans <|
    congrArg (· ≫ _) (singularHomologyCrossRel_def X Y A R S p q n h).symm

/-- **The cross product of two pairs on absolute classes.** Mapping the cross product `a × b` of
`a ∈ Hₚ(X; R)` and `b ∈ H_q(Y; S)` to the relative homology of `(X × Y, A × Y ∪ X × B)` gives the
cross product of the images of `a` in `Hₚ(X, A; R)` and of `b` in `H_q(Y, B; S)`. -/
@[reassoc]
theorem singularHomologyCross_comp_singularHomologyπ_eq_singularHomologyCrossRelPair
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((toSSet.obj X).chainComplex R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y).chainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y).chainComplex S).X ((ComplexShape.down ℕ).prev q)))] :
    singularHomologyCross X Y R S p q n h ≫
        (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularHomologyπ (R ⊗ S) n =
      ((TopPair.ofSubset A).singularHomologyπ R p ⊗ₘ (TopPair.ofSubset B).singularHomologyπ S q) ≫
        singularHomologyCrossRelPair X Y A B R S p q n h := by
  -- Naturality of the algebraic cross product along `π ⊗ π`, and the defining property of the
  -- shuffle map of the pairs; the singular homology maps are by definition maps on homology.
  have hn := homologyCross_naturality (K := (toSSet.obj X).chainComplex R)
    (L := (toSSet.obj Y).chainComplex S) ((TopPair.ofSubset A).singularChainComplexπ R)
    ((TopPair.ofSubset B).singularChainComplexπ S) p q n h
  refine (congrArg (· ≫ _) (singularHomologyCross_def X Y R S p q n h)).trans ?_
  exact (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) (homologyMap_comp _ _ n).symm).trans <|
    (congrArg (fun φ ↦ _ ≫ homologyMap φ n)
      (singularChainComplexπ_tensorHom_singularChainComplexπ_shufflePair X Y A B R S).symm).trans <|
    (congrArg (_ ≫ ·) (homologyMap_comp _ _ n)).trans <| (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ homologyMap (shufflePair X Y A B R S) n) hn.symm).trans (Category.assoc _ _ _)

end TopCat
