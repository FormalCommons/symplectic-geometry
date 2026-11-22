/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.Kunneth.Pair
public import TauCeti.AlgebraicTopology.Singular.CrossProduct
public import TauCeti.Algebra.Homology.Homotopy
public import TauCeti.AlgebraicTopology.SimplicialSet.EilenbergZilber
public import TauCeti.AlgebraicTopology.Singular.AlexanderWhitney.RelativeCup

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

The shuffle map of the pairs factors through the small chains `C(X × Y; A × Y + X × B; R ⊗ S)` of
`X × Y`, relative to its singular simplices lying in `A × Y` or in `X × B`
(`TopCat.shuffleSmallPair`, and `TopCat.shuffleSmallPair_comp_smallSingularSubcomplexPairToUnion`).
There the relative Alexander–Whitney diagonal applies, and its composite with the small shuffle
map, `TopCat.shuffleAlexanderWhitneyPair`, is chain homotopic to the identity of
`C(X, A; R) ⊗ C(Y, B; S)` (`TopCat.shuffleAlexanderWhitneyPairHomotopy`): this is the relative
form of the Eilenberg–Zilber homotopy `SSet.shuffleAlexanderWhitneyHomotopy`, which is natural, so
it descends along the two quotient maps (`Homotopy.descCokernel`).

## Main definitions

* `TopCat.singularHomologyCrossRelPair`: the cross product of two pairs in singular homology.
* `TopCat.shuffleSmallPair`: the shuffle map of the pairs into the small chains.
* `TopCat.shuffleAlexanderWhitneyPair`: the relative Alexander–Whitney map of the pairs after
  `TopCat.shuffleSmallPair`, an endomorphism of `C(X, A; R) ⊗ C(Y, B; S)`.
* `TopCat.shuffleAlexanderWhitneyPairHomotopy`: the homotopy from it to the identity.

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

The two-step descent of the shuffle map to the small chains follows the construction of
`TopCat.shufflePair` (`SymplecticGeometry/AlgebraicTopology/Singular/Kunneth/Pair.lean`, from Tau
Ceti), whose two private identities between the projections of tensor products are restated here
as `TopCat.singularChainComplexπ_tensorHom_singularChainComplexπ_eq_comp` and
`TopCat.singularChainComplexπ_tensorHom_id_comp_id_tensorHom_chainComplexMap`.
`TopCat.alexanderWhitneyDiagonal_comp_tensorHom_fst_snd` is a step of the proof of
`TauCeti.singularCross_eq_singularCup` (Tau Ceti, `Cohomology/CrossProduct.lean`), and the
descent of the homotopy adapts the use of `SSet.shuffleAlexanderWhitneyHomotopy` in
`TauCeti.singularEilenbergZilberCohomologyIso_hom_singularCross` (same file) to relative chains.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.B, the relative cross product `Hₚ(X, A) ⊗ H_q(Y, B) ⟶ Hₙ(X × Y, A × Y ∪ X × B)`.
* S. Eilenberg and J. A. Zilber, *On products of complexes*, Amer. J. Math. 75 (1953).
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory HomologicalComplex Limits
  AlgebraicTopology

universe w v u

namespace TopCat

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

section Small

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

/-- A continuous map into `X` whose image lies in a member of a family `U` of subsets induces a
chain map that vanishes in the chains of `X` relative to its singular simplices lying in some
member of `U`. -/
theorem chainComplexMap_comp_chainComplexπ_smallSingularSubcomplex {X Z : TopCat.{w}}
    {ι : Type*} (U : ι → Set X) {f : Z ⟶ X} {i : ι} (hf : Set.range f ⊆ U i) (R : C) :
    SSet.chainComplexMap (toSSet.map f) R ≫
      (X.smallSingularSubcomplex U).pair.chainComplexπ R = 0 := by
  have hfac : f = ofHom ⟨Set.codRestrict f (U i) fun z ↦ hf ⟨z, rfl⟩, by fun_prop⟩ ≫
      ofHom (ContinuousMap.subtypeVal (U i)) := TopCat.ext fun _ ↦ rfl
  rw [hfac, Functor.map_comp, ← toSmallSingularSubcomplex_ι U (subset_refl (U i)),
    SSet.chainComplexMap, Functor.map_comp, Functor.map_comp]
  exact (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) ((X.smallSingularSubcomplex U).pair.chainComplex_condition R)).trans
      comp_zero))).trans comp_zero

end Small

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCoproducts.{w} C]

section AlexanderWhitney

variable (X Y : TopCat.{w}) (R S : C)

/-- The Alexander–Whitney diagonal of `X × Y`, followed by the chain maps of the two projections,
is the Alexander–Whitney map of `X` and `Y`. -/
theorem alexanderWhitneyDiagonal_comp_tensorHom_fst_snd :
    (X ⊗ Y).alexanderWhitneyDiagonal (𝟙 (R ⊗ S)) ≫
        (SSet.chainComplexMap (toSSet.map (fst X Y)) R ⊗ₘ
          SSet.chainComplexMap (toSSet.map (snd X Y)) S) =
      alexanderWhitney X Y R S := by
  have hdiag : lift (𝟙 (X ⊗ Y)) (𝟙 (X ⊗ Y)) ≫ (fst X Y ⊗ₘ snd X Y) = 𝟙 (X ⊗ Y) := by
    ext <;> simp
  rw [TauCeti.alexanderWhitneyDiagonal_def, (SSet.chainComplexFunctor C).map_id]
  simp only [NatTrans.id_app, Category.id_comp, Category.assoc]
  rw [← alexanderWhitney_naturality, ← Category.assoc, SSet.chainComplexMap, SSet.chainComplexMap,
    ← Functor.map_comp, ← Functor.map_comp, hdiag, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

end AlexanderWhitney

section Projections

variable (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (R S : C)

/-- The projection `C(X; R) ⊗ C(Y; S) ⟶ C(X, A; R) ⊗ C(Y, B; S)` is the projection in the first
variable followed by the projection in the second. -/
theorem singularChainComplexπ_tensorHom_singularChainComplexπ_eq_comp :
    (TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ (TopPair.ofSubset B).singularChainComplexπ S =
      ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ 𝟙 ((toSSet.obj Y).chainComplex S)) ≫
        (𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
          (TopPair.ofSubset B).singularChainComplexπ S) :=
  (congrArg₂ (· ⊗ₘ ·) (Category.comp_id _).symm (Category.id_comp _).symm).trans
    (mapBifunctorMap_comp _ _ _ _ _ _)

/-- The projection `C(X; R) ⟶ C(X, A; R)` and the inclusion `C(B; S) ⟶ C(Y; S)`, tensored in the
two variables, commute. -/
theorem singularChainComplexπ_tensorHom_id_comp_id_tensorHom_chainComplexMap :
    ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
        𝟙 ((toSSet.obj (TopPair.ofSubset B).snd).chainComplex S)) ≫
      (𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
        SSet.chainComplexMap (toSSet.map (TopPair.ofSubset B).map) S) =
      (𝟙 ((toSSet.obj X).chainComplex R) ⊗ₘ
        SSet.chainComplexMap (toSSet.map (TopPair.ofSubset B).map) S) ≫
      ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ 𝟙 ((toSSet.obj Y).chainComplex S)) :=
  ((mapBifunctorMap_comp _ _ _ _ _ _).symm.trans
    (congrArg₂ (mapBifunctorMap · · (curriedTensor C) (ComplexShape.down ℕ))
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((Category.id_comp _).trans (Category.comp_id _).symm))).trans
    (mapBifunctorMap_comp _ _ _ _ _ _)

end Projections

variable [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)]

section CrossRelPair

variable (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (R S : C)
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

end CrossRelPair

section ShuffleSmall

variable (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (R S : C)

/-- The shuffle map carries `C(A; R) ⊗ C(Y; S)` into the small chains of `A × Y`. -/
private theorem shuffle_cokernel_condition_small_fst :
    (SSet.chainComplexMap (toSSet.map (TopPair.ofSubset A).map) R ⊗ₘ
        𝟙 ((toSSet.obj Y).chainComplex S)) ≫ shuffle X Y R S ≫
      ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ
        (R ⊗ S) = 0 := by
  have h := shuffle_naturality (TopPair.ofSubset A).map (𝟙 Y) R S
  simp only [CategoryTheory.Functor.map_id] at h
  -- Term-mode steps here and below: the singular chains of a space appear both as
  -- `(toSSet.obj X).chainComplex R` and as the ambient chains of a pair, which agree only up to
  -- unfolding `TopPair.ofSubset`, so `rw [Category.assoc]` does not apply.
  exact (Category.assoc _ _ _).symm.trans <| (h =≫ _).trans <| (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) (chainComplexMap_comp_chainComplexπ_smallSingularSubcomplex _
      (i := 0) (by rintro _ ⟨z, rfl⟩; exact z.1.property) (R ⊗ S))).trans comp_zero

/-- The shuffle map `C(X, A; R) ⊗ C(Y; S) ⟶ C(X × Y; A × Y + X × B; R ⊗ S)` into the small chains,
induced by the shuffle map. -/
def shuffleSmallPairFst :
    (TopPair.ofSubset A).singularChainComplex R ⊗ (toSSet.obj Y).chainComplex S ⟶
      ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplex
        (R ⊗ S) :=
  have hS := shortExact_tensorRightShortComplex_singularChainComplexShortComplex X Y A R S
  have := hS.epi_g
  hS.exact.gIsCokernel.desc
    (CokernelCofork.ofπ _ (shuffle_cokernel_condition_small_fst X Y A B R S))

/-- On `C(X; R) ⊗ C(Y; S)`, the map `shuffleSmallPairFst` is the shuffle map followed by the
projection to the small chains. -/
theorem singularChainComplexπ_tensorHom_id_shuffleSmallPairFst :
    ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ 𝟙 ((toSSet.obj Y).chainComplex S)) ≫
        shuffleSmallPairFst X Y A B R S =
      shuffle X Y R S ≫
        ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ
          (R ⊗ S) :=
  have hS := shortExact_tensorRightShortComplex_singularChainComplexShortComplex X Y A R S
  have := hS.epi_g
  hS.exact.gIsCokernel.fac _ WalkingParallelPair.one

/-- The shuffle map carries `C(X; R) ⊗ C(B; S)` into the small chains of `X × B`. -/
private theorem shuffle_cokernel_condition_small_snd :
    (𝟙 ((toSSet.obj X).chainComplex R) ⊗ₘ
        SSet.chainComplexMap (toSSet.map (TopPair.ofSubset B).map) S) ≫ shuffle X Y R S ≫
      ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ
        (R ⊗ S) = 0 := by
  have h := shuffle_naturality (𝟙 X) (TopPair.ofSubset B).map R S
  simp only [CategoryTheory.Functor.map_id] at h
  exact (Category.assoc _ _ _).symm.trans <| (h =≫ _).trans <| (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) (chainComplexMap_comp_chainComplexπ_smallSingularSubcomplex _
      (i := 1) (by rintro _ ⟨z, rfl⟩; exact z.2.property) (R ⊗ S))).trans comp_zero

/-- The small-chain shuffle map of `(X, A)` and `Y` vanishes on `C(X, A; R) ⊗ C(B; S)`. -/
private theorem shuffleSmallPairFst_cokernel_condition :
    (𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
        SSet.chainComplexMap (toSSet.map (TopPair.ofSubset B).map) S) ≫
      shuffleSmallPairFst X Y A B R S = 0 := by
  have := (shortExact_tensorRightShortComplex_singularChainComplexShortComplex X
    (TopPair.ofSubset B).snd A R S).epi_g
  refine (cancel_epi ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
      𝟙 ((toSSet.obj (TopPair.ofSubset B).snd).chainComplex S))).1 ?_
  exact (Category.assoc _ _ _).symm.trans <|
    ((singularChainComplexπ_tensorHom_id_comp_id_tensorHom_chainComplexMap
    X Y A B R S) =≫ _).trans <| (Category.assoc _ _ _).trans <|
    ((congrArg (_ ≫ ·) (singularChainComplexπ_tensorHom_id_shuffleSmallPairFst X Y A B R S)).trans
      (shuffle_cokernel_condition_small_snd X Y A B R S)).trans comp_zero.symm

/-- **The shuffle map into the small chains** `C(X, A; R) ⊗ C(Y, B; S) ⟶ C(X × Y; A × Y + X × B)`,
induced by the shuffle map; followed by the map to `C(X × Y, A × Y ∪ X × B)` it is
`TopCat.shufflePair`. -/
def shuffleSmallPair :
    (TopPair.ofSubset A).singularChainComplex R ⊗ (TopPair.ofSubset B).singularChainComplex S ⟶
      ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplex
        (R ⊗ S) :=
  have hS := shortExact_tensorLeftShortComplex_singularChainComplexShortComplex X Y A B R S
  have := hS.epi_g
  hS.exact.gIsCokernel.desc
    (CokernelCofork.ofπ _ (shuffleSmallPairFst_cokernel_condition X Y A B R S))

/-- On `C(X, A; R) ⊗ C(Y; S)`, the small-chain shuffle map of the pairs is
`shuffleSmallPairFst`. -/
theorem id_tensorHom_singularChainComplexπ_shuffleSmallPair :
    (𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
        (TopPair.ofSubset B).singularChainComplexπ S) ≫ shuffleSmallPair X Y A B R S =
      shuffleSmallPairFst X Y A B R S :=
  have hS := shortExact_tensorLeftShortComplex_singularChainComplexShortComplex X Y A B R S
  have := hS.epi_g
  hS.exact.gIsCokernel.fac _ WalkingParallelPair.one

/-- On `C(X; R) ⊗ C(Y; S)`, the small-chain shuffle map of the pairs is the shuffle map followed by
the projection to the small chains. -/
theorem singularChainComplexπ_tensorHom_singularChainComplexπ_shuffleSmallPair :
    ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
        (TopPair.ofSubset B).singularChainComplexπ S) ≫ shuffleSmallPair X Y A B R S =
      shuffle X Y R S ≫
        ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ
          (R ⊗ S) :=
  (congrArg (· ≫ shuffleSmallPair X Y A B R S)
    (singularChainComplexπ_tensorHom_singularChainComplexπ_eq_comp X Y A B R S)).trans <|
    (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) (id_tensorHom_singularChainComplexπ_shuffleSmallPair X Y A B R S)).trans
        (singularChainComplexπ_tensorHom_id_shuffleSmallPairFst X Y A B R S)

/-- The small-chain shuffle map followed by the map to the relative chains of the union is the
shuffle map of the pairs. -/
theorem shuffleSmallPair_comp_smallSingularSubcomplexPairToUnion :
    shuffleSmallPair X Y A B R S ≫ SSetPair.chainComplexMap
        (smallSingularSubcomplexPairToUnion (fst X Y ⁻¹' A) (snd X Y ⁻¹' B)) (R ⊗ S) =
      shufflePair X Y A B R S := by
  have := epi_singularChainComplexπ_tensorHom_singularChainComplexπ X Y A B R S
  refine (cancel_epi ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
      (TopPair.ofSubset B).singularChainComplexπ S)).1 ?_
  exact (Category.assoc _ _ _).symm.trans <|
    ((singularChainComplexπ_tensorHom_singularChainComplexπ_shuffleSmallPair
      X Y A B R S) =≫ _).trans <|
      (Category.assoc _ _ _).trans <|
        (congrArg (_ ≫ ·) (chainComplexπ_smallSingularSubcomplexPairToUnion _ _ _)).trans
          (singularChainComplexπ_tensorHom_singularChainComplexπ_shufflePair X Y A B R S).symm

end ShuffleSmall

section Homotopy

variable (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (R S : C)

/-- The composite of the shuffle and Alexander–Whitney maps, descended to `C(X, A; R) ⊗ C(Y; S)`. -/
def shuffleAlexanderWhitneyPairFst :
    (TopPair.ofSubset A).singularChainComplex R ⊗ (toSSet.obj Y).chainComplex S ⟶
      (TopPair.ofSubset A).singularChainComplex R ⊗ (toSSet.obj Y).chainComplex S :=
  have hS := shortExact_tensorRightShortComplex_singularChainComplexShortComplex X Y A R S
  have := hS.epi_g
  hS.exact.gIsCokernel.desc (CokernelCofork.ofπ
    (shuffle X Y R S ≫ alexanderWhitney X Y R S ≫
      ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ 𝟙 ((toSSet.obj Y).chainComplex S))) (by
    have h₁ := shuffle_naturality (TopPair.ofSubset A).map (𝟙 Y) R S
    have h₂ := alexanderWhitney_naturality (TopPair.ofSubset A).map (𝟙 Y) R S
    simp only [CategoryTheory.Functor.map_id] at h₁ h₂
    exact (Category.assoc _ _ _).symm.trans <| (h₁ =≫ _).trans <| (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans <| (h₂ =≫ _).trans <|
        (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) (tensorRightShortComplex
          ((toSSet.obj Y).chainComplex S)
          ((TopPair.ofSubset A).singularChainComplexShortComplex R)).zero).trans comp_zero)).trans
        comp_zero))

/-- On `C(X; R) ⊗ C(Y; S)`, the map `shuffleAlexanderWhitneyPairFst` is the shuffle map followed by
the Alexander–Whitney map, projected to `C(X, A; R) ⊗ C(Y; S)`. -/
theorem singularChainComplexπ_tensorHom_id_shuffleAlexanderWhitneyPairFst :
    ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ 𝟙 ((toSSet.obj Y).chainComplex S)) ≫
        shuffleAlexanderWhitneyPairFst X Y A R S =
      shuffle X Y R S ≫ alexanderWhitney X Y R S ≫
        ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ 𝟙 ((toSSet.obj Y).chainComplex S)) :=
  have hS := shortExact_tensorRightShortComplex_singularChainComplexShortComplex X Y A R S
  have := hS.epi_g
  hS.exact.gIsCokernel.fac _ WalkingParallelPair.one

/-- The Eilenberg–Zilber homotopy `AW ∘ shuffle ≃ id`, descended to `C(X, A; R) ⊗ C(Y; S)`: it is
natural, so it preserves `C(A; R) ⊗ C(Y; S)`. -/
def shuffleAlexanderWhitneyPairFstHomotopy :
    _root_.Homotopy (shuffleAlexanderWhitneyPairFst X Y A R S) (𝟙 _) :=
  have hS := shortExact_tensorRightShortComplex_singularChainComplexShortComplex X Y A R S
  _root_.Homotopy.descCokernel
    (SSet.shuffleAlexanderWhitneyHomotopy (toSSet.obj X) (toSSet.obj Y) R S)
    (tensorRightShortComplex ((toSSet.obj Y).chainComplex S)
      ((TopPair.ofSubset A).singularChainComplexShortComplex R)).f
    (tensorRightShortComplex ((toSSet.obj Y).chainComplex S)
      ((TopPair.ofSubset A).singularChainComplexShortComplex R)).g
    (tensorRightShortComplex ((toSSet.obj Y).chainComplex S)
      ((TopPair.ofSubset A).singularChainComplexShortComplex R)).g _
    (fun i ↦ have hSi := hS.map_of_exact (HomologicalComplex.eval C _ i)
      have := hSi.epi_g
      hSi.exact.gIsCokernel)
    (fun i j ↦ by
      have h := SSet.shuffleAlexanderWhitneyHomotopy_hom_naturality R S
        (toSSet.map (TopPair.ofSubset A).map) (𝟙 (toSSet.obj Y)) i j
      simp only [CategoryTheory.Functor.map_id] at h
      exact (Category.assoc _ _ _).symm.trans <| (h =≫ _).trans <| (Category.assoc _ _ _).trans <|
        (congrArg (_ ≫ ·) ((comp_f _ _ j).symm.trans ((congrArg (fun φ ↦ φ.f j)
          (tensorRightShortComplex ((toSSet.obj Y).chainComplex S)
            ((TopPair.ofSubset A).singularChainComplexShortComplex R)).zero).trans
              (zero_f _ _ j)))).trans comp_zero)
    ((singularChainComplexπ_tensorHom_id_shuffleAlexanderWhitneyPairFst X Y A R S).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ _) (shuffle_alexanderWhitney X Y R S))))
    ((Category.comp_id _).trans (Category.id_comp _).symm)

/-- The homotopy `shuffleAlexanderWhitneyPairFstHomotopy` is the Eilenberg–Zilber homotopy of
`Sing X` and `Sing Y`, projected to `C(X, A; R) ⊗ C(Y; S)`. -/
theorem singularChainComplexπ_tensorHom_id_f_shuffleAlexanderWhitneyPairFstHomotopy_hom
    (i j : ℕ) :
    ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ 𝟙 ((toSSet.obj Y).chainComplex S)).f i ≫
        (shuffleAlexanderWhitneyPairFstHomotopy X Y A R S).hom i j =
      (SSet.shuffleAlexanderWhitneyHomotopy (toSSet.obj X) (toSSet.obj Y) R S).hom i j ≫
        ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ 𝟙 ((toSSet.obj Y).chainComplex S)).f j :=
  Homotopy.π_descCokernel_hom _ _ _ _ _ _ _ _ _ i j

/-- The relative Alexander–Whitney map of the two pairs, after the small-chain shuffle map: an
endomorphism of `C(X, A; R) ⊗ C(Y, B; S)`. -/
def shuffleAlexanderWhitneyPair :
    (TopPair.ofSubset A).singularChainComplex R ⊗ (TopPair.ofSubset B).singularChainComplex S ⟶
      (TopPair.ofSubset A).singularChainComplex R ⊗ (TopPair.ofSubset B).singularChainComplex S :=
  shuffleSmallPair X Y A B R S ≫
    relativeAlexanderWhitneyDiagonal (fst X Y ⁻¹' A) (snd X Y ⁻¹' B) (𝟙 (R ⊗ S)) ≫
      (TopPair.singularChainComplexMap
          (TopPair.ofSubsetMap (fst X Y) (Set.mapsTo_preimage _ _)) R ⊗ₘ
        TopPair.singularChainComplexMap
          (TopPair.ofSubsetMap (snd X Y) (Set.mapsTo_preimage _ _)) S)

/-- `shuffleAlexanderWhitneyPair` is the small-chain shuffle map, followed by the relative
Alexander–Whitney diagonal and the chain maps of the two projections. -/
theorem shuffleAlexanderWhitneyPair_def :
    shuffleAlexanderWhitneyPair X Y A B R S =
      shuffleSmallPair X Y A B R S ≫
        relativeAlexanderWhitneyDiagonal (fst X Y ⁻¹' A) (snd X Y ⁻¹' B) (𝟙 (R ⊗ S)) ≫
          (TopPair.singularChainComplexMap
              (TopPair.ofSubsetMap (fst X Y) (Set.mapsTo_preimage _ _)) R ⊗ₘ
            TopPair.singularChainComplexMap
              (TopPair.ofSubsetMap (snd X Y) (Set.mapsTo_preimage _ _)) S) :=
  (rfl)

/-- On `C(X; R) ⊗ C(Y; S)`, the map `shuffleAlexanderWhitneyPair` is the shuffle map followed by the
Alexander–Whitney map, projected to `C(X, A; R) ⊗ C(Y, B; S)`. -/
theorem singularChainComplexπ_tensorHom_singularChainComplexπ_shuffleAlexanderWhitneyPair :
    ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
        (TopPair.ofSubset B).singularChainComplexπ S) ≫ shuffleAlexanderWhitneyPair X Y A B R S =
      shuffle X Y R S ≫ alexanderWhitney X Y R S ≫
        ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
          (TopPair.ofSubset B).singularChainComplexπ S) := by
  have hU := TopPair.singularChainComplexπ_pair_naturality
    (TopPair.ofSubsetMap (fst X Y) (Set.mapsTo_preimage _ A)) R
  have hV := TopPair.singularChainComplexπ_pair_naturality
    (TopPair.ofSubsetMap (snd X Y) (Set.mapsTo_preimage _ B)) S
  rw [TopPair.ofSubsetMap_fst] at hU hV
  have hπ : ((TopPair.ofSubset (fst X Y ⁻¹' A)).singularChainComplexπ R ⊗ₘ
        (TopPair.ofSubset (snd X Y ⁻¹' B)).singularChainComplexπ S) ≫
      (TopPair.singularChainComplexMap
          (TopPair.ofSubsetMap (fst X Y) (Set.mapsTo_preimage _ _)) R ⊗ₘ
        TopPair.singularChainComplexMap
          (TopPair.ofSubsetMap (snd X Y) (Set.mapsTo_preimage _ _)) S) =
      (SSet.chainComplexMap (toSSet.map (fst X Y)) R ⊗ₘ
          SSet.chainComplexMap (toSSet.map (snd X Y)) S) ≫
        ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
          (TopPair.ofSubset B).singularChainComplexπ S) :=
    (mapBifunctorMap_comp _ _ _ _ _ _).symm.trans <|
      (congrArg₂ (mapBifunctorMap · · (curriedTensor C) (ComplexShape.down ℕ)) hU.symm
        hV.symm).trans (mapBifunctorMap_comp _ _ _ _ _ _)
  exact (Category.assoc _ _ _).symm.trans <|
    ((singularChainComplexπ_tensorHom_singularChainComplexπ_shuffleSmallPair
      X Y A B R S) =≫ _).trans <|
      (Category.assoc _ _ _).trans <| congrArg (_ ≫ ·) <|
        (chainComplexπ_relativeAlexanderWhitneyDiagonal_assoc _ _ _ _).trans <|
          (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) hπ).trans <|
            (Category.assoc _ _ _).symm.trans <|
              congrArg (· ≫ _) (alexanderWhitneyDiagonal_comp_tensorHom_fst_snd X Y R S)

/-- On `C(X, A; R) ⊗ C(Y; S)`, the composite `shuffleAlexanderWhitneyPair` of the pairs is the
composite `shuffleAlexanderWhitneyPairFst` of `(X, A)` and `Y`, followed by the projection to
`C(X, A; R) ⊗ C(Y, B; S)`. -/
theorem id_tensorHom_singularChainComplexπ_shuffleAlexanderWhitneyPair :
    (𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
        (TopPair.ofSubset B).singularChainComplexπ S) ≫ shuffleAlexanderWhitneyPair X Y A B R S =
      shuffleAlexanderWhitneyPairFst X Y A R S ≫
        (𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
          (TopPair.ofSubset B).singularChainComplexπ S) := by
  have := (shortExact_tensorRightShortComplex_singularChainComplexShortComplex X Y A R S).epi_g
  refine (cancel_epi ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
    𝟙 ((toSSet.obj Y).chainComplex S))).1 ?_
  exact (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ shuffleAlexanderWhitneyPair X Y A B R S)
      (singularChainComplexπ_tensorHom_singularChainComplexπ_eq_comp X Y A B R S).symm).trans <|
    (singularChainComplexπ_tensorHom_singularChainComplexπ_shuffleAlexanderWhitneyPair
      X Y A B R S).trans <|
    (congrArg (fun t ↦ shuffle X Y R S ≫ alexanderWhitney X Y R S ≫ t)
      (singularChainComplexπ_tensorHom_singularChainComplexπ_eq_comp X Y A B R S)).trans <|
    (congrArg (shuffle X Y R S ≫ ·) (Category.assoc _ _ _).symm).trans <|
    (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _)
      (singularChainComplexπ_tensorHom_id_shuffleAlexanderWhitneyPairFst X Y A R S).symm).trans
        (Category.assoc _ _ _)

/-- The Eilenberg–Zilber homotopy `AW ∘ shuffle ≃ id`, descended to `C(X, A; R) ⊗ C(Y, B; S)`: the
relative Alexander–Whitney map of the pairs after the small-chain shuffle map is homotopic to the
identity. -/
def shuffleAlexanderWhitneyPairHomotopy :
    _root_.Homotopy (shuffleAlexanderWhitneyPair X Y A B R S) (𝟙 _) :=
  have hS₁ := shortExact_tensorRightShortComplex_singularChainComplexShortComplex X Y A R S
  have hS₂ := shortExact_tensorLeftShortComplex_singularChainComplexShortComplex X Y A B R S
  have := hS₁.epi_g
  _root_.Homotopy.descCokernel (shuffleAlexanderWhitneyPairFstHomotopy X Y A R S)
    (tensorLeftShortComplex ((TopPair.ofSubset A).singularChainComplex R)
      ((TopPair.ofSubset B).singularChainComplexShortComplex S)).f
    (tensorLeftShortComplex ((TopPair.ofSubset A).singularChainComplex R)
      ((TopPair.ofSubset B).singularChainComplexShortComplex S)).g
    (tensorLeftShortComplex ((TopPair.ofSubset A).singularChainComplex R)
      ((TopPair.ofSubset B).singularChainComplexShortComplex S)).g _
    (fun i ↦ have hSi := hS₂.map_of_exact (HomologicalComplex.eval C _ i)
      have := hSi.epi_g
      hSi.exact.gIsCokernel)
    (fun i j ↦ by
      -- After the epimorphism `C(X; R) ⊗ C(B; S) ⟶ C(X, A; R) ⊗ C(B; S)`, this is the naturality of
      -- the Eilenberg–Zilber homotopy along the inclusion of `B`.
      have : Epi (((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
          𝟙 ((toSSet.obj (TopPair.ofSubset B).snd).chainComplex S)).f i) :=
        ((shortExact_tensorRightShortComplex_singularChainComplexShortComplex X
          (TopPair.ofSubset B).snd A R S).map_of_exact (HomologicalComplex.eval C _ i)).epi_g
      refine (cancel_epi (((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
        𝟙 ((toSSet.obj (TopPair.ofSubset B).snd).chainComplex S)).f i)).1 ?_
      have e₁ := congrArg (fun φ ↦ φ.f i)
        (singularChainComplexπ_tensorHom_id_comp_id_tensorHom_chainComplexMap X Y A B R S)
      have e₂ := SSet.shuffleAlexanderWhitneyHomotopy_hom_naturality R S
        (𝟙 (toSSet.obj X)) (toSSet.map (TopPair.ofSubset B).map) i j
      have e₃ : (𝟙 ((toSSet.obj X).chainComplex R) ⊗ₘ
            SSet.chainComplexMap (toSSet.map (TopPair.ofSubset B).map) S) ≫
          ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ 𝟙 ((toSSet.obj Y).chainComplex S)) ≫
            (tensorLeftShortComplex ((TopPair.ofSubset A).singularChainComplex R)
              ((TopPair.ofSubset B).singularChainComplexShortComplex S)).g = 0 :=
        (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _)
          (singularChainComplexπ_tensorHom_id_comp_id_tensorHom_chainComplexMap
            X Y A B R S).symm).trans <|
            (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·)
              (tensorLeftShortComplex ((TopPair.ofSubset A).singularChainComplex R)
                ((TopPair.ofSubset B).singularChainComplexShortComplex S)).zero).trans comp_zero
      have e₃' := congrArg (fun φ ↦ φ.f j) e₃
      simp only [comp_f, zero_f] at e₁ e₃'
      simp only [CategoryTheory.Functor.map_id] at e₂
      exact (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) e₁).trans <|
        (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ _)
            (singularChainComplexπ_tensorHom_id_f_shuffleAlexanderWhitneyPairFstHomotopy_hom
              X Y A R S
              i j)).trans (Category.assoc _ _ _)))).trans <|
        (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) e₂).trans <|
        (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) e₃').trans <|
          comp_zero.trans comp_zero.symm)
    (id_tensorHom_singularChainComplexπ_shuffleAlexanderWhitneyPair X Y A B R S)
    ((Category.comp_id _).trans (Category.id_comp _).symm)

end Homotopy

end TopCat
