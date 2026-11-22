/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.Kunneth.RelativePair
public import TauCeti.AlgebraicTopology.Cohomology.Local.Cross

/-!
# The Kronecker pairing of relative cross products

Let `A ⊆ X` and `B ⊆ Y` be open, and write `A × Y` and `X × B` for their preimages under the
projections of `X × Y`. The relative cohomology cross product
`TauCeti.singularRelativeCross : Hᵖ(X, A) × H^q(Y, B) ⟶ Hⁿ(X × Y, A × Y ∪ X × B)` and the homology
cross product of the pairs
`TopCat.singularHomologyCrossRelPair : Hₚ(X, A) ⊗ H_q(Y, B) ⟶ Hₙ(X × Y, A × Y ∪ X × B)` pair as
the absolute ones do, with no sign:

`⟨a × b, x × y⟩ = μ (⟨a, x⟩ ⊗ ⟨b, y⟩)`

(`TopCat.singularHomologyCrossRelPair_comp_singularKronecker_singularRelativeCross`).

The relative cross product is defined through the chains `C(X × Y; A × Y + X × B)` of `X × Y`
relative to its singular simplices lying in `A × Y` or in `X × B`, on which it is represented by
the relative Alexander–Whitney diagonal. The shuffle map of the pairs factors through these small
chains, and the composite of the shuffle and Alexander–Whitney maps on
`C(X, A; R) ⊗ C(Y, B; S)` is chain homotopic to the identity
(`TopCat.shuffleAlexanderWhitneyPairHomotopy`, in
`SymplecticGeometry/AlgebraicTopology/Singular/Kunneth/RelativePair.lean`). Pulled back along the
shuffle map, the relative cross product is therefore the cross product of cochains on
`C(X, A; R) ⊗ C(Y, B; S)` (`TopCat.homologyMap_shufflePair_singularRelativeCross`), and the
algebraic identity `ChainComplex.homologyCross_comp_kronecker_cup` applies.

For a coefficient morphism `u : T ⟶ R ⊗ S`, the relative cup product along `u` is the one along
the identity of `R ⊗ S` followed by the change of chain coefficients along `u`
(`TopCat.singularRelativeCup_eq_homologyMap_singularRelativeCup`). With it, the Kronecker pairing
of the relative cup product of classes pulled back along the two projections, restricted to any
`Z ⊆ A × Y ∪ X × B`, is computed from the relative cross product
(`TopCat.singularKronecker_singularRelativeCupPullback_fst_snd`). For the pairs `(V, V ∖ {0})`
this evaluates Tau Ceti's product of local classes `TauCeti.complZeroPairCross`
(`TauCeti.singularKronecker_complZeroPairCross`).

## Main results

* `TopCat.singularHomologyCrossRelPair_comp_singularKronecker_singularRelativeCross`: the
  Kronecker pairing of the relative cross products.
* `TopCat.homologyMap_shufflePair_singularRelativeCross`: the relative cross product pulled
  back along the shuffle map of the pairs.
* `TopCat.singularRelativeCup_eq_homologyMap_singularRelativeCup`: the relative cup product
  along a coefficient morphism.
* `TopCat.singularKronecker_singularRelativeCupPullback_fst_snd`: the Kronecker pairing of the
  relative cup product of classes pulled back along the projections of a product.
* `TauCeti.singularKronecker_complZeroPairCross`: the Kronecker pairing of the product of classes
  of the pairs `(V₁, V₁ ∖ {0})` and `(V₂, V₂ ∖ {0})`, with coefficients in modules.

The proof of the Kronecker pairing adapts that of
`TopCat.singularHomologyCross_comp_singularKronecker_singularCross` and
`TauCeti.singularEilenbergZilberCohomologyIso_hom_singularCross` (Tau Ceti,
`TauCeti/AlgebraicTopology/Cohomology/CrossProduct.lean`) from absolute to relative chains. The
change of coefficients adapts `TopCat.singularCup_eq_homologyMap_singularCup` (Tau Ceti,
`Cohomology/Cup/Basic.lean`) to the relative cup product, through the small-chain isomorphism as
in `TopCat.singularRelativeCup_naturality` (`Cohomology/Cup/Relative.lean`).

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.2, the relative cross product and the Kronecker pairing of cross products, and
  Section 3.B, the cross product in homology.
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

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCoproducts.{w} C]

section Coefficients

variable {X : TopCat.{w}} {R S T M N L : C} {k : Type*} [CommRing k] [Linear k C]
  [MonoidalLinear k C]

/-- The relative Alexander–Whitney diagonal along a coefficient morphism `u : T ⟶ R ⊗ S` is the
change of chain coefficients along `u` followed by the relative Alexander–Whitney diagonal along
the identity of `R ⊗ S`. -/
theorem relativeAlexanderWhitneyDiagonal_eq_comp (U V : Set X) (u : T ⟶ R ⊗ S) :
    relativeAlexanderWhitneyDiagonal U V u =
      ((SSetPair.chainComplexFunctor C).map u).app (X.smallSingularSubcomplex ![U, V]).pair ≫
        relativeAlexanderWhitneyDiagonal U V (𝟙 (R ⊗ S)) := by
  refine (cancel_epi (smallSingularSubcomplexπ ![U, V] T)).1 ?_
  have hD : X.alexanderWhitneyDiagonal u =
      ((SSet.chainComplexFunctor C).map u).app _ ≫ X.alexanderWhitneyDiagonal (𝟙 (R ⊗ S)) := by
    simp [TauCeti.alexanderWhitneyDiagonal_def]
  rw [smallSingularSubcomplexπ_relativeAlexanderWhitneyDiagonal, hD, Category.assoc,
    ← smallSingularSubcomplexπ_relativeAlexanderWhitneyDiagonal,
    smallSingularSubcomplexπ_coefficient_naturality_assoc]

/-- **The relative cup product changes coefficients along its coefficient morphism**: the relative
cup product along `u : T ⟶ R ⊗ S` is the relative cup product along the identity of `R ⊗ S`,
followed by the map `Hⁿ(X, U ∪ V; R ⊗ S, L) ⟶ Hⁿ(X, U ∪ V; T, L)` that precomposes relative
cochains with the chain map induced by `u`. -/
theorem singularRelativeCup_eq_homologyMap_singularRelativeCup (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ L)
    (U V : Set X) (hU : IsOpen ((↑) ⁻¹' U : Set ↥(U ∪ V)))
    (hV : IsOpen ((↑) ⁻¹' V : Set ↥(U ∪ V))) (p q n : ℕ) (h : p + q = n)
    (a : (TopPair.ofSubset U).singularCohomology R k M p)
    (b : (TopPair.ofSubset V).singularCohomology S k N q) :
    singularRelativeCup k u μ U V hU hV p q n h a b =
      homologyMap ((TauCeti.ChainComplex.linearYonedaFunctor k L).map
        (((SSetPair.chainComplexFunctor C).map u).app
          (TopPair.toSSetPair.obj (TopPair.ofSubset (U ∪ V)))).op) n
        (singularRelativeCup k (𝟙 (R ⊗ S)) μ U V hU hV p q n h a b) := by
  -- Both sides are determined by their images under the small-chain isomorphism, which commutes
  -- with the change of coefficients.
  have := isIso_homologyMap_cochainComplexMap_smallSingularSubcomplexPairToUnion T k L U V hU hV n
  apply (ModuleCat.mono_iff_injective (homologyMap (SSetPair.cochainComplexMap (R := T) (k := k)
    (M := L) (smallSingularSubcomplexPairToUnion U V)) n)).1 inferInstance
  rw [homologyMap_cochainComplexMap_singularRelativeCup, relativeAlexanderWhitneyDiagonal_eq_comp,
    TauCeti.ChainComplex.cup_precomp,
    ← homologyMap_cochainComplexMap_singularRelativeCup k (𝟙 (R ⊗ S)) μ U V hU hV]
  have hnat := ((SSetPair.chainComplexFunctor C).map u).naturality
    (smallSingularSubcomplexPairToUnion U V)
  have h₁ := TauCeti.ChainComplex.homologyMap_linearYonedaFunctor_map_comp_apply (k := k) (Y := L)
    (((SSetPair.chainComplexFunctor C).map u).app (X.smallSingularSubcomplex ![U, V]).pair)
    (((SSetPair.chainComplexFunctor C).obj (R ⊗ S)).map (smallSingularSubcomplexPairToUnion U V))
    n (singularRelativeCup k (𝟙 (R ⊗ S)) μ U V hU hV p q n h a b)
  have h₂ := TauCeti.ChainComplex.homologyMap_linearYonedaFunctor_map_comp_apply (k := k) (Y := L)
    (((SSetPair.chainComplexFunctor C).obj T).map (smallSingularSubcomplexPairToUnion U V))
    (((SSetPair.chainComplexFunctor C).map u).app
      (TopPair.toSSetPair.obj (TopPair.ofSubset (U ∪ V)))) n
    (singularRelativeCup k (𝟙 (R ⊗ S)) μ U V hU hV p q n h a b)
  rw [← hnat] at h₁
  exact h₁.symm.trans h₂

variable {Y : TopCat.{w}} {A : Set X} {B : Set Y}

/-- **The Kronecker pairing of the relative cup product of classes pulled back to a product.**
For open `A ⊆ X` and `B ⊆ Y`, a coefficient morphism `u : T ⟶ R ⊗ S` and `Z ⊆ A × Y ∪ X × B`,
evaluating the relative cup product of the pull-backs of `a` and `b` along the two projections,
in `Hⁿ(X × Y, Z; T, L)` (`TopCat.singularRelativeCupPullback`), is mapping to
`Hₙ(X × Y, A × Y ∪ X × B; T)`, changing coefficients along `u`, and evaluating the relative cross
product `a × b`. -/
theorem singularKronecker_singularRelativeCupPullback_fst_snd (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ L)
    (hA : IsOpen A) (hB : IsOpen B) {Z : Set ↑(X ⊗ Y)} (hZ : Z ⊆ fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)
    (p q n : ℕ) (h : p + q = n) (a : (TopPair.ofSubset A).singularCohomology R k M p)
    (b : (TopPair.ofSubset B).singularCohomology S k N q) :
    (TopPair.ofSubset Z).singularKronecker k n
        (singularRelativeCupPullback k u μ (fst X Y) (snd X Y) hA hB hZ p q n h a b) =
      TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 (X ⊗ Y)) fun _ hz ↦ hZ hz) T n ≫
        homologyMap (((SSetPair.chainComplexFunctor C).map u).app
          (TopPair.toSSetPair.obj (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)))) n ≫
          (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularKronecker k n
            (TauCeti.singularRelativeCross k X Y hA hB μ p q n h a b) := by
  rw [singularRelativeCupPullback_apply, TopPair.singularKronecker_naturality,
    singularRelativeCup_eq_homologyMap_singularRelativeCup, TauCeti.singularRelativeCross_apply,
    TopPair.singularKronecker_def, TopPair.singularKronecker_def]
  exact congrArg (_ ≫ ·) (TauCeti.ChainComplex.kronecker_naturality (k := k) (Y := L)
    (X := (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularChainComplex (R ⊗ S))
    (((SSetPair.chainComplexFunctor C).map u).app
      (TopPair.toSSetPair.obj (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)))) n _)

end Coefficients

variable [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)]

section Kronecker

variable (X Y : TopCat.{w}) {A : Set X} {B : Set Y} {R S : C} {k : Type*} [CommRing k]
  [Linear k C] [MonoidalLinear k C] {M N P : C} (μ : M ⊗ N ⟶ P) (hA : IsOpen A) (hB : IsOpen B)

/-- Pulled back along the shuffle map of the pairs, the relative cross product is the cross product
of the cochain complexes `Hom(C(X, A; R), M)` and `Hom(C(Y, B; S), N)`: the cup product along the
identity of `C(X, A; R) ⊗ C(Y, B; S)`. -/
theorem homologyMap_shufflePair_singularRelativeCross (p q n : ℕ) (h : p + q = n)
    (a : (TopPair.ofSubset A).singularCohomology R k M p)
    (b : (TopPair.ofSubset B).singularCohomology S k N q) :
    homologyMap ((TauCeti.ChainComplex.linearYonedaFunctor k P).map
        (shufflePair X Y A B R S).op) n (TauCeti.singularRelativeCross k X Y hA hB μ p q n h a b) =
      TauCeti.ChainComplex.cup k (𝟙 ((TopPair.ofSubset A).singularChainComplex R ⊗
        (TopPair.ofSubset B).singularChainComplex S)) μ p q n h a b := by
  have hid : ∀ x : ((TopPair.ofSubset A).singularChainComplex R ⊗
      (TopPair.ofSubset B).singularChainComplex S).linearYonedaObj k P |>.homology n,
      homologyMap ((TauCeti.ChainComplex.linearYonedaFunctor k P).map
        (𝟙 ((TopPair.ofSubset A).singularChainComplex R ⊗
          (TopPair.ofSubset B).singularChainComplex S)).op) n x = x := fun x ↦ by
    rw [op_id, CategoryTheory.Functor.map_id]
    exact ConcreteCategory.congr_hom (homologyMap_id _ n) x
  -- The shuffle map of the pairs factors through the small chains, on which the relative cross
  -- product is the cup product along the relative Alexander–Whitney diagonal.
  rw [← shuffleSmallPair_comp_smallSingularSubcomplexPairToUnion]
  refine (TauCeti.ChainComplex.homologyMap_linearYonedaFunctor_map_comp_apply _ _ n _).trans ?_
  rw [TauCeti.singularRelativeCross_apply]
  refine (congrArg (homologyMap ((TauCeti.ChainComplex.linearYonedaFunctor k P).map
      (shuffleSmallPair X Y A B R S).op) n)
    (homologyMap_cochainComplexMap_singularRelativeCup k (𝟙 (R ⊗ S)) μ (fst X Y ⁻¹' A)
      (snd X Y ⁻¹' B) (isOpen_subtypeVal_preimage_preimage_fst_union hA)
      (isOpen_subtypeVal_preimage_preimage_snd_union hB) p q n h _ _)).trans ?_
  refine (TauCeti.ChainComplex.cup_precomp _ μ _ p q n h _ _).symm.trans ?_
  refine (TauCeti.ChainComplex.cup_naturality (shuffleAlexanderWhitneyPair X Y A B R S) μ _
    (𝟙 _) (TopPair.singularChainComplexMap
      (TopPair.ofSubsetMap (fst X Y) (Set.mapsTo_preimage _ _)) R)
    (TopPair.singularChainComplexMap
      (TopPair.ofSubsetMap (snd X Y) (Set.mapsTo_preimage _ _)) S)
    ((Category.id_comp _).trans <|
      (shuffleAlexanderWhitneyPair_def X Y A B R S).trans (Category.assoc _ _ _).symm)
    p q n h a b).trans ?_
  -- The resulting diagonal of `C(X, A; R) ⊗ C(Y, B; S)` is homotopic to the identity.
  exact (hid _).trans (TauCeti.ChainComplex.cup_eq_of_homotopy _ μ
    (shuffleAlexanderWhitneyPairHomotopy X Y A B R S) p q n h a b)

variable (p q : ℕ)
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorLeft (((TopPair.ofSubset A).singularChainComplex R).homology p))]
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorRight (((TopPair.ofSubset B).singularChainComplex S).cycles q))]
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorRight (((TopPair.ofSubset B).singularChainComplex S).X ((ComplexShape.down ℕ).prev q)))]

/-- **The Kronecker pairing of relative cross products**, `⟨a × b, x × y⟩ = μ (⟨a, x⟩ ⊗ ⟨b, y⟩)`:
for open `A ⊆ X` and `B ⊆ Y`, the evaluation of the relative cohomology cross product
`a × b ∈ Hⁿ(X × Y, A × Y ∪ X × B; R ⊗ S, P)` on the image of the homology cross product
`Hₚ(X, A; R) ⊗ H_q(Y, B; S) ⟶ Hₙ(X × Y, A × Y ∪ X × B; R ⊗ S)` of the pairs is the tensor product
of the evaluations of `a` and `b`, followed by the coefficient pairing `μ`. -/
theorem singularHomologyCrossRelPair_comp_singularKronecker_singularRelativeCross (n : ℕ)
    (h : p + q = n) (a : (TopPair.ofSubset A).singularCohomology R k M p)
    (b : (TopPair.ofSubset B).singularCohomology S k N q) :
    singularHomologyCrossRelPair X Y A B R S p q n h ≫
        (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularKronecker k n
          (TauCeti.singularRelativeCross k X Y hA hB μ p q n h a b) =
      ((TopPair.ofSubset A).singularKronecker k p a ⊗ₘ
        (TopPair.ofSubset B).singularKronecker k q b) ≫ μ := by
  rw [singularHomologyCrossRelPair_def, TopPair.singularKronecker_def,
    TopPair.singularKronecker_def, TopPair.singularKronecker_def, Category.assoc,
    ← TauCeti.ChainComplex.kronecker_naturality]
  refine (congrArg (_ ≫ TauCeti.ChainComplex.kronecker k _ P n ·)
    (homologyMap_shufflePair_singularRelativeCross X Y μ hA hB p q n h a b)).trans ?_
  exact ChainComplex.homologyCross_comp_kronecker_cup _ _ μ p q n h a b

end Kronecker

end TopCat

namespace TauCeti

variable {K : Type w} [CommRing K] {R S T M N L : ModuleCat.{w} K}
  (V₁ V₂ : Type w) [TopologicalSpace V₁] [Zero V₁] [T1Space V₁]
  [TopologicalSpace V₂] [Zero V₂] [T1Space V₂]

/-- **The Kronecker pairing of the product of classes of the pairs `(V, V ∖ {0})`.** Let
`x ∈ Hₚ(V₁, V₁ ∖ {0}; R)` and `y ∈ H_q(V₂, V₂ ∖ {0}; S)`, and let
`z ∈ Hₙ(V₁ × V₂, (V₁ × V₂) ∖ {0}; T)` be a class whose image in
`Hₙ(V₁ × V₂, (V₁ ∖ {0}) × V₂ ∪ V₁ × (V₂ ∖ {0}); R ⊗ S)`, after the change of coefficients along
`u : T ⟶ R ⊗ S`, is the homology cross product of `x` and `y`. Then the product
`g₁ × g₂ = TauCeti.complZeroPairCross … u μ … g₁ g₂` of `g₁ ∈ Hᵖ(V₁, V₁ ∖ {0}; R, M)` and
`g₂ ∈ H^q(V₂, V₂ ∖ {0}; S, N)` satisfies `⟨g₁ × g₂, z⟩ = μ (⟨g₁, x⟩ ⊗ ⟨g₂, y⟩)`. -/
theorem singularKronecker_complZeroPairCross (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ L) {p q n : ℕ}
    (h : p + q = n)
    (g₁ : (TopPair.ofSubset (X := TopCat.of V₁) ({0}ᶜ : Set V₁)).singularCohomology R K M p)
    (g₂ : (TopPair.ofSubset (X := TopCat.of V₂) ({0}ᶜ : Set V₂)).singularCohomology S K N q)
    (x : ↑((TopPair.ofSubset (X := TopCat.of V₁) ({0}ᶜ : Set V₁)).singularHomology R p))
    (y : ↑((TopPair.ofSubset (X := TopCat.of V₂) ({0}ᶜ : Set V₂)).singularHomology S q))
    (z : ↑((TopPair.ofSubset (X := TopCat.of (V₁ × V₂)) ({0}ᶜ : Set (V₁ × V₂))).singularHomology
      T n))
    (hz : homologyMap (((SSetPair.chainComplexFunctor (ModuleCat.{w} K)).map u).app
        (TopPair.toSSetPair.obj (TopPair.ofSubset
          (CartesianMonoidalCategory.fst (TopCat.of V₁) (TopCat.of V₂) ⁻¹' {0}ᶜ ∪
            CartesianMonoidalCategory.snd (TopCat.of V₁) (TopCat.of V₂) ⁻¹' {0}ᶜ))))
        n (TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 (TopCat.of V₁ ⊗ TopCat.of V₂))
          fun _ hv ↦ compl_zero_prod_subset V₁ V₂ hv) T n z) =
      TopCat.singularHomologyCrossRelPair (TopCat.of V₁) (TopCat.of V₂) {0}ᶜ {0}ᶜ R S p q n h
        (x ⊗ₜ y)) :
    (TopPair.ofSubset (X := TopCat.of (V₁ × V₂)) ({0}ᶜ : Set (V₁ × V₂))).singularKronecker K n
        (complZeroPairCross K V₁ V₂ u μ p q n h g₁ g₂) z =
      μ ((TopPair.ofSubset (X := TopCat.of V₁) ({0}ᶜ : Set V₁)).singularKronecker K p g₁ x ⊗ₜ
        (TopPair.ofSubset (X := TopCat.of V₂) ({0}ᶜ : Set V₂)).singularKronecker K q g₂ y) := by
  have hK := ConcreteCategory.congr_hom
    (TopCat.singularKronecker_singularRelativeCupPullback_fst_snd (X := TopCat.of V₁)
      (Y := TopCat.of V₂) u μ isOpen_compl_singleton isOpen_compl_singleton
      (compl_zero_prod_subset V₁ V₂) p q n h g₁ g₂) z
  have hA := ConcreteCategory.congr_hom
    (TopCat.singularHomologyCrossRelPair_comp_singularKronecker_singularRelativeCross
      (TopCat.of V₁) (TopCat.of V₂) μ isOpen_compl_singleton isOpen_compl_singleton p q n h
      g₁ g₂) (x ⊗ₜ y)
  rw [complZeroPairCross_def]
  -- The composite of linear maps is applied one after the other.
  exact hK.trans <| (congrArg (ConcreteCategory.hom (TopPair.singularKronecker _ K n
    (singularRelativeCross K (TopCat.of V₁) (TopCat.of V₂) isOpen_compl_singleton
      isOpen_compl_singleton μ p q n h g₁ g₂))) hz).trans hA

end TauCeti
