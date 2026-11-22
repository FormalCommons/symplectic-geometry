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
`C(X, A; R) ⊗ C(Y, B; S)` is chain homotopic to the identity: Tau Ceti's Eilenberg–Zilber homotopy
`SSet.shuffleAlexanderWhitneyHomotopy` is natural, so it descends from `C(X; R) ⊗ C(Y; S)` along
the two quotient maps (`Homotopy.descCokernel`). Pulled back along the shuffle map, the relative
cross product is therefore the cross product of cochains on `C(X, A; R) ⊗ C(Y, B; S)`, and the
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
two-step descent of the shuffle map to the small chains follows the construction of
`TopCat.shufflePair` (`SymplecticGeometry/AlgebraicTopology/Singular/Kunneth/Pair.lean`, from Tau
Ceti), whose two private identities between the projections of tensor products are restated here.
`TopCat.alexanderWhitneyDiagonal_comp_tensorHom_fst_snd` is a step of the proof of
`TauCeti.singularCross_eq_singularCup`, and the change of coefficients adapts
`TopCat.singularCup_eq_homologyMap_singularCup` (Tau Ceti, `Cohomology/Cup/Basic.lean`) to the
relative cup product, through the small-chain isomorphism as in
`TopCat.singularRelativeCup_naturality` (`Cohomology/Cup/Relative.lean`).

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
  refine (cancel_epi ((X.smallSingularSubcomplex ![U, V]).pair.chainComplexπ T)).1 ?_
  have hπ := congrArg (fun η ↦ η.app (X.smallSingularSubcomplex ![U, V]).pair)
    ((SSetPair.chainComplexFunctorπ C).naturality u)
  dsimp only [NatTrans.comp_app] at hπ
  have hD : X.alexanderWhitneyDiagonal u =
      ((SSet.chainComplexFunctor C).map u).app _ ≫ X.alexanderWhitneyDiagonal (𝟙 (R ⊗ S)) := by
    simp [TauCeti.alexanderWhitneyDiagonal_def]
  exact (chainComplexπ_relativeAlexanderWhitneyDiagonal U V u).trans <|
    (congrArg (· ≫ _) hD).trans <| (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) (chainComplexπ_relativeAlexanderWhitneyDiagonal U V (𝟙 _)).symm).trans <|
        (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) hπ).trans (Category.assoc _ _ _)

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

section Projections

variable (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (R S : C)

/-- The projection `C(X; R) ⊗ C(Y; S) ⟶ C(X, A; R) ⊗ C(Y, B; S)` is the projection in the first
variable followed by the projection in the second. -/
private theorem singularChainComplexπ_tensorHom_singularChainComplexπ_eq_comp :
    (TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ (TopPair.ofSubset B).singularChainComplexπ S =
      ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ 𝟙 ((toSSet.obj Y).chainComplex S)) ≫
        (𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
          (TopPair.ofSubset B).singularChainComplexπ S) :=
  (congrArg₂ (· ⊗ₘ ·) (Category.comp_id _).symm (Category.id_comp _).symm).trans
    (mapBifunctorMap_comp _ _ _ _ _ _)

/-- The projection `C(X; R) ⟶ C(X, A; R)` and the inclusion `C(B; S) ⟶ C(Y; S)`, tensored in the
two variables, commute. -/
private theorem singularChainComplexπ_tensorHom_id_comp_id_tensorHom_chainComplexMap :
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
private def shuffleSmallFst :
    (TopPair.ofSubset A).singularChainComplex R ⊗ (toSSet.obj Y).chainComplex S ⟶
      ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplex
        (R ⊗ S) :=
  have hS := shortExact_tensorRightShortComplex_singularChainComplexShortComplex X Y A R S
  have := hS.epi_g
  hS.exact.gIsCokernel.desc
    (CokernelCofork.ofπ _ (shuffle_cokernel_condition_small_fst X Y A B R S))

private theorem singularChainComplexπ_tensorHom_id_shuffleSmallFst :
    ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ 𝟙 ((toSSet.obj Y).chainComplex S)) ≫
        shuffleSmallFst X Y A B R S =
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
private theorem shuffleSmallFst_cokernel_condition :
    (𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
        SSet.chainComplexMap (toSSet.map (TopPair.ofSubset B).map) S) ≫
      shuffleSmallFst X Y A B R S = 0 := by
  have := (shortExact_tensorRightShortComplex_singularChainComplexShortComplex X
    (TopPair.ofSubset B).snd A R S).epi_g
  refine (cancel_epi ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
      𝟙 ((toSSet.obj (TopPair.ofSubset B).snd).chainComplex S))).1 ?_
  exact (Category.assoc _ _ _).symm.trans <|
    ((singularChainComplexπ_tensorHom_id_comp_id_tensorHom_chainComplexMap
    X Y A B R S) =≫ _).trans <| (Category.assoc _ _ _).trans <|
    ((congrArg (_ ≫ ·) (singularChainComplexπ_tensorHom_id_shuffleSmallFst X Y A B R S)).trans
      (shuffle_cokernel_condition_small_snd X Y A B R S)).trans comp_zero.symm

/-- **The shuffle map into the small chains** `C(X, A; R) ⊗ C(Y, B; S) ⟶ C(X × Y; A × Y + X × B)`,
induced by the shuffle map; followed by the map to `C(X × Y, A × Y ∪ X × B)` it is
`TopCat.shufflePair`. -/
private def shuffleSmall :
    (TopPair.ofSubset A).singularChainComplex R ⊗ (TopPair.ofSubset B).singularChainComplex S ⟶
      ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplex
        (R ⊗ S) :=
  have hS := shortExact_tensorLeftShortComplex_singularChainComplexShortComplex X Y A B R S
  have := hS.epi_g
  hS.exact.gIsCokernel.desc
    (CokernelCofork.ofπ _ (shuffleSmallFst_cokernel_condition X Y A B R S))

private theorem id_tensorHom_singularChainComplexπ_shuffleSmall :
    (𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
        (TopPair.ofSubset B).singularChainComplexπ S) ≫ shuffleSmall X Y A B R S =
      shuffleSmallFst X Y A B R S :=
  have hS := shortExact_tensorLeftShortComplex_singularChainComplexShortComplex X Y A B R S
  have := hS.epi_g
  hS.exact.gIsCokernel.fac _ WalkingParallelPair.one

private theorem singularChainComplexπ_tensorHom_singularChainComplexπ_shuffleSmall :
    ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
        (TopPair.ofSubset B).singularChainComplexπ S) ≫ shuffleSmall X Y A B R S =
      shuffle X Y R S ≫
        ((X ⊗ Y).smallSingularSubcomplex ![fst X Y ⁻¹' A, snd X Y ⁻¹' B]).pair.chainComplexπ
          (R ⊗ S) :=
  (congrArg (· ≫ shuffleSmall X Y A B R S)
    (singularChainComplexπ_tensorHom_singularChainComplexπ_eq_comp X Y A B R S)).trans <|
    (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) (id_tensorHom_singularChainComplexπ_shuffleSmall X Y A B R S)).trans
        (singularChainComplexπ_tensorHom_id_shuffleSmallFst X Y A B R S)

/-- The small-chain shuffle map followed by the map to the relative chains of the union is the
shuffle map of the pairs. -/
private theorem shuffleSmall_comp_smallSingularSubcomplexPairToUnion :
    shuffleSmall X Y A B R S ≫ SSetPair.chainComplexMap
        (smallSingularSubcomplexPairToUnion (fst X Y ⁻¹' A) (snd X Y ⁻¹' B)) (R ⊗ S) =
      shufflePair X Y A B R S := by
  have := epi_singularChainComplexπ_tensorHom_singularChainComplexπ X Y A B R S
  refine (cancel_epi ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
      (TopPair.ofSubset B).singularChainComplexπ S)).1 ?_
  exact (Category.assoc _ _ _).symm.trans <|
    ((singularChainComplexπ_tensorHom_singularChainComplexπ_shuffleSmall X Y A B R S) =≫ _).trans <|
      (Category.assoc _ _ _).trans <|
        (congrArg (_ ≫ ·) (chainComplexπ_smallSingularSubcomplexPairToUnion _ _ _)).trans
          (singularChainComplexπ_tensorHom_singularChainComplexπ_shufflePair X Y A B R S).symm

end ShuffleSmall

section Homotopy

variable (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (R S : C)

/-- The composite of the shuffle and Alexander–Whitney maps, descended to `C(X, A; R) ⊗ C(Y; S)`. -/
private def shuffleAlexanderWhitneyFst :
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

private theorem singularChainComplexπ_tensorHom_id_shuffleAlexanderWhitneyFst :
    ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ 𝟙 ((toSSet.obj Y).chainComplex S)) ≫
        shuffleAlexanderWhitneyFst X Y A R S =
      shuffle X Y R S ≫ alexanderWhitney X Y R S ≫
        ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ 𝟙 ((toSSet.obj Y).chainComplex S)) :=
  have hS := shortExact_tensorRightShortComplex_singularChainComplexShortComplex X Y A R S
  have := hS.epi_g
  hS.exact.gIsCokernel.fac _ WalkingParallelPair.one

/-- The Eilenberg–Zilber homotopy `AW ∘ shuffle ≃ id`, descended to `C(X, A; R) ⊗ C(Y; S)`: it is
natural, so it preserves `C(A; R) ⊗ C(Y; S)`. -/
private def shuffleAlexanderWhitneyFstHomotopy :
    _root_.Homotopy (shuffleAlexanderWhitneyFst X Y A R S) (𝟙 _) :=
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
    ((singularChainComplexπ_tensorHom_id_shuffleAlexanderWhitneyFst X Y A R S).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ _) (shuffle_alexanderWhitney X Y R S))))
    ((Category.comp_id _).trans (Category.id_comp _).symm)

private theorem singularChainComplexπ_tensorHom_id_f_shuffleAlexanderWhitneyFstHomotopy_hom
    (i j : ℕ) :
    ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ 𝟙 ((toSSet.obj Y).chainComplex S)).f i ≫
        (shuffleAlexanderWhitneyFstHomotopy X Y A R S).hom i j =
      (SSet.shuffleAlexanderWhitneyHomotopy (toSSet.obj X) (toSSet.obj Y) R S).hom i j ≫
        ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ 𝟙 ((toSSet.obj Y).chainComplex S)).f j :=
  Homotopy.π_descCokernel_hom _ _ _ _ _ _ _ _ _ i j

/-- The relative Alexander–Whitney map of the two pairs, after the small-chain shuffle map: an
endomorphism of `C(X, A; R) ⊗ C(Y, B; S)`. -/
private def shuffleAlexanderWhitneyPair :
    (TopPair.ofSubset A).singularChainComplex R ⊗ (TopPair.ofSubset B).singularChainComplex S ⟶
      (TopPair.ofSubset A).singularChainComplex R ⊗ (TopPair.ofSubset B).singularChainComplex S :=
  shuffleSmall X Y A B R S ≫
    relativeAlexanderWhitneyDiagonal (fst X Y ⁻¹' A) (snd X Y ⁻¹' B) (𝟙 (R ⊗ S)) ≫
      (TopPair.singularChainComplexMap
          (TopPair.ofSubsetMap (fst X Y) (Set.mapsTo_preimage _ _)) R ⊗ₘ
        TopPair.singularChainComplexMap
          (TopPair.ofSubsetMap (snd X Y) (Set.mapsTo_preimage _ _)) S)

private theorem singularChainComplexπ_tensorHom_singularChainComplexπ_shuffleAlexanderWhitneyPair :
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
    ((singularChainComplexπ_tensorHom_singularChainComplexπ_shuffleSmall X Y A B R S) =≫ _).trans <|
      (Category.assoc _ _ _).trans <| congrArg (_ ≫ ·) <|
        (chainComplexπ_relativeAlexanderWhitneyDiagonal_assoc _ _ _ _).trans <|
          (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) hπ).trans <|
            (Category.assoc _ _ _).symm.trans <|
              congrArg (· ≫ _) (alexanderWhitneyDiagonal_comp_tensorHom_fst_snd X Y R S)

/-- The Eilenberg–Zilber homotopy `AW ∘ shuffle ≃ id`, descended to `C(X, A; R) ⊗ C(Y, B; S)`: the
relative Alexander–Whitney map of the pairs after the small-chain shuffle map is homotopic to the
identity. -/
private def shuffleAlexanderWhitneyPairHomotopy :
    _root_.Homotopy (shuffleAlexanderWhitneyPair X Y A B R S) (𝟙 _) :=
  have hS₁ := shortExact_tensorRightShortComplex_singularChainComplexShortComplex X Y A R S
  have hS₂ := shortExact_tensorLeftShortComplex_singularChainComplexShortComplex X Y A B R S
  have := hS₁.epi_g
  _root_.Homotopy.descCokernel (shuffleAlexanderWhitneyFstHomotopy X Y A R S)
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
            (singularChainComplexπ_tensorHom_id_f_shuffleAlexanderWhitneyFstHomotopy_hom X Y A R S
              i j)).trans (Category.assoc _ _ _)))).trans <|
        (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) e₂).trans <|
        (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) e₃').trans <|
          comp_zero.trans comp_zero.symm)
    ((cancel_epi (tensorRightShortComplex ((toSSet.obj Y).chainComplex S)
      ((TopPair.ofSubset A).singularChainComplexShortComplex R)).g).1 <|
      (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ shuffleAlexanderWhitneyPair X Y A B R S)
        (singularChainComplexπ_tensorHom_singularChainComplexπ_eq_comp X Y A B R S).symm).trans <|
      (singularChainComplexπ_tensorHom_singularChainComplexπ_shuffleAlexanderWhitneyPair
        X Y A B R S).trans <|
      (congrArg (fun t ↦ shuffle X Y R S ≫ alexanderWhitney X Y R S ≫ t)
        (singularChainComplexπ_tensorHom_singularChainComplexπ_eq_comp X Y A B R S)).trans <|
      (congrArg (shuffle X Y R S ≫ ·) (Category.assoc _ _ _).symm).trans <|
      (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _)
        (singularChainComplexπ_tensorHom_id_shuffleAlexanderWhitneyFst X Y A R S).symm).trans
          (Category.assoc _ _ _))
    ((Category.comp_id _).trans (Category.id_comp _).symm)

end Homotopy

section Kronecker

variable (X Y : TopCat.{w}) {A : Set X} {B : Set Y} (R S : C) {k : Type*} [CommRing k]
  [Linear k C] [MonoidalLinear k C] {M N P : C} (μ : M ⊗ N ⟶ P) (hA : IsOpen A) (hB : IsOpen B)

/-- Pulled back along the shuffle map of the pairs, the relative cross product is the cross product
of the cochain complexes `Hom(C(X, A; R), M)` and `Hom(C(Y, B; S), N)`: the cup product along the
identity of `C(X, A; R) ⊗ C(Y, B; S)`. -/
private theorem homologyMap_shufflePair_singularRelativeCross (p q n : ℕ) (h : p + q = n)
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
  rw [← shuffleSmall_comp_smallSingularSubcomplexPairToUnion]
  refine (TauCeti.ChainComplex.homologyMap_linearYonedaFunctor_map_comp_apply _ _ n _).trans ?_
  rw [TauCeti.singularRelativeCross_apply]
  refine (congrArg (homologyMap ((TauCeti.ChainComplex.linearYonedaFunctor k P).map
      (shuffleSmall X Y A B R S).op) n)
    (homologyMap_cochainComplexMap_singularRelativeCup k (𝟙 (R ⊗ S)) μ (fst X Y ⁻¹' A)
      (snd X Y ⁻¹' B) (isOpen_subtypeVal_preimage_preimage_fst_union hA)
      (isOpen_subtypeVal_preimage_preimage_snd_union hB) p q n h _ _)).trans ?_
  refine (TauCeti.ChainComplex.cup_precomp _ μ _ p q n h _ _).symm.trans ?_
  refine (TauCeti.ChainComplex.cup_naturality (shuffleAlexanderWhitneyPair X Y A B R S) μ _
    (𝟙 _) (TopPair.singularChainComplexMap
      (TopPair.ofSubsetMap (fst X Y) (Set.mapsTo_preimage _ _)) R)
    (TopPair.singularChainComplexMap
      (TopPair.ofSubsetMap (snd X Y) (Set.mapsTo_preimage _ _)) S)
    ((Category.id_comp _).trans (Category.assoc _ _ _).symm) p q n h a b).trans ?_
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
    (homologyMap_shufflePair_singularRelativeCross X Y R S μ hA hB p q n h a b)).trans ?_
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
      (TopCat.of V₁) (TopCat.of V₂) R S μ isOpen_compl_singleton isOpen_compl_singleton p q n h
      g₁ g₂) (x ⊗ₜ y)
  rw [complZeroPairCross_def]
  -- The composite of linear maps is applied one after the other.
  exact hK.trans <| (congrArg (ConcreteCategory.hom (TopPair.singularKronecker _ K n
    (singularRelativeCross K (TopCat.of V₁) (TopCat.of V₂) isOpen_compl_singleton
      isOpen_compl_singleton μ p q n h g₁ g₂))) hz).trans hA

end TauCeti
