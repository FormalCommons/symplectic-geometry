/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.MayerVietoris.Relative
public import TauCeti.AlgebraicTopology.Singular.AlexanderWhitney.RelativeCup

/-!
# The relative Alexander–Whitney diagonal through the small-chain quotient

For subsets `U` and `V` of a space `X`, Tau Ceti's `TopCat.relativeAlexanderWhitneyDiagonal`
is the descent of the Alexander–Whitney diagonal of `X` to its chains relative to the singular
simplices lying in `U` or in `V`. This file restates the equation that characterizes it,
`TopCat.chainComplexπ_relativeAlexanderWhitneyDiagonal`, with the quotient maps written as
`TopCat.smallSingularSubcomplexπ` and `TopPair.singularChainComplexπOfSubset`, whose sources are
the chains of `X`, so that it rewrites in composites with chain maps into the chains of `X`.

It also states the compatibility of the relative diagonal with the map from the relative chains of
`(X, U)` to the chains relative to the small chains, and its compatibility with changes of
the chain coefficients.

## Main results

* `TopCat.smallSingularSubcomplexπ_relativeAlexanderWhitneyDiagonal`: the relative
  Alexander–Whitney diagonal after the quotient map to the chains relative to the small chains is
  the Alexander–Whitney diagonal of `X` followed by the tensor product of the quotient maps to the
  chains of `(X, U)` and of `(X, V)`.
* `TopCat.chainComplexMap_toSmallSingularSubcomplexPair_relativeAlexanderWhitneyDiagonal`: the
  relative Alexander–Whitney diagonal after the map from the chains of `(X, U)` to the chains
  relative to the small chains is the Alexander–Whitney diagonal of `(X, U)` followed by the
  quotient map onto the chains of `(X, V)` on the second factor.
* `TopCat.relativeAlexanderWhitneyDiagonal_coefficient_naturality`: the relative
  Alexander–Whitney diagonal commutes with compatible changes of the chain coefficients. Its proof
  adapts that of Tau Ceti's `TopPair.alexanderWhitneyDiagonal_coefficient_naturality`
  (`Singular/AlexanderWhitney/Relative.lean`) to the chains relative to the small chains.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.1, Proposition 2.21, the chains subordinate to a cover.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory Limits

universe w v u

namespace TopCat

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts in
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts in
/-- `TopCat.chainComplexπ_relativeAlexanderWhitneyDiagonal`, with the quotient maps written as
`TopCat.smallSingularSubcomplexπ` and `TopPair.singularChainComplexπOfSubset`, whose sources are
the chains of `X`. -/
@[reassoc]
theorem smallSingularSubcomplexπ_relativeAlexanderWhitneyDiagonal [MonoidalCategory C]
    [MonoidalPreadditive C] {X : TopCat.{w}} (U V : Set X) {R S T : C} (u : T ⟶ R ⊗ S) :
    smallSingularSubcomplexπ ![U, V] T ≫ relativeAlexanderWhitneyDiagonal U V u =
      X.alexanderWhitneyDiagonal u ≫
        (TopPair.singularChainComplexπOfSubset R U ⊗ₘ TopPair.singularChainComplexπOfSubset S V) :=
  chainComplexπ_relativeAlexanderWhitneyDiagonal U V u

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts in
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts in
/-- The relative Alexander–Whitney diagonal after the map from the relative chains of `(X, U)` to
the chains relative to the small chains is the Alexander–Whitney diagonal of `(X, U)` followed by
the quotient map onto the chains of `(X, V)` on the second factor. -/
@[reassoc]
theorem chainComplexMap_toSmallSingularSubcomplexPair_relativeAlexanderWhitneyDiagonal
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] [MonoidalCategory C]
    [MonoidalPreadditive C] {X : TopCat.{w}} (U V : Set X) {R S T : C} (u : T ⟶ R ⊗ S) :
    SSetPair.chainComplexMap
        (toSmallSingularSubcomplexPair ![U, V] (A := U) (i := 0) subset_rfl) T ≫
        relativeAlexanderWhitneyDiagonal U V u =
      (TopPair.ofSubset U).alexanderWhitneyDiagonal u ≫
        HomologicalComplex.tensorHom (𝟙 _) (TopPair.singularChainComplexπOfSubset S V) := by
  rw [← cancel_epi (TopPair.singularChainComplexπOfSubset T U),
    singularChainComplexπOfSubset_comp_chainComplexMap_toSmallSingularSubcomplexPair_assoc ![U, V]
      (A := U) (i := 0) subset_rfl T,
    smallSingularSubcomplexπ_relativeAlexanderWhitneyDiagonal]
  refine Eq.trans ?_ (TopPair.singularChainComplexπ_alexanderWhitneyDiagonal_assoc
    (TopPair.ofSubset U) u _).symm
  have hπ := HomologicalComplex.mapBifunctorMap_comp (curriedTensor C) (ComplexShape.down ℕ)
    (TopPair.singularChainComplexπOfSubset R U) (𝟙 _) (𝟙 _)
    (TopPair.singularChainComplexπOfSubset S V)
  rw [Category.comp_id, Category.id_comp] at hπ
  -- The whiskering on the right is `HomologicalComplex.tensorHom f (𝟙 _)` by definition.
  exact (congrArg (X.alexanderWhitneyDiagonal u ≫ ·) hπ).trans (Category.assoc _ _ _).symm

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts in
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts in
/-- **Coefficient naturality of the relative Alexander–Whitney diagonal**: if
`c ≫ u = u' ≫ (a ⊗ b)`, then changing the chain coefficients of `C(X; U + V)` along `c` and taking
the relative diagonal along `u` is taking the relative diagonal along `u'` and changing the
coefficients of `C(X, U)` along `a` and of `C(X, V)` along `b`. -/
@[reassoc]
theorem relativeAlexanderWhitneyDiagonal_coefficient_naturality {C : Type u} [Category.{v} C]
    [HasCoproducts.{w} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
    {X : TopCat.{w}} (U V : Set X) {R S T R' S' T' : C} (u : T ⟶ R ⊗ S) (u' : T' ⟶ R' ⊗ S')
    (a : R' ⟶ R) (b : S' ⟶ S) (c : T' ⟶ T) (hu : c ≫ u = u' ≫ (a ⊗ₘ b)) :
    ((SSetPair.chainComplexFunctor C).map c).app (X.smallSingularSubcomplex ![U, V]).pair ≫
        relativeAlexanderWhitneyDiagonal U V u =
      relativeAlexanderWhitneyDiagonal U V u' ≫
        HomologicalComplex.tensorHom
          (((SSetPair.chainComplexFunctor C).map a).app
            (TopPair.toSSetPair.obj (TopPair.ofSubset U)))
          (((SSetPair.chainComplexFunctor C).map b).app
            (TopPair.toSSetPair.obj (TopPair.ofSubset V))) := by
  rw [← cancel_epi (smallSingularSubcomplexπ ![U, V] T'),
    ← smallSingularSubcomplexπ_coefficient_naturality_assoc,
    smallSingularSubcomplexπ_relativeAlexanderWhitneyDiagonal,
    smallSingularSubcomplexπ_relativeAlexanderWhitneyDiagonal_assoc,
    reassoc_of% (alexanderWhitneyDiagonal_coefficient_naturality X u u' a b c hu)]
  refine congrArg (_ ≫ ·) ((HomologicalComplex.mapBifunctorMap_comp _ _ _ _ _ _).symm.trans ?_)
  rw [TopPair.singularChainComplexπOfSubset_coefficient_naturality,
    TopPair.singularChainComplexπOfSubset_coefficient_naturality]
  exact HomologicalComplex.mapBifunctorMap_comp _ _ _ _ _ _

end TopCat

end
