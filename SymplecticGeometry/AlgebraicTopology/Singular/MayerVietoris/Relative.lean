/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.PairMap
public import SymplecticGeometry.Topology.Category.TopCat.CodRestrict
public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.Relative

/-!
# The quotient map to the small chains

For a family `U` of subsets of a space `X`, Tau Ceti's relative Mayer–Vietoris sequence and its
relative cup product use the chains of `X` relative to its singular simplices lying in some member
of `U`, the cokernel of the inclusion of the small chains `X.smallSingularSubcomplex U`. This file
writes the quotient map to these chains as `TopCat.smallSingularSubcomplexπ`, whose source is the
chains of `X` rather than the ambient chains of the pair `(X.smallSingularSubcomplex U).pair`, as
`TopPair.singularChainComplexπOfSubset` does for the pair of a subset. Composites with chain maps
of maps into `X` then reassociate by `rw`.

## Main definitions and results

* `TopCat.smallSingularSubcomplexπ`: the quotient map from the chains of `X` to its chains
  relative to the small chains.
* `TopCat.chainComplexMap_comp_smallSingularSubcomplexπ`: a map into `X` whose image lies in a
  member of `U` sends chains to zero there.
* `TopCat.smallSingularSubcomplexπ_comp_chainComplexMap_smallSingularSubcomplexPairToUnion`:
  Tau Ceti's `TopCat.chainComplexπ_smallSingularSubcomplexPairToUnion`, restated through
  `TopCat.smallSingularSubcomplexπ` and `TopPair.singularChainComplexπOfSubset`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.1, Proposition 2.21, the chains subordinate to a cover.
-/

public section

noncomputable section

open CategoryTheory Limits

universe w v u

namespace TopCat

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

/-- The quotient map from the singular chains of `X` to its chains relative to the singular
simplices lying in some member of a family `U` of subsets: `SSetPair.chainComplexπ` of the pair
`(X.smallSingularSubcomplex U).pair`, with its source written as the chains of `X` rather than as
the ambient chains of the pair, as in `TopPair.singularChainComplexπOfSubset`, so that composites
with maps into the chains of `X` reassociate by `rw`. -/
noncomputable abbrev smallSingularSubcomplexπ {X : TopCat.{w}} {ι : Type*} (U : ι → Set X)
    (R : C) : (toSSet.obj X).chainComplex R ⟶ (X.smallSingularSubcomplex U).pair.chainComplex R :=
  (X.smallSingularSubcomplex U).pair.chainComplexπ R

lemma smallSingularSubcomplexπ_eq {X : TopCat.{w}} {ι : Type*} (U : ι → Set X) (R : C) :
    smallSingularSubcomplexπ U R = (X.smallSingularSubcomplex U).pair.chainComplexπ R :=
  (rfl)

/-- The quotient map from the chains of `X` to its chains relative to the small chains is an
epimorphism. -/
instance epi_smallSingularSubcomplexπ {X : TopCat.{w}} {ι : Type*} (U : ι → Set X) (R : C) :
    Epi (smallSingularSubcomplexπ U R) :=
  inferInstanceAs (Epi ((X.smallSingularSubcomplex U).pair.chainComplexπ R))

/-- The quotient map from the chains of `X` to its chains relative to the small chains is natural
in the coefficient object. -/
@[reassoc]
lemma smallSingularSubcomplexπ_coefficient_naturality {X : TopCat.{w}} {ι : Type*}
    (U : ι → Set X) {M N : C} (φ : M ⟶ N) :
    ((SSet.chainComplexFunctor C).map φ).app (toSSet.obj X) ≫ smallSingularSubcomplexπ U N =
      smallSingularSubcomplexπ U M ≫
        ((SSetPair.chainComplexFunctor C).map φ).app (X.smallSingularSubcomplex U).pair :=
  -- the naturality of `SSetPair.chainComplexFunctorπ`, whose source is the functor of the ambient
  -- chains of a pair, which are the chains of `X` here up to unfolding
  congrArg (fun η ↦ η.app (X.smallSingularSubcomplex U).pair)
    ((SSetPair.chainComplexFunctorπ C).naturality φ)

/-- The small chains of `X` vanish in its chains relative to them. -/
@[reassoc]
lemma chainComplexMap_ι_comp_smallSingularSubcomplexπ {X : TopCat.{w}} {ι : Type*}
    (U : ι → Set X) (R : C) :
    SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R ≫ smallSingularSubcomplexπ U R = 0 :=
  -- `SSetPair.chainComplex_condition`, whose structure map `(X.smallSingularSubcomplex U).pair.hom`
  -- is the inclusion of the small chains only up to unfolding `SSetPair.of`
  (X.smallSingularSubcomplex U).pair.chainComplex_condition R

/-- A continuous map into `X` whose image lies in a member of a family `U` of subsets induces a
chain map that vanishes in the chains of `X` relative to its singular simplices lying in some
member of `U`. -/
@[reassoc]
theorem chainComplexMap_comp_smallSingularSubcomplexπ {X Z : TopCat.{w}} {ι : Type*}
    (U : ι → Set X) {f : Z ⟶ X} {i : ι} (hf : Set.range f ⊆ U i) (R : C) :
    SSet.chainComplexMap (toSSet.map f) R ≫ smallSingularSubcomplexπ U R = 0 := by
  rw [← codRestrict_comp_ofHom_subtypeVal f (U i) (fun z ↦ hf ⟨z, rfl⟩), Functor.map_comp,
    ← toSmallSingularSubcomplex_ι U (subset_refl (U i)), SSet.chainComplexMap, Functor.map_comp,
    Functor.map_comp, Category.assoc, Category.assoc,
    chainComplexMap_ι_comp_smallSingularSubcomplexπ, comp_zero, comp_zero]

/-- `TopCat.chainComplexπ_smallSingularSubcomplexPairToUnion`, with the quotient maps written as
`TopCat.smallSingularSubcomplexπ` and `TopPair.singularChainComplexπOfSubset`, whose sources are
the chains of `X`. -/
@[reassoc]
theorem smallSingularSubcomplexπ_comp_chainComplexMap_smallSingularSubcomplexPairToUnion
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]
    {X : TopCat.{w}} (U V : Set X) (R : C) :
    smallSingularSubcomplexπ ![U, V] R ≫
        SSetPair.chainComplexMap (smallSingularSubcomplexPairToUnion U V) R =
      TopPair.singularChainComplexπOfSubset R (U ∪ V) :=
  chainComplexπ_smallSingularSubcomplexPairToUnion _ _ _

end TopCat

end
