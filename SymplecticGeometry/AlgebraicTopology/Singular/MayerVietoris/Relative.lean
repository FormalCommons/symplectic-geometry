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
* `TopCat.toSmallSingularSubcomplexPair`: the map of singular pairs from `(X, A)`, for `A`
  contained in a member of `U`, to `X` relative to the small chains. Tau Ceti has it as the private
  `toSmallPair` of `Singular/MayerVietoris/Relative.lean`.
* `TopCat.singularChainComplexπOfSubset_comp_chainComplexMap_toSmallSingularSubcomplexPair`: its
  chain map takes the quotient map onto `C(X, A)` to the quotient map onto the chains relative to
  the small chains.
* `TopCat.chainComplexMap_toSmallSingularSubcomplexPair_comp_smallSingularSubcomplexPairToUnion`:
  the map `C(X, U) ⟶ C(X, U ∪ V)` factors through the chains relative to the small chains.
* `TopCat.isIso_homologyMap_smallSingularSubcomplexPairToUnion`: for `U` and `V` open in `U ∪ V`,
  the homology of `X` relative to its singular simplices lying in `U` or in `V` is that of
  `(X, U ∪ V)`. Tau Ceti proves this for `U` and `V` open in `X`, in the private lemma
  `isIso_homologyMap_smallPairToUnion` of `Singular/MayerVietoris/Relative.lean`, whose proof this
  one follows.

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

/-- The map of singular pairs `(X, A) ⟶ (X, X.smallSingularSubcomplex U)` for a subset `A`
contained in a member `U i` of the family `U`: the inclusion of the singular simplices of `A` into
the small chains, and the identity on the singular simplicial set of `X`. -/
noncomputable def toSmallSingularSubcomplexPair {X : TopCat.{w}} {ι : Type*} (U : ι → Set X)
    {A : Set X} {i : ι} (h : A ⊆ U i) :
    TopPair.toSSetPair.obj (TopPair.ofSubset A) ⟶ (X.smallSingularSubcomplex U).pair :=
  SSetPair.homMk (toSmallSingularSubcomplex U h) (𝟙 _)
    ((toSmallSingularSubcomplex_ι _ _).trans (Category.comp_id _).symm)

/-- The map of singular pairs `(X, A) ⟶ (X, X.smallSingularSubcomplex U)` is the identity on the
singular simplicial set of `X`. -/
@[simp]
lemma toSmallSingularSubcomplexPair_right {X : TopCat.{w}} {ι : Type*} (U : ι → Set X)
    {A : Set X} {i : ι} (h : A ⊆ U i) :
    (toSmallSingularSubcomplexPair U h).right = 𝟙 _ :=
  (rfl)

/-- The chain map of `TopCat.toSmallSingularSubcomplexPair` takes the quotient map from the chains
of `X` onto the relative chains of `(X, A)` to the quotient map onto its chains relative to the
small chains. -/
@[reassoc]
theorem singularChainComplexπOfSubset_comp_chainComplexMap_toSmallSingularSubcomplexPair
    {X : TopCat.{w}} {ι : Type*} (U : ι → Set X) {A : Set X} {i : ι} (h : A ⊆ U i) (R : C) :
    TopPair.singularChainComplexπOfSubset R A ≫
        SSetPair.chainComplexMap (toSmallSingularSubcomplexPair U h) R =
      smallSingularSubcomplexπ U R :=
  -- the naturality of `SSetPair.chainComplexπ`, whose map on the ambient chains is that of
  -- `(toSmallSingularSubcomplexPair U h).right`, the identity
  (SSetPair.chainComplexπ_naturality R _).symm.trans
    ((congrArg (· ≫ _) (CategoryTheory.Functor.map_id _ _)).trans (Category.id_comp _))

/-- The map `C(X, U) ⟶ C(X, U ∪ V)` of relative chains factors through the chains of `X` relative
to its singular simplices lying in `U` or in `V`. -/
@[reassoc]
theorem chainComplexMap_toSmallSingularSubcomplexPair_comp_smallSingularSubcomplexPairToUnion
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]
    {X : TopCat.{w}} (U V : Set X) (R : C) :
    SSetPair.chainComplexMap
        (toSmallSingularSubcomplexPair ![U, V] (A := U) (i := 0) subset_rfl) R ≫
        SSetPair.chainComplexMap (smallSingularSubcomplexPairToUnion U V) R =
      TopPair.singularChainComplexMap (TopPair.ofSubsetMap (𝟙 X) fun _ hx ↦ Or.inl hx) R := by
  rw [← cancel_epi (TopPair.singularChainComplexπOfSubset R U),
    singularChainComplexπOfSubset_comp_chainComplexMap_toSmallSingularSubcomplexPair_assoc ![U, V]
      (A := U) (i := 0) subset_rfl R,
    smallSingularSubcomplexπ_comp_chainComplexMap_smallSingularSubcomplexPairToUnion]
  refine Eq.trans ?_ (TopPair.singularChainComplexπOfSubset_naturality R (𝟙 X) _)
  simp

/-- For `U` and `V` open in `U ∪ V`, the comparison of the chains of `X` relative to its singular
simplices lying in `U` or in `V` with the relative chains of `(X, U ∪ V)` is an isomorphism on
homology, by the small-chain theorem for the cover of `U ∪ V` by `U` and `V`. -/
theorem isIso_homologyMap_smallSingularSubcomplexPairToUnion {C : Type u} [Category.{v} C]
    [HasCoproducts.{w} C] [Abelian C] {X : TopCat.{w}} (U V : Set X) (R : C)
    (hU : IsOpen ((↑) ⁻¹' U : Set ↥(U ∪ V))) (hV : IsOpen ((↑) ⁻¹' V : Set ↥(U ∪ V))) (n : ℕ) :
    IsIso (SSetPair.homologyMap (smallSingularSubcomplexPairToUnion U V) R n) := by
  have : QuasiIso (SSet.chainComplexMap (smallSingularSubcomplexPairToUnion U V).left R) := by
    rw [smallSingularSubcomplexPairToUnion_left]
    exact quasiIso_chainComplexMap_smallSingularSubcomplexToUnion R U V hU hV
  have : IsIso (SSet.chainComplexMap (smallSingularSubcomplexPairToUnion U V).right R) := by
    rw [chainComplexMap_smallSingularSubcomplexPairToUnion_right]
    exact IsIso.id _
  have : QuasiIso (SSet.chainComplexMap (smallSingularSubcomplexPairToUnion U V).right R) :=
    quasiIso_of_isIso _
  exact SSetPair.isIso_homologyMap_of_quasiIso _ R n

end TopCat

end
