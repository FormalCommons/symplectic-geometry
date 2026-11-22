/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Relative

/-!
# Change of coefficients in the singular homology of a pair

A morphism of coefficients `φ : R ⟶ R'` induces a map of relative singular chains
`C(X, A; R) ⟶ C(X, A; R')`, the component of the bifunctor `SSetPair.chainComplexFunctor`, and
hence a map `Hₙ(X, A; R) ⟶ Hₙ(X, A; R')`. This map commutes with the maps induced by maps of
pairs (`TopPair.singularHomologyMap_coefficient_naturality`). It is the homology counterpart of
`TopPair.singularCohomologyChainCoefficientMap_naturality`
(`SymplecticGeometry/AlgebraicTopology/Cohomology/PairChangeOfCoefficients.lean`), and its proof
is that of the cohomology statement, without the dual.
-/

public section

open CategoryTheory Limits HomologicalComplex

universe w v u

namespace TopPair

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  [CategoryWithHomology C]

/-- The change of coefficients along `φ : R ⟶ R'` commutes with the map on relative singular
homology induced by a map of pairs `f : P ⟶ P'`. -/
@[reassoc]
theorem singularHomologyMap_coefficient_naturality {P P' : TopPair.{w}} (f : P ⟶ P') {R R' : C}
    (φ : R ⟶ R') (n : ℕ) :
    homologyMap (((SSetPair.chainComplexFunctor C).map φ).app (toSSetPair.obj P)) n ≫
        TopPair.singularHomologyMap f R' n =
      TopPair.singularHomologyMap f R n ≫
        homologyMap (((SSetPair.chainComplexFunctor C).map φ).app (toSSetPair.obj P')) n :=
  (homologyMap_comp _ _ n).symm.trans <| (congrArg (homologyMap · n)
    (((SSetPair.chainComplexFunctor C).map φ).naturality (toSSetPair.map f)).symm).trans
      (homologyMap_comp _ _ n)

end TopPair

end
