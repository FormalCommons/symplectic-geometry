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

## Main results

* `TopCat.smallSingularSubcomplexπ_relativeAlexanderWhitneyDiagonal`: the relative
  Alexander–Whitney diagonal after the quotient map to the chains relative to the small chains is
  the Alexander–Whitney diagonal of `X` followed by the tensor product of the quotient maps to the
  chains of `(X, U)` and of `(X, V)`.

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

end TopCat

end
