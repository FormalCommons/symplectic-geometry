/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Kronecker
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.System

/-!
# The Kronecker pairing with the local point class

For a space `X`, a set `S ⊆ X` and a point `x`, Tau Ceti's `TauCeti.localHomologyPointClass R S x`
is the class of the point `x` in the relative homology `H₀(X, X ∖ S; R)`, the image of the
absolute point class `TauCeti.singularHomology₀Section R x` under the quotient map. Pairing a
relative class `a ∈ H⁰(X, X ∖ S; R, M)` with it is pairing the image of `a` in the absolute
cohomology `H⁰(X; R, M)` with the absolute point class
(`TauCeti.localHomologyPointClass_comp_singularKronecker`).

## Main results

* `TauCeti.localHomologyPointClass_comp_singularKronecker`: the Kronecker pairing of a relative
  degree-zero class with the local point class.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1.
-/

public section

open CategoryTheory Limits

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  (k : Type*) [Ring k] [Linear k C] {M : C} {X : Type w} [TopologicalSpace X]

/-- Pairing a relative class `a ∈ H⁰(X, X ∖ S; R, M)` with the local point class of `x` is pairing
the image of `a` in `H⁰(X; R, M)` with the absolute point class of `x`. -/
theorem localHomologyPointClass_comp_singularKronecker (S : Set X) (x : X)
    (a : (TopPair.ofSubset (Sᶜ : Set (TopCat.of X))).singularCohomology R k M 0) :
    localHomologyPointClass R S x ≫
        (TopPair.ofSubset (Sᶜ : Set (TopCat.of X))).singularKronecker k 0 a =
      singularHomology₀Section R (X := (TopPair.ofSubset (Sᶜ : Set (TopCat.of X))).fst) x ≫
        (TopPair.ofSubset (Sᶜ : Set (TopCat.of X))).fst.singularKronecker k 0
          ((TopPair.ofSubset (Sᶜ : Set (TopCat.of X))).singularCohomologyπ R k M 0 a) := by
  rw [TopPair.singularKronecker_singularCohomologyπ, localHomologyPointClass_def]
  -- The point class lands in zeroth homology named through `singularHomologyFunctor`, the
  -- relative quotient starts from the homology of the singular simplicial set; the two agree only
  -- after unfolding, so associativity is applied as a term rather than rewritten.
  exact Category.assoc _ _ _

end TauCeti
