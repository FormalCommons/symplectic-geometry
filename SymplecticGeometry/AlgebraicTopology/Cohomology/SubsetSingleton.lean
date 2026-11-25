/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Kronecker
public import TauCeti.AlgebraicTopology.Cohomology.Point
public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Basic
public import TauCeti.Topology.Homotopy.LusternikSchnirelmann.Basic

/-!
# Cohomology of a space relative to a point

For a space `X` and a point `x`, this file proves two facts about the relative singular
cohomology `Hⁿ(X, {x})`.

* `TopPair.surjective_singularCohomologyπ_ofSubset_singleton`: in positive degrees every class of
  `Hⁿ(X)` lifts to `Hⁿ(X, {x})`, since the inclusion of a point is nullhomotopic.
* `GenLoop.singularKronecker_singularCohomologyMap_toCubeBoundaryPairHom`: for a generalized loop
  `γ : (Iⁿ⁺¹, ∂Iⁿ⁺¹) ⟶ (X, {x})` and a class `α ∈ Hⁿ⁺¹(X, {x})`, the pull-back `γ^* α` takes on
  the generator of `Hₙ₊₁(Iⁿ⁺¹, ∂Iⁿ⁺¹)` the value of the image of `α` in `Hⁿ⁺¹(X)` on the Hurewicz
  class of `γ`. This follows from naturality of the Kronecker pairing and its comparison with the
  absolute pairing.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.1 (the Kronecker
  pairing) and Section 4.2 (the Hurewicz map).
-/

public section

open CategoryTheory Limits AlgebraicTopology TauCeti
open scoped Topology.Homotopy

universe w v u

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]
  {R : C} {k : Type*} [Ring k] [Linear k C] {M : C}

namespace TopPair

/-- In positive degrees, every class of `Hⁿ(X)` is the image of a class of `Hⁿ(X, {x})`. -/
theorem surjective_singularCohomologyπ_ofSubset_singleton {X : TopCat.{w}} (x : X) {n : ℕ}
    (hn : n ≠ 0) :
    Function.Surjective ((TopPair.ofSubset ({x} : Set X)).singularCohomologyπ R k M n) :=
  (ModuleCat.epi_iff_surjective _).1 (TopPair.epi_singularCohomologyπ_of_nullhomotopic _
    (nullhomotopic_subtypeVal_of_subset_singleton subset_rfl) hn)

end TopPair

namespace GenLoop

/-- The pull-back of a class `α ∈ Hⁿ⁺¹(X, {x})` along a generalized loop
`γ : (Iⁿ⁺¹, ∂Iⁿ⁺¹) ⟶ (X, {x})` takes on the generator of `Hₙ₊₁(Iⁿ⁺¹, ∂Iⁿ⁺¹; R) ≅ R` the value of
the image of `α` in `Hⁿ⁺¹(X)` on the Hurewicz class of `γ`. -/
theorem singularKronecker_singularCohomologyMap_toCubeBoundaryPairHom {X : Type w}
    [TopologicalSpace X] {x : X} {n : ℕ} (γ : Ω^ (Fin (n + 1)) X x)
    (α : (TopPair.ofSubset ({x} : Set (TopCat.of X))).singularCohomology R k M (n + 1)) :
    (singularHomologyCubeBoundaryPairIso R (n + 1)).inv ≫
        (cubeBoundaryPair.{w} (n + 1)).singularKronecker k (n + 1)
          (TopPair.singularCohomologyMap (toCubeBoundaryPairHom γ) (n + 1) α) =
      hurewicz R γ ≫ (TopCat.of X).singularKronecker k (n + 1)
        ((TopPair.ofSubset ({x} : Set (TopCat.of X))).singularCohomologyπ R k M (n + 1) α) := by
  rw [TopPair.singularKronecker_naturality,
    ← hurewicz_comp_singularHomologyIsoOfSubsetSingleton_hom_assoc,
    singularHomologyIsoOfSubsetSingleton_hom]
  -- `exact` rather than `rw`: the source of `singularHomologyπ` is the homology of the singular
  -- simplicial set, which is the absolute singular homology only up to unfolding.
  exact congrArg (hurewicz R γ ≫ ·)
    ((TopPair.ofSubset _).singularKronecker_singularCohomologyπ k (n + 1) α).symm

end GenLoop

end
