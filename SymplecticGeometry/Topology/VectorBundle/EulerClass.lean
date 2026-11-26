/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.VectorBundle.EulerClass
public import TauCeti.AlgebraicTopology.Cohomology.DegreeZero

/-!
# Values of degree-zero Euler classes

For a class `u` of `H⁰(E, E₀; K)` of the Thom pair of a real vector bundle `E` over `B`, with
coefficients in a commutative ring `K`, the Euler class `TauCeti.eulerClass … 0 u` lies in
`H⁰(B; K)`, and so is determined by its values at the points of `B`.
`TauCeti.singularCohomologyZeroEval_eulerClass` computes the value at `b`: it is the value at the
zero vector of the image in `H⁰(E_b; K)` of the restriction of `u` to the fibre pair
`(E_b, E_b ∖ {0})`. It holds in every rank and needs no orientation.

The statement and proof adapt a step of the proof of Tau Ceti's
`TauCeti.span_singularCohomologyMap_fiberThomPairMap_eq_top_iff`
(`TauCeti/Topology/VectorBundle/Thom/RankZero.lean`), where it is proved inline for a bundle of
rank zero.

## Main results

* `TauCeti.singularCohomologyZeroEval_eulerClass`: the value of a degree-zero Euler class at a
  point is the value at the zero vector of the restriction to the fibre over it.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §9 (the Euler class).
-/

public section

open Bundle CategoryTheory MonoidalCategory

universe w

namespace TauCeti

/-- **The value of a degree-zero Euler class at a point** `b` of the base is the value at the
zero vector of the restriction of the class to the fibre pair `(E_b, E_b ∖ {0})`, read in
`H⁰(E_b; K)`. -/
theorem singularCohomologyZeroEval_eulerClass {B : Type w} [TopologicalSpace B] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
    [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] [VectorBundle ℝ F E] {K : Type w} [CommRing K]
    (u : (thomPair F E).singularCohomology (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0)
    (b : B) :
    singularCohomologyZeroEval b
        (eulerClass (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) F E 0 u) =
      singularCohomologyZeroEval
        (X := (TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).fst) (0 : E b)
        ((TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).singularCohomologyπ _ K _ 0
          (TopPair.singularCohomologyMap (fiberThomPairMap F E b) 0 u)) := by
  rw [eulerClass_def, ConcreteCategory.comp_apply, singularCohomologyZeroEval_naturality]
  -- The zero vector `0 : E b` stands for a point of the ambient space of the fibre pair, so the
  -- goal is not type-correct at the transparency of `rw`; the last steps go through `Eq.trans`.
  have h := ConcreteCategory.congr_hom (TopPair.singularCohomologyπ_naturality
    (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := 𝟙_ (ModuleCat.{w} K)) (fiberThomPairMap F E b) 0) u
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  refine Eq.trans ?_ (congrArg (singularCohomologyZeroEval _) h)
  refine Eq.trans ?_ (singularCohomologyZeroEval_naturality _ _ _).symm
  exact congrArg (singularCohomologyZeroEval · _)
    ((zeroSectionHom_apply F E b).trans (fiberThomPairMap_fst_apply F E b 0).symm)

end TauCeti

end
