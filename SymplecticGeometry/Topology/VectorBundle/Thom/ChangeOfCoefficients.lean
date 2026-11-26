/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cohomology.PairChangeOfCoefficients
public import TauCeti.Algebra.Module.Equiv.SpanSingleton
public import TauCeti.Topology.VectorBundle.EulerClass

/-!
# Thom classes and Euler classes under a change of coefficients

Let `E → B` be a real vector bundle with Thom pair `(E, E₀)`. The three changes of coefficients
of the cohomology of a pair (`PairChangeOfCoefficients.lean`) — of chain coefficients along an
isomorphism, of cochain values along an isomorphism, and of the linear structure of the category
of coefficients — carry Thom classes (`TauCeti.IsThomClass`) to Thom classes, since they commute
with the restriction to each fibre and are isomorphisms. Their combination below also commutes
with the Euler class map `TauCeti.eulerClass`, since it commutes with the map to absolute
cohomology and with pull-backs.

So a Thom class in one convention of coefficients gives one in another, with the corresponding
Euler class. This is how Tau Ceti's integral Thom class of an oriented bundle, with chain
coefficients and values `ULift ℤ`, becomes a Thom class with coefficients `ℤ`, to which the Thom
isomorphism `TauCeti.bijective_thomMap_of_compactSpace` applies. Over a base in `Type`, the
three changes combine into the linear equivalence `TopPair.uliftIntegralCohomologyEquiv`, which
carries a class with coefficients `ULift ℤ` along `TauCeti.uliftIntIso : ULift ℤ ≅ ℤ` to the
coefficients of `TauCeti.thomMap`, and so also carries Thom classes to Thom classes.

## Main results

* `TauCeti.IsThomClass.singularCohomologyChainCoefficientMap`,
  `TauCeti.IsThomClass.singularCohomologyValueMap`,
  `TauCeti.IsThomClass.singularCohomologyLinearCongr`: the changes of coefficients preserve Thom
  classes, and `TauCeti.IsThomClass.uliftIntegralCohomologyEquiv` for their combination.
* `TauCeti.eulerClass_uliftIntegralCohomologyEquiv`: the combination commutes with the Euler
  class, a consequence of `TopPair.singularCohomologyπ_uliftIntegralCohomologyEquiv` and the
  naturality of the conversions for spaces.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §9 and §10.
-/

public section

open Bundle CategoryTheory Limits Module

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]
  {B : Type w} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E]

section ThomClass

variable [∀ b, Zero (E b)]

/-- **A change of chain coefficients along an isomorphism carries Thom classes to Thom
classes.** -/
theorem IsThomClass.singularCohomologyChainCoefficientMap {R R' : C} {k : Type*} [Ring k]
    [Linear k C] {M : C} (e : R' ≅ R)
    {u : (thomPair F E).singularCohomology R k M (finrank ℝ F)} (hu : IsThomClass F E u) :
    IsThomClass F E
      ((thomPair F E).singularCohomologyChainCoefficientMap k M e.hom (finrank ℝ F) u) := by
  refine isThomClass_iff.2 ⟨(isThomClass_iff.1 hu).1, fun b ↦ ?_⟩
  rw [← TopPair.singularCohomologyChainCoefficientMap_naturality_apply,
    ← TopPair.singularCohomologyChainCoefficientIso_hom]
  exact (Iso.toLinearEquiv _).span_singleton_apply_eq_top_iff.2 ((isThomClass_iff.1 hu).2 b)

/-- **A change of cochain values along an isomorphism carries Thom classes to Thom classes.** -/
theorem IsThomClass.singularCohomologyValueMap {R : C} {k : Type*} [Ring k] [Linear k C]
    {M M' : C} (e : M ≅ M')
    {u : (thomPair F E).singularCohomology R k M (finrank ℝ F)} (hu : IsThomClass F E u) :
    IsThomClass F E
      ((thomPair F E).singularCohomologyValueMap R k e.hom (finrank ℝ F) u) := by
  refine isThomClass_iff.2 ⟨(isThomClass_iff.1 hu).1, fun b ↦ ?_⟩
  rw [← TopPair.singularCohomologyValueMap_naturality_apply,
    ← TopPair.singularCohomologyValueIso_hom]
  exact (Iso.toLinearEquiv _).span_singleton_apply_eq_top_iff.2 ((isThomClass_iff.1 hu).2 b)

/-- **A change of the linear structure of the coefficients carries Thom classes to Thom
classes.** -/
theorem IsThomClass.singularCohomologyLinearCongr {R M : C} {k : Type*} [Ring k]
    {L₁ L₂ : Linear k C} (e : L₁ = L₂)
    {u : @TopPair.singularCohomology C _ _ _ (thomPair F E) R k _ L₁ M (finrank ℝ F)}
    (hu : @IsThomClass C _ _ _ R k _ L₁ M B _ F _ E _ _ _ _ _ _ u) :
    @IsThomClass C _ _ _ R k _ L₂ M B _ F _ E _ _ _ _ _ _
      (TopPair.singularCohomologyLinearCongr e (thomPair F E) R M (finrank ℝ F) u) := by
  subst e
  rwa [TopPair.singularCohomologyLinearCongr_refl, LinearEquiv.refl_apply]

end ThomClass

section Integral

variable {B : Type} {F : Type*} {E : B → Type} [TopologicalSpace B] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E] [∀ b, Zero (E b)]

/-- **A Thom class with coefficients `ULift ℤ` gives one with coefficients `ℤ`**: if `U` is a
Thom class, so is its image under `TopPair.uliftIntegralCohomologyEquiv`, for the structure
`ModuleCat.instLinear`. -/
theorem IsThomClass.uliftIntegralCohomologyEquiv
    {U : (thomPair F E).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
      (ModuleCat.of ℤ (ULift.{0} ℤ)) (finrank ℝ F)} (hU : IsThomClass F E U) :
    @IsThomClass _ _ _ _ (ModuleCat.of ℤ ℤ) ℤ _ ModuleCat.instLinear (ModuleCat.of ℤ ℤ) B _ F _ E
      _ _ _ _ _ _ ((thomPair F E).uliftIntegralCohomologyEquiv (finrank ℝ F) U) := by
  rw [TopPair.uliftIntegralCohomologyEquiv_apply]
  exact ((hU.singularCohomologyValueMap uliftIntIso).singularCohomologyChainCoefficientMap
    uliftIntIso.symm).singularCohomologyLinearCongr _

end Integral

section IntegralEulerClass

variable {B : Type} {F : Type*} {E : B → Type} [TopologicalSpace B] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]

/-- **The Euler class commutes with `TopPair.uliftIntegralCohomologyEquiv`**: the Euler class, for
the structure `ModuleCat.instLinear`, of the image of `u ∈ Hⁿ(E, E₀; ULift ℤ)` under
`TopPair.uliftIntegralCohomologyEquiv` is the Euler class of `u`, read in integral cohomology
through `TopCat.uliftIntegralCohomologyIso`, sent by Tau Ceti's `TopCat.integralCohomologyEquiv`
to cohomology with chain coefficients and values `ℤ`. -/
theorem eulerClass_uliftIntegralCohomologyEquiv (n : ℕ)
    (u : (thomPair F E).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
      (ModuleCat.of ℤ (ULift.{0} ℤ)) n) :
    @eulerClass _ _ _ _ (ModuleCat.of ℤ ℤ) ℤ _ ModuleCat.instLinear (ModuleCat.of ℤ ℤ) B _ F _ _ E
        _ _ _ _ _ _ n ((thomPair F E).uliftIntegralCohomologyEquiv n u) =
      (TopCat.of B).integralCohomologyEquiv n
        ((TopCat.uliftIntegralCohomologyIso _ n).hom (eulerClass _ ℤ _ F E n u)) := by
  simp only [eulerClass_def, ConcreteCategory.comp_apply]
  rw [TopPair.singularCohomologyπ_uliftIntegralCohomologyEquiv,
    ← TopCat.integralCohomologyEquiv_naturality,
    ← TopCat.uliftIntegralCohomologyIso_naturality_apply]

end IntegralEulerClass

end TauCeti

end
