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
with the restriction to each fibre and are isomorphisms; and they commute with the Euler class map
`TauCeti.eulerClass`, since they commute with the map to absolute cohomology and with pull-backs.

So a Thom class in one convention of coefficients gives one in another, with the corresponding
Euler class. This is how Tau Ceti's integral Thom class of an oriented bundle, with chain
coefficients and values `ULift ℤ`, becomes a Thom class with coefficients `ℤ`, to which the Thom
isomorphism `TauCeti.bijective_thomMap_of_compactSpace` applies.

## Main results

* `TauCeti.IsThomClass.singularCohomologyChainCoefficientMap`,
  `TauCeti.IsThomClass.singularCohomologyValueMap`,
  `TauCeti.IsThomClass.singularCohomologyLinearCongr`: the changes of coefficients preserve Thom
  classes.
* `TauCeti.eulerClass_comp_singularCohomologyChainCoefficientMap`,
  `TauCeti.eulerClass_comp_singularCohomologyValueMap`,
  `TauCeti.singularCohomologyLinearCongr_eulerClass`: they commute with the Euler class.

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
  rw [← ConcreteCategory.comp_apply, ← TopPair.singularCohomologyChainCoefficientMap_naturality,
    ConcreteCategory.comp_apply, ← TopPair.singularCohomologyChainCoefficientIso_hom]
  exact (Iso.toLinearEquiv _).span_singleton_apply_eq_top_iff.2 ((isThomClass_iff.1 hu).2 b)

/-- **A change of cochain values along an isomorphism carries Thom classes to Thom classes.** -/
theorem IsThomClass.singularCohomologyValueMap {R : C} {k : Type*} [Ring k] [Linear k C]
    {M M' : C} (e : M ≅ M')
    {u : (thomPair F E).singularCohomology R k M (finrank ℝ F)} (hu : IsThomClass F E u) :
    IsThomClass F E
      ((thomPair F E).singularCohomologyValueMap R k e.hom (finrank ℝ F) u) := by
  refine isThomClass_iff.2 ⟨(isThomClass_iff.1 hu).1, fun b ↦ ?_⟩
  rw [← ConcreteCategory.comp_apply, ← TopPair.singularCohomologyValueMap_naturality,
    ConcreteCategory.comp_apply, ← TopPair.singularCohomologyValueIso_hom]
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

section EulerClass

variable [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [VectorBundle ℝ F E]

/-- **The Euler class commutes with a change of chain coefficients.** -/
@[reassoc]
theorem eulerClass_comp_singularCohomologyChainCoefficientMap {R R' : C} (k : Type*) [Ring k]
    [Linear k C] (M : C) (f : R' ⟶ R) (n : ℕ) :
    eulerClass R k M F E n ≫ (TopCat.of B).singularCohomologyChainCoefficientMap k M f n =
      (thomPair F E).singularCohomologyChainCoefficientMap k M f n ≫ eulerClass R' k M F E n := by
  rw [eulerClass_def, eulerClass_def, Category.assoc,
    TopCat.singularCohomologyChainCoefficientMap_naturality,
    TopPair.singularCohomologyπ_singularCohomologyChainCoefficientMap_assoc]

/-- **The Euler class commutes with a change of cochain values.** -/
@[reassoc]
theorem eulerClass_comp_singularCohomologyValueMap (R : C) (k : Type*) [Ring k] [Linear k C]
    {M M' : C} (g : M ⟶ M') (n : ℕ) :
    eulerClass R k M F E n ≫ (TopCat.of B).singularCohomologyValueMap R k g n =
      (thomPair F E).singularCohomologyValueMap R k g n ≫ eulerClass R k M' F E n := by
  rw [eulerClass_def, eulerClass_def, Category.assoc,
    TopCat.singularCohomologyValueMap_naturality,
    TopPair.singularCohomologyπ_singularCohomologyValueMap_assoc]

/-- **The Euler class commutes with a change of the linear structure of the coefficients.** -/
theorem singularCohomologyLinearCongr_eulerClass {k : Type*} [Ring k] {L₁ L₂ : Linear k C}
    (e : L₁ = L₂) (R M : C) (n : ℕ)
    (u : @TopPair.singularCohomology C _ _ _ (thomPair F E) R k _ L₁ M n) :
    TopCat.singularCohomologyLinearCongr e (TopCat.of B) R M n
        (@eulerClass C _ _ _ R k _ L₁ M B _ F _ _ E _ _ _ _ _ _ n u) =
      @eulerClass C _ _ _ R k _ L₂ M B _ F _ _ E _ _ _ _ _ _ n
        (TopPair.singularCohomologyLinearCongr e (thomPair F E) R M n u) := by
  subst e
  simp only [TopPair.singularCohomologyLinearCongr_refl, TopCat.singularCohomologyLinearCongr_refl,
    LinearEquiv.refl_apply]

end EulerClass

end TauCeti

end
