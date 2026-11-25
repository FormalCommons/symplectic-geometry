/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cohomology.PairChangeOfCoefficients
public import TauCeti.Algebra.Module.Equiv.SpanSingleton
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass
public import TauCeti.CategoryTheory.Linear.Int
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
isomorphism `TauCeti.bijective_thomMap_of_compactSpace` applies. Over a base in `Type`, the
three changes combine into `TauCeti.intThomClass`, which carries a class with coefficients
`ULift ℤ` along `TauCeti.uliftIntIso : ULift ℤ ≅ ℤ` to the coefficients of `TauCeti.thomMap`;
this is the conversion that the proof of the library's `TauCeti.bijective_integralCup_eulerClass`
(`Thom/CupEulerClass.lean`) makes.

## Main definitions

* `TauCeti.intThomClass`: a class of the Thom pair with coefficients `ULift ℤ`, carried to
  coefficients `ℤ` with the linear structure `ModuleCat.instLinear`.

## Main results

* `TauCeti.IsThomClass.singularCohomologyChainCoefficientMap`,
  `TauCeti.IsThomClass.singularCohomologyValueMap`,
  `TauCeti.IsThomClass.singularCohomologyLinearCongr`: the changes of coefficients preserve Thom
  classes, and `TauCeti.IsThomClass.intThomClass` for their combination.
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

variable {B : Type} {F : Type*} {E : B → Type} [TopologicalSpace (TotalSpace F E)]
  [∀ b, Zero (E b)] {n : ℕ}

/-- **A class of the Thom pair carried to coefficients `ℤ`.** A class `U ∈ Hⁿ(E, E₀; ULift ℤ)`,
with chain coefficients and values `ULift ℤ` and the `ℤ`-linear structure of `ModuleCat ℤ` as a
preadditive category, carried along `ULift ℤ ≅ ℤ` (`TauCeti.uliftIntIso`) by the change of values
and of chain coefficients to chain coefficients and values `ℤ`, with the structure
`ModuleCat.instLinear` that the Thom map `TauCeti.thomMap` takes. -/
noncomputable def intThomClass
    (U : (thomPair F E).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
      (ModuleCat.of ℤ (ULift.{0} ℤ)) n) :
    @TopPair.singularCohomology (ModuleCat.{0} ℤ) _ _ _ (thomPair F E) (ModuleCat.of ℤ ℤ) ℤ _
      ModuleCat.instLinear (ModuleCat.of ℤ ℤ) n :=
  TopPair.singularCohomologyLinearCongr (Subsingleton.elim _ _) (thomPair F E) _ _ _
    ((thomPair F E).singularCohomologyChainCoefficientMap ℤ _ uliftIntIso.inv _
      ((thomPair F E).singularCohomologyValueMap _ ℤ uliftIntIso.hom _ U))

/-- `TauCeti.intThomClass`, unfolded. -/
theorem intThomClass_def
    (U : (thomPair F E).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
      (ModuleCat.of ℤ (ULift.{0} ℤ)) n) :
    intThomClass U =
      TopPair.singularCohomologyLinearCongr (Subsingleton.elim _ _) (thomPair F E) _ _ _
        ((thomPair F E).singularCohomologyChainCoefficientMap ℤ _ uliftIntIso.inv _
          ((thomPair F E).singularCohomologyValueMap _ ℤ uliftIntIso.hom _ U)) :=
  (rfl)

/-- `TauCeti.intThomClass` is additive. -/
@[simp]
theorem intThomClass_add
    (U V : (thomPair F E).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
      (ModuleCat.of ℤ (ULift.{0} ℤ)) n) :
    intThomClass (U + V) = intThomClass U + intThomClass V := by
  simp only [intThomClass_def, map_add]

/-- `TauCeti.intThomClass` commutes with negation. -/
@[simp]
theorem intThomClass_neg
    (U : (thomPair F E).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
      (ModuleCat.of ℤ (ULift.{0} ℤ)) n) :
    intThomClass (-U) = -intThomClass U := by
  simp only [intThomClass_def, map_neg]

/-- **A Thom class with coefficients `ULift ℤ` gives one with coefficients `ℤ`**: if `U` is a
Thom class, so is `TauCeti.intThomClass U`, for the structure `ModuleCat.instLinear`. -/
theorem IsThomClass.intThomClass [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
    {U : (thomPair F E).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
      (ModuleCat.of ℤ (ULift.{0} ℤ)) (finrank ℝ F)} (hU : IsThomClass F E U) :
    @IsThomClass _ _ _ _ (ModuleCat.of ℤ ℤ) ℤ _ ModuleCat.instLinear (ModuleCat.of ℤ ℤ) B _ F _ E
      _ _ _ _ _ _ (TauCeti.intThomClass U) :=
  ((hU.singularCohomologyValueMap uliftIntIso).singularCohomologyChainCoefficientMap
    uliftIntIso.symm).singularCohomologyLinearCongr _

end Integral

section EulerClass

variable [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [VectorBundle ℝ F E]

/-- **The Euler class commutes with a change of chain coefficients.** -/
@[reassoc, elementwise]
theorem eulerClass_comp_singularCohomologyChainCoefficientMap {R R' : C} (k : Type*) [Ring k]
    [Linear k C] (M : C) (f : R' ⟶ R) (n : ℕ) :
    eulerClass R k M F E n ≫ (TopCat.of B).singularCohomologyChainCoefficientMap k M f n =
      (thomPair F E).singularCohomologyChainCoefficientMap k M f n ≫ eulerClass R' k M F E n := by
  rw [eulerClass_def, eulerClass_def, Category.assoc,
    TopCat.singularCohomologyChainCoefficientMap_naturality,
    TopPair.singularCohomologyπ_singularCohomologyChainCoefficientMap_assoc]

/-- **The Euler class commutes with a change of cochain values.** -/
@[reassoc, elementwise]
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
