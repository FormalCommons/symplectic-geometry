/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Monoidal.Unit
public import TauCeti.AlgebraicTopology.Cohomology.IntegralCup
public import TauCeti.AlgebraicTopology.Cohomology.Local.Cross
public import TauCeti.AlgebraicTopology.Cohomology.Local.Orientation
public import TauCeti.CategoryTheory.Monoidal.Preadditive
public import TauCeti.LinearAlgebra.Dimension.Prod
public import TauCeti.LinearAlgebra.Orientation.Prod
import SymplecticGeometry.AlgebraicTopology.Cohomology.Cup.RelativeKronecker
import SymplecticGeometry.AlgebraicTopology.Cohomology.IntegralCohomologyULift
import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Orientation.Cross.Sign

/-!
# The product of the local cohomology generators selected by two orientations

Let `F₁` and `F₂` be real normed spaces of dimensions `m + 1` and `n + 1`, with orientations
`ω₁` and `ω₂`. Each orientation selects a generator of the integral local cohomology at the
origin (`Orientation.localCohomologyClass`), the class pairing to one with the local orientation
it selects. Tau Ceti's product `TauCeti.complZeroPairCross` of classes of the pairs
`(F, F ∖ {0})`, with chain coefficients and cochain values `ULift ℤ` multiplied by
`TauCeti.integralCoeffComul` and `ModuleCat.uliftTensorSelfIso ℤ`, as in the cup product of
integral classes with values in `ULift ℤ` (`TopCat.uliftIntegralCohomologyIso_singularCup`), sends
the two generators to `(-1) ^ ((m + 1) * (n + 1))` times the generator selected by the product
orientation `ω₁.prod ω₂`, reindexed to `Fin (d + 1)`
(`Orientation.complZeroPairCross_localCohomologyClass`).

The product of the generators pairs with the cross product of the two local orientations to one
(`TauCeti.singularKronecker_complZeroPairCross_int`, in `Cohomology/Cup/RelativeKronecker.lean`,
whose hypothesis is `SymplecticGeometry.localHomologyCross_comp_homologyMap_uliftTensorSelfIso_inv`
with the diagonal `TauCeti.integralCoeffComul` as the inverse of the multiplication),
and that cross product is `(-1) ^ ((m + 1) * (n + 1))` times the local orientation selected by
`ω₁.prod ω₂` (`TauCeti.LocalOrientation.coe_cross_localOrientation_eq_neg_one_pow_smul`, in
`Singular/LocalHomology/Orientation/Cross/Sign.lean`). The sign is `1` when one of the two
dimensions is even, as for complex vector spaces.

The integral cohomology here takes the `ℤ`-linear structure that `ModuleCat ℤ` has as a
preadditive category, as Tau Ceti's integral cup product does
(`CategoryTheory.MonoidalPreadditive.monoidalLinearInt`).

## Main results

* `Orientation.complZeroPairCross_localCohomologyClass`: the product of the generators selected
  by `ω₁` and `ω₂` is `(-1) ^ ((m + 1) * (n + 1))` times the generator selected by `ω₁.prod ω₂`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.2 (cross products) and Section 3.3 (local orientations).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, Sections 9 and 10.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory Module

attribute [local instance] MonoidalPreadditive.monoidalLinearInt

namespace Orientation

open TauCeti SymplecticGeometry

variable {F₁ F₂ : Type} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] {m n d : ℕ}

/-- **The product of the local cohomology generators selected by two orientations.** For
orientations `ω₁` of `F₁` and `ω₂` of `F₂`, of dimensions `m + 1` and `n + 1`, the product
`TauCeti.complZeroPairCross` of the generators of `Hᵐ⁺¹(F₁, F₁ ∖ {0}; ℤ)` and
`Hⁿ⁺¹(F₂, F₂ ∖ {0}; ℤ)` that they select, with the diagonal and the multiplication of `ULift ℤ`, is
`(-1) ^ ((m + 1) * (n + 1))` times the generator of `Hᵈ⁺¹(F₁ × F₂, (F₁ × F₂) ∖ {0}; ℤ)` selected by
the product orientation `ω₁.prod ω₂`, reindexed by `Fin (m + 1 + (n + 1)) ≃ Fin (d + 1)`. -/
theorem complZeroPairCross_localCohomologyClass (hF₁ : finrank ℝ F₁ = m + 1)
    (hF₂ : finrank ℝ F₂ = n + 1) (h : m + 1 + (n + 1) = d + 1) (ω₁ : Orientation ℝ F₁ (Fin (m + 1)))
    (ω₂ : Orientation ℝ F₂ (Fin (n + 1))) :
    complZeroPairCross ℤ F₁ F₂ integralCoeffComul (ModuleCat.uliftTensorSelfIso ℤ).hom
        (m + 1) (n + 1) (d + 1) h (ω₁.localCohomologyClass hF₁) (ω₂.localCohomologyClass hF₂) =
      haveI := FiniteDimensional.of_finrank_eq_succ hF₁
      haveI := FiniteDimensional.of_finrank_eq_succ hF₂
      (-1 : ℤ) ^ ((m + 1) * (n + 1)) •
        (Orientation.reindex ℝ (F₁ × F₂) (finCongr h) (ω₁.prod ω₂ hF₁ hF₂)).localCohomologyClass
          (finrank_prod_eq_succ hF₁ hF₂ h) := by
  have := FiniteDimensional.of_finrank_eq_succ hF₁
  have := FiniteDimensional.of_finrank_eq_succ hF₂
  have hs : ((-1 : ℤ) ^ ((m + 1) * (n + 1))) * (-1 : ℤ) ^ ((m + 1) * (n + 1)) = 1 := by
    simp [← mul_pow]
  have hP : ((Orientation.reindex ℝ (F₁ × F₂) (finCongr h) (ω₁.prod ω₂ hF₁ hF₂)).localOrientation
      (finrank_prod_eq_succ hF₁ hF₂ h)).val = (-1 : ℤ) ^ ((m + 1) * (n + 1)) •
        (LocalOrientation.cross hF₁ hF₂ h (ω₁.localOrientation hF₁)
          (ω₂.localOrientation hF₂)).val := by
    rw [LocalOrientation.coe_cross_localOrientation_eq_neg_one_pow_smul, smul_smul, hs, one_smul]
  have hz := singularKronecker_complZeroPairCross_int F₁ F₂ integralCoeffComul
    (ModuleCat.uliftTensorSelfIso ℤ).hom h (ω₁.localCohomologyClass hF₁)
    (ω₂.localCohomologyClass hF₂) (ω₁.localOrientation hF₁).val (ω₂.localOrientation hF₂).val
    (LocalOrientation.cross hF₁ hF₂ h (ω₁.localOrientation hF₁) (ω₂.localOrientation hF₂)).val (by
      rw [integralCoeffComul_eq_uliftTensorSelfIso_inv, LocalOrientation.coe_cross]
      exact localHomologyCross_comp_homologyMap_uliftTensorSelfIso_inv_apply (0 : F₁) (0 : F₂) _ _ _
        h _)
  have h1 := (eq_localCohomologyClass_iff _ (finrank_prod_eq_succ hF₁ hF₂ h)
    ((-1 : ℤ) ^ ((m + 1) * (n + 1)) • complZeroPairCross ℤ F₁ F₂ integralCoeffComul
      (ModuleCat.uliftTensorSelfIso ℤ).hom (m + 1) (n + 1) (d + 1) h
      (ω₁.localCohomologyClass hF₁) (ω₂.localCohomologyClass hF₂))).2 (by
    rw [hP, map_zsmul, map_zsmul, ModuleCat.hom_zsmul, LinearMap.smul_apply, smul_smul, hs,
      one_smul]
    refine hz.trans ?_
    rw [kronecker_localCohomologyClass, kronecker_localCohomologyClass]
    -- `1 ⊗ 1 ↦ 1 * 1`; the lemma is stated for `ModuleCat.Hom.hom`, the goal through
    -- `ConcreteCategory.hom`, which agree by definition.
    exact (ModuleCat.uliftTensorSelfIso_hom_tmul ℤ 1 1).trans (congrArg ULift.up (mul_one 1)))
  rw [← h1, smul_smul, hs, one_smul]

end Orientation
