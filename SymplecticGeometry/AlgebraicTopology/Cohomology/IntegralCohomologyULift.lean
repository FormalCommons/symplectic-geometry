/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cohomology.ChangeOfValues
public import SymplecticGeometry.AlgebraicTopology.Cohomology.LinearCongr
public import TauCeti.AlgebraicTopology.Cohomology.DegreeZero
public import TauCeti.AlgebraicTopology.Cohomology.IntegralCup
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass
public import TauCeti.Algebra.Category.ModuleCat.Monoidal.Unit
public import TauCeti.CategoryTheory.Linear.Int
import all TauCeti.AlgebraicTopology.Cohomology.IntegralCup

/-!
# Integral cohomology with values in `ULift ℤ`

Tau Ceti writes the Euler class of a complex vector bundle (`TauCeti.complexEulerClass`) in
singular cohomology with chain coefficients and cochain values both `ULift ℤ`, while its integral
cohomology `TopCat.integralCohomology` and integral cup product `TopCat.integralCup` take cochain
values in `ℤ`. This file identifies the two.

The change of cochain values `TopCat.singularCohomologyValueIso` along
`TauCeti.uliftIntIso : ULift ℤ ≅ ℤ` gives
`TopCat.uliftIntegralCohomologyIso X n : Hⁿ(X; ULift ℤ) ≅ Hⁿ(X; ℤ)`. Since `uliftIntIso` carries
the multiplication `ModuleCat.uliftTensorSelfIso ℤ` of `ULift ℤ` to the multiplication
`TauCeti.integralCoeffMul` of `ℤ`, this isomorphism carries the cup product with values in
`ULift ℤ` to the integral cup product, by `TopCat.singularCup_singularCohomologyValueMap`.

Singular cohomology with chain coefficients and cochain values `ℤ`, in the form that
`TopCat.lerayHirsch` takes for `k = ℤ`, is also identified with integral cohomology, by
Tau Ceti's `TopCat.integralCohomologyEquiv`, whose inverse this file uses. The two differ in two
ways: the chain coefficients are `ℤ` rather than `ULift ℤ`, changed along
`TauCeti.integralCoeffIso`; and the former uses the structure of `ModuleCat ℤ` as a linear
category over the commutative ring `ℤ`, the latter the structure that every preadditive category
has over `ℤ`. These two structures are not definitionally equal, but they are equal
(`CategoryTheory.Linear.subsingletonInt`), and the identification transports classes, pull-backs
and cup products along that equality, by
`TopCat.singularCohomologyLinearCongr` (`LinearCongr.lean`). Tau Ceti gives the equivalence
with its naturality and its Kronecker pairings; this file adds its values, its compatibility with
cup products and its value on the unit class. The values are read off Tau Ceti's definition, which
is why the file imports all of `TauCeti.AlgebraicTopology.Cohomology.IntegralCup`.

## Main definitions

* `TopCat.uliftIntegralCohomologyIso`: the isomorphism `Hⁿ(X; ULift ℤ) ≅ Hⁿ(X; ℤ)`.

## Main results

* `TauCeti.uliftTensorSelfIso_hom_comp_uliftIntIso_hom`: `TauCeti.uliftIntIso` carries the
  multiplication of `ULift ℤ` to that of `ℤ`.
* `TauCeti.integralCoeffComul_eq_uliftTensorSelfIso_inv`: the diagonal of `ULift ℤ` is the
  inverse of its multiplication.
* `TauCeti.integralCoeffIso_inv_eq_uliftIntIso_inv`: Tau Ceti's isomorphisms
  `TauCeti.integralCoeffIso` and `TauCeti.uliftIntIso` have the same inverse.
* `TopCat.uliftIntegralCohomologyIso_naturality`: `TopCat.uliftIntegralCohomologyIso` commutes
  with the maps induced by continuous maps; `TopCat.uliftIntegralCohomologyIso_naturality_apply`
  states it on a class.
* `TopCat.uliftIntegralCohomologyIso_singularCup`: `TopCat.uliftIntegralCohomologyIso` carries the
  cup product with values in `ULift ℤ` to `TopCat.integralCup`.
* `TopCat.integralCohomologyEquiv_apply` and `TopCat.integralCohomologyEquiv_symm_apply`: the
  values of Tau Ceti's `TopCat.integralCohomologyEquiv` and of its inverse.
* `TopCat.integralCohomologyEquiv_symm_naturality` and
  `TopCat.integralCohomologyEquiv_symm_singularCup`: the inverse of
  `TopCat.integralCohomologyEquiv` commutes with pull-backs and carries cup products to
  `TopCat.integralCup`.
* `TopCat.bijective_integralCup_integralCohomologyEquiv_symm_iff`: cup product with a class is
  bijective in integral cohomology exactly when it is with coefficients `ℤ`.
* `TopCat.integralCohomologyEquiv_symm_singularCohomologyZeroOne`: the equivalence sends the
  unit class to the unit class; so `TopCat.bijective_zsmul_integralCohomologyOne`: on a
  path-connected space, `m ↦ m • 1` is a bijection from `ℤ` onto `H⁰(X; ℤ)`, by Tau Ceti's
  `TauCeti.singularCohomologyZeroEvalEquiv`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Sections 3.1 and 3.2.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex

namespace TauCeti

/-- The isomorphism `ULift ℤ ≅ ℤ` carries the multiplication `a ⊗ b ↦ ⟨a.down * b.down⟩` of
`ULift ℤ` to the multiplication `TauCeti.integralCoeffMul` of `ℤ`. -/
theorem uliftTensorSelfIso_hom_comp_uliftIntIso_hom :
    (ModuleCat.uliftTensorSelfIso ℤ).hom ≫ uliftIntIso.hom =
      (uliftIntIso.hom ⊗ₘ uliftIntIso.hom) ≫ integralCoeffMul := by
  refine ModuleCat.MonoidalCategory.tensor_ext fun a b ↦ ?_
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul, ModuleCat.uliftTensorSelfIso_hom_tmul,
    integralCoeffMul_apply, uliftIntIso_hom_apply, uliftIntIso_hom_apply, uliftIntIso_hom_apply]

/-- The diagonal `n ↦ n (1 ⊗ 1)` of the integral chain coefficients `ULift ℤ` is the inverse of
their multiplication `ModuleCat.uliftTensorSelfIso ℤ`. -/
theorem integralCoeffComul_eq_uliftTensorSelfIso_inv :
    integralCoeffComul = (ModuleCat.uliftTensorSelfIso ℤ).inv := by
  ext a
  rw [integralCoeffComul_apply, ModuleCat.uliftTensorSelfIso_inv_apply,
    ← TensorProduct.tmul_smul]
  congr 1
  ext
  simp

/-- Tau Ceti's two isomorphisms `ULift ℤ ≅ ℤ`, `TauCeti.integralCoeffIso` (the chain coefficients
of integral cohomology) and `TauCeti.uliftIntIso`, have the same inverse `n ↦ ⟨n⟩`. -/
theorem integralCoeffIso_inv_eq_uliftIntIso_inv : integralCoeffIso.inv = uliftIntIso.inv :=
  ModuleCat.hom_ext (LinearMap.ext fun x ↦
    (integralCoeffIso_inv_apply x).trans (uliftIntIso_inv_apply x).symm)

end TauCeti

namespace TopCat

section ULift

open TauCeti

attribute [local instance] MonoidalPreadditive.monoidalLinearInt

variable (X : TopCat.{0})

/-- The isomorphism `Hⁿ(X; ULift ℤ) ≅ Hⁿ(X; ℤ)` from singular cohomology with chain coefficients
and cochain values `ULift ℤ`, the convention of `TauCeti.complexEulerClass`, to the integral
cohomology `TopCat.integralCohomology`: the change of cochain values along
`TauCeti.uliftIntIso : ULift ℤ ≅ ℤ`. -/
def uliftIntegralCohomologyIso (n : ℕ) :
    X.singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ (ModuleCat.of ℤ (ULift.{0} ℤ)) n ≅
      X.integralCohomology n :=
  X.singularCohomologyValueIso _ ℤ uliftIntIso n

theorem uliftIntegralCohomologyIso_hom (n : ℕ) :
    (X.uliftIntegralCohomologyIso n).hom = X.singularCohomologyValueMap _ ℤ uliftIntIso.hom n :=
  X.singularCohomologyValueIso_hom _ ℤ uliftIntIso n

theorem uliftIntegralCohomologyIso_inv (n : ℕ) :
    (X.uliftIntegralCohomologyIso n).inv = X.singularCohomologyValueMap _ ℤ uliftIntIso.inv n :=
  X.singularCohomologyValueIso_inv _ ℤ uliftIntIso n

/-- `TopCat.uliftIntegralCohomologyIso` sends the class of a cocycle `a` with values in `ULift ℤ`
to the class of the integral cocycle `a ≫ uliftIntIso.hom`, that is, `σ ↦ (a σ).down`
(`ChainComplex.iCycles_cyclesMap_linearYonedaObjMap_apply`, `TauCeti.uliftIntIso_hom_apply`). -/
theorem uliftIntegralCohomologyIso_hom_homologyπ (n : ℕ)
    (a : (X.singularCochainComplex (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
      (ModuleCat.of ℤ (ULift.{0} ℤ))).cycles n) :
    (X.uliftIntegralCohomologyIso n).hom
        ((X.singularCochainComplex (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
          (ModuleCat.of ℤ (ULift.{0} ℤ))).homologyπ n a) =
      (X.singularCochainComplex (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ (ModuleCat.of ℤ ℤ)).homologyπ n
        (cyclesMap (((toSSet.obj X).chainComplex
          (ModuleCat.of ℤ (ULift.{0} ℤ))).linearYonedaObjMap ℤ uliftIntIso.hom) n a) := by
  rw [uliftIntegralCohomologyIso_hom]
  exact singularCohomologyValueMap_homologyπ X _ ℤ _ n a

/-- **Naturality of `TopCat.uliftIntegralCohomologyIso`**: it commutes with the maps induced by a
continuous map `f : X ⟶ Y`. Its form applied to a class is
`TopCat.uliftIntegralCohomologyIso_naturality_apply`. -/
@[reassoc, elementwise]
theorem uliftIntegralCohomologyIso_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    TopCat.singularCohomologyMap f n ≫ (X.uliftIntegralCohomologyIso n).hom =
      (Y.uliftIntegralCohomologyIso n).hom ≫ TopCat.singularCohomologyMap f n := by
  rw [uliftIntegralCohomologyIso_hom, uliftIntegralCohomologyIso_hom]
  exact singularCohomologyValueMap_naturality f _ ℤ _ n

/-- **`TopCat.uliftIntegralCohomologyIso` carries cup products to cup products**: the cup product
with values in `ULift ℤ`, along the diagonal `TauCeti.integralCoeffComul` and the multiplication
`ModuleCat.uliftTensorSelfIso ℤ`, is carried to the integral cup product `TopCat.integralCup`. -/
theorem uliftIntegralCohomologyIso_singularCup (p q n : ℕ) (h : p + q = n)
    (a : X.singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
      (ModuleCat.of ℤ (ULift.{0} ℤ)) p)
    (b : X.singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
      (ModuleCat.of ℤ (ULift.{0} ℤ)) q) :
    (X.uliftIntegralCohomologyIso n).hom
        (X.singularCup ℤ integralCoeffComul (ModuleCat.uliftTensorSelfIso ℤ).hom p q n h a b) =
      X.integralCup p q n h ((X.uliftIntegralCohomologyIso p).hom a)
        ((X.uliftIntegralCohomologyIso q).hom b) := by
  rw [uliftIntegralCohomologyIso_hom, uliftIntegralCohomologyIso_hom,
    uliftIntegralCohomologyIso_hom, integralCup_def]
  exact (X.singularCup_singularCohomologyValueMap ℤ integralCoeffComul
    uliftTensorSelfIso_hom_comp_uliftIntIso_hom.symm p q n h a b).symm

end ULift

section IntegerCoefficients

open TauCeti

attribute [local instance] MonoidalPreadditive.monoidalLinearInt

/- The cohomology with coefficients `ℤ` below uses the structure `ModuleCat.instLinear`, the one
that `TopCat.lerayHirsch` uses for `k = ℤ` and the target of Tau Ceti's
`TopCat.integralCohomologyEquiv`. With Tau Ceti's integral cohomology imported, instance search
would otherwise find `CategoryTheory.Linear.preadditiveIntLinear`, the structure that integral
cohomology uses; the pull-back on integral cohomology names that structure. -/
attribute [local instance high] ModuleCat.instLinear

/-- The inverse of Tau Ceti's `TopCat.integralCohomologyEquiv`, from cohomology with chain
coefficients and values `ℤ` to integral cohomology: the change of linear structure
`TopCat.singularCohomologyLinearCongr`, from `ModuleCat.instLinear` to
`CategoryTheory.Linear.preadditiveIntLinear`, followed by the change of chain coefficients
`TopCat.singularCohomologyChainCoefficientMap` along `TauCeti.integralCoeffIso`. -/
theorem integralCohomologyEquiv_symm_apply (X : TopCat.{0}) (n : ℕ)
    (a : X.singularCohomology (𝟙_ (ModuleCat.{0} ℤ)) ℤ (𝟙_ (ModuleCat.{0} ℤ)) n) :
    (X.integralCohomologyEquiv n).symm a =
      @TopCat.singularCohomologyChainCoefficientMap _ _ _ _ _ _ X ℤ _
        Linear.preadditiveIntLinear (ModuleCat.of ℤ ℤ) integralCoeffIso.hom n
        (singularCohomologyLinearCongr (Subsingleton.elim ModuleCat.instLinear _) X (𝟙_ _) (𝟙_ _) n
          a) := by
  rw [LinearEquiv.symm_apply_eq, integralCohomologyEquiv.eq_1]
  simp only [Iso.toLinearEquiv_apply, Iso.trans_hom, Iso.symm_hom,
    singularCohomologyChainCoefficientIso_inv, ConcreteCategory.comp_apply, eqToIso.hom]
  rw [← singularCohomologyLinearCongr_apply (Subsingleton.elim _ _),
    singularCohomologyLinearCongr_singularCohomologyChainCoefficientMap]
  -- Tau Ceti's definition writes the cochain values as `ModuleCat.of ℤ ℤ` in its change of linear
  -- structure and as `𝟙_ (ModuleCat ℤ)` in its change of chain coefficients. Mathlib defines the
  -- latter to be the former, but `rw` does not see this, so the step that joins the two changes
  -- of linear structure, and the closing `exact`, work up to this unfolding.
  erw [singularCohomologyLinearCongr_apply_apply]
  rw [singularCohomologyLinearCongr_refl, LinearEquiv.refl_apply,
    ← singularCohomologyChainCoefficientIso_hom, ← singularCohomologyChainCoefficientIso_inv]
  exact (Iso.hom_inv_id_apply _ a).symm

/-- Tau Ceti's `TopCat.integralCohomologyEquiv`, from integral cohomology to cohomology with chain
coefficients and values `ℤ`: the change of chain coefficients
`TopCat.singularCohomologyChainCoefficientMap` along the inverse of `TauCeti.integralCoeffIso`,
followed by the change of linear structure `TopCat.singularCohomologyLinearCongr`, from
`CategoryTheory.Linear.preadditiveIntLinear` to `ModuleCat.instLinear`. -/
theorem integralCohomologyEquiv_apply (X : TopCat.{0}) (n : ℕ) (y : X.integralCohomology n) :
    X.integralCohomologyEquiv n y =
      singularCohomologyLinearCongr (Subsingleton.elim _ ModuleCat.instLinear) X (𝟙_ _) (𝟙_ _) n
        (@TopCat.singularCohomologyChainCoefficientMap _ _ _ _ _ _ X ℤ _
          Linear.preadditiveIntLinear (ModuleCat.of ℤ ℤ) integralCoeffIso.symm.hom n y) := by
  apply (X.integralCohomologyEquiv n).symm.injective
  rw [LinearEquiv.symm_apply_apply, integralCohomologyEquiv_symm_apply,
    singularCohomologyLinearCongr_apply_apply, singularCohomologyLinearCongr_refl,
    LinearEquiv.refl_apply, Iso.symm_hom, ← singularCohomologyChainCoefficientIso_inv,
    ← singularCohomologyChainCoefficientIso_hom]
  exact (Iso.inv_hom_id_apply _ y).symm

/-- **Naturality of the inverse of `TopCat.integralCohomologyEquiv`**: it commutes with the maps
induced by a continuous map `f : X ⟶ Y`. -/
theorem integralCohomologyEquiv_symm_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (a : Y.singularCohomology (𝟙_ (ModuleCat.{0} ℤ)) ℤ (𝟙_ (ModuleCat.{0} ℤ)) n) :
    (X.integralCohomologyEquiv n).symm (TopCat.singularCohomologyMap f n a) =
      @TopCat.singularCohomologyMap _ _ _ _ (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ _
        Linear.preadditiveIntLinear (ModuleCat.of ℤ ℤ) X Y f n
        ((Y.integralCohomologyEquiv n).symm a) := by
  rw [LinearEquiv.symm_apply_eq, integralCohomologyEquiv_naturality, LinearEquiv.apply_symm_apply]

/-- **The inverse of `TopCat.integralCohomologyEquiv` carries cup products to cup products**: the
cup product with coefficients `ℤ`, along the unitors, is carried to the integral cup product
`TopCat.integralCup`. -/
theorem integralCohomologyEquiv_symm_singularCup (X : TopCat.{0}) (p q n : ℕ) (h : p + q = n)
    (a : X.singularCohomology (𝟙_ (ModuleCat.{0} ℤ)) ℤ (𝟙_ (ModuleCat.{0} ℤ)) p)
    (b : X.singularCohomology (𝟙_ (ModuleCat.{0} ℤ)) ℤ (𝟙_ (ModuleCat.{0} ℤ)) q) :
    (X.integralCohomologyEquiv n).symm (X.singularCup ℤ (λ_ _).inv (λ_ _).hom p q n h a b) =
      X.integralCup p q n h ((X.integralCohomologyEquiv p).symm a)
        ((X.integralCohomologyEquiv q).symm b) := by
  rw [integralCohomologyEquiv_symm_apply, integralCohomologyEquiv_symm_apply,
    integralCohomologyEquiv_symm_apply, singularCohomologyLinearCongr_singularCup,
    integralCup_singularCohomologyChainCoefficientMap]
  -- The two sides differ only in writing the cochain values as the unit `𝟙_ (ModuleCat ℤ)` or as
  -- `ModuleCat.of ℤ ℤ`, which Mathlib defines it to be.
  rfl

/-- Cup product with a class is bijective in integral cohomology exactly when it is in cohomology
with chain coefficients and values `ℤ`: for `b` of degree `q`, `a ↦ a ⌣ b` is a bijection
`Hᵖ(X; ℤ) → Hⁿ(X; ℤ)` of `TopCat.integralCohomology`, for the image of `b` under
the inverse of `TopCat.integralCohomologyEquiv`, if and only if it is one for `b`. -/
theorem bijective_integralCup_integralCohomologyEquiv_symm_iff (X : TopCat.{0}) (p q n : ℕ)
    (h : p + q = n) (b : X.singularCohomology (𝟙_ (ModuleCat.{0} ℤ)) ℤ (𝟙_ (ModuleCat.{0} ℤ)) q) :
    Function.Bijective (fun a : X.integralCohomology p ↦
        X.integralCup p q n h a ((X.integralCohomologyEquiv q).symm b)) ↔
      Function.Bijective (fun a ↦ X.singularCup ℤ (λ_ _).inv (λ_ _).hom p q n h a b) := by
  have hf : (fun a : X.integralCohomology p ↦
      X.integralCup p q n h a ((X.integralCohomologyEquiv q).symm b)) =
      (X.integralCohomologyEquiv n).symm ∘
        (fun a ↦ X.singularCup ℤ (λ_ _).inv (λ_ _).hom p q n h a b) ∘
        X.integralCohomologyEquiv p := by
    funext a
    conv_lhs => rw [← LinearEquiv.symm_apply_apply (X.integralCohomologyEquiv p) a]
    rw [← integralCohomologyEquiv_symm_singularCup]
    simp only [Function.comp_apply]
  rw [hf, Function.Bijective.of_comp_iff' (LinearEquiv.bijective _),
    Function.Bijective.of_comp_iff _ (LinearEquiv.bijective _)]

/-- The inverse of `TopCat.integralCohomologyEquiv` sends the unit class
`TopCat.singularCohomologyZeroOne` of cohomology with coefficients `ℤ` to the unit class
`TopCat.integralCohomologyOne` of integral cohomology. -/
theorem integralCohomologyEquiv_symm_singularCohomologyZeroOne (X : TopCat.{0}) :
    (X.integralCohomologyEquiv 0).symm X.singularCohomologyZeroOne = X.integralCohomologyOne := by
  -- Both are units for the cup product, which the equivalence carries to `TopCat.integralCup`.
  have h := X.integralCohomologyEquiv_symm_singularCup 0 0 0 rfl X.singularCohomologyZeroOne
    (X.integralCohomologyEquiv 0 X.integralCohomologyOne)
  rw [singularCup_singularCohomologyZeroOne_left, LinearEquiv.symm_apply_apply,
    integralCup_integralCohomologyOne_right] at h
  exact h.symm

/-- **The degree-zero integral cohomology of a path-connected space** is free on the unit class:
`m ↦ m • 1` is a bijection from `ℤ` onto `H⁰(X; ℤ)`. -/
theorem bijective_zsmul_integralCohomologyOne (X : TopCat.{0}) [PathConnectedSpace X] :
    Function.Bijective fun m : ℤ ↦ m • X.integralCohomologyOne := by
  convert ((singularCohomologyZeroEvalEquiv (k := ℤ) (Classical.arbitrary X)).symm.trans
    ((X.integralCohomologyEquiv 0).symm)).bijective using 1
  funext m
  rw [LinearEquiv.trans_apply, singularCohomologyZeroEvalEquiv_symm_apply, LinearEquiv.map_smul,
    integralCohomologyEquiv_symm_singularCohomologyZeroOne]
  -- The two sides use the `ℤ`-action of the module structure and that of the group structure.
  exact (int_smul_eq_zsmul _ _ _).symm

end IntegerCoefficients

end TopCat

end
