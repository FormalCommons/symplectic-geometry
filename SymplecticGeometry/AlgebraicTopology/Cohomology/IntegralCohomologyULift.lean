/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cohomology.ChangeOfValues
public import TauCeti.AlgebraicTopology.Cohomology.IntegralCup
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass
public import TauCeti.Algebra.Category.ModuleCat.Monoidal.Unit

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

## Main definitions

* `TopCat.uliftIntegralCohomologyIso`: the isomorphism `Hⁿ(X; ULift ℤ) ≅ Hⁿ(X; ℤ)`.

## Main results

* `TauCeti.uliftTensorSelfIso_hom_comp_uliftIntIso_hom`: `TauCeti.uliftIntIso` carries the
  multiplication of `ULift ℤ` to that of `ℤ`.
* `TopCat.uliftIntegralCohomologyIso_naturality`: `TopCat.uliftIntegralCohomologyIso` commutes
  with the maps induced by continuous maps.
* `TopCat.uliftIntegralCohomologyIso_singularCup`: `TopCat.uliftIntegralCohomologyIso` carries the
  cup product with values in `ULift ℤ` to `TopCat.integralCup`.

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
continuous map `f : X ⟶ Y`. -/
@[reassoc]
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

end TopCat

end
