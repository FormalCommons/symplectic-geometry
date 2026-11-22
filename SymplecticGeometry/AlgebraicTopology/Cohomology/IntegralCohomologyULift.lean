/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cohomology.ChangeOfValues
public import SymplecticGeometry.AlgebraicTopology.Cohomology.LinearCongr
public import TauCeti.AlgebraicTopology.Cohomology.IntegralCup
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass
public import TauCeti.Algebra.Category.ModuleCat.Monoidal.Unit
public import TauCeti.CategoryTheory.Linear.Int

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
`TopCat.integralCohomologyLinearEquiv`. The two differ in two ways: the chain coefficients are
`ℤ` rather than `ULift ℤ`, changed along `TauCeti.integralCoeffIso`; and the former uses the
structure of `ModuleCat ℤ` as a linear category over the commutative ring `ℤ`, the latter the
structure that every preadditive category has over `ℤ`. These two structures are not
definitionally equal, but they are equal (`CategoryTheory.Linear.subsingletonInt`), and the
identification transports classes, pull-backs and cup products along that equality, by
`TopCat.singularCohomologyLinearCongr` (`LinearCongr.lean`).

## Main definitions

* `TopCat.uliftIntegralCohomologyIso`: the isomorphism `Hⁿ(X; ULift ℤ) ≅ Hⁿ(X; ℤ)`.
* `TopCat.integralCohomologyLinearEquiv`: the linear equivalence from cohomology with chain
  coefficients and values `ℤ` to `TopCat.integralCohomology`; its value and that of its inverse
  are given by `TopCat.integralCohomologyLinearEquiv_apply` and
  `TopCat.integralCohomologyLinearEquiv_symm_apply`.

## Main results

* `TauCeti.uliftTensorSelfIso_hom_comp_uliftIntIso_hom`: `TauCeti.uliftIntIso` carries the
  multiplication of `ULift ℤ` to that of `ℤ`.
* `TopCat.uliftIntegralCohomologyIso_naturality`: `TopCat.uliftIntegralCohomologyIso` commutes
  with the maps induced by continuous maps.
* `TopCat.uliftIntegralCohomologyIso_singularCup`: `TopCat.uliftIntegralCohomologyIso` carries the
  cup product with values in `ULift ℤ` to `TopCat.integralCup`.
* `TopCat.integralCohomologyLinearEquiv_naturality` and
  `TopCat.integralCohomologyLinearEquiv_singularCup`: `TopCat.integralCohomologyLinearEquiv`
  commutes with pull-backs and carries cup products to `TopCat.integralCup`.
* `TopCat.bijective_integralCup_integralCohomologyLinearEquiv_iff`: cup product with a class is
  bijective in integral cohomology exactly when it is with coefficients `ℤ`.

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

section IntegerCoefficients

open TauCeti

attribute [local instance] MonoidalPreadditive.monoidalLinearInt

/-! The cohomology with chain coefficients and values `ℤ` uses the structure of `ModuleCat ℤ` as a
linear category over the commutative ring `ℤ`, and integral cohomology the structure every
preadditive category has over `ℤ`. The declarations below pass from one to the other by
`TopCat.singularCohomologyLinearCongr`. -/

/-- From cohomology with coefficients `ℤ`, for the linear structure `ModuleCat.instLinear`, to
integral cohomology: the change of linear structure, then the change of chain coefficients along
`TauCeti.integralCoeffIso`. -/
private def toIntegral (X : TopCat.{0}) (n : ℕ) :
    @TopCat.singularCohomology (ModuleCat.{0} ℤ) _ _ _ (𝟙_ (ModuleCat.{0} ℤ)) ℤ _
        ModuleCat.instLinear (𝟙_ (ModuleCat.{0} ℤ)) X n ≃ₗ[ℤ] X.integralCohomology n :=
  (singularCohomologyLinearCongr (Subsingleton.elim _ _) X _ _ n).trans
    (X.singularCohomologyChainCoefficientIso ℤ (ModuleCat.of ℤ ℤ) integralCoeffIso n).toLinearEquiv

private lemma toIntegral_apply (X : TopCat.{0}) (n : ℕ)
    (a : @TopCat.singularCohomology (ModuleCat.{0} ℤ) _ _ _ (𝟙_ (ModuleCat.{0} ℤ)) ℤ _
      ModuleCat.instLinear (𝟙_ (ModuleCat.{0} ℤ)) X n) :
    toIntegral X n a = X.singularCohomologyChainCoefficientMap ℤ (ModuleCat.of ℤ ℤ)
      integralCoeffIso.hom n
        (singularCohomologyLinearCongr (Subsingleton.elim _ _) X (𝟙_ _) (𝟙_ _) n a) := by
  rw [toIntegral, LinearEquiv.trans_apply, Iso.toLinearEquiv_apply,
    singularCohomologyChainCoefficientIso_hom]

private lemma toIntegral_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (a : @TopCat.singularCohomology (ModuleCat.{0} ℤ) _ _ _ (𝟙_ (ModuleCat.{0} ℤ)) ℤ _
      ModuleCat.instLinear (𝟙_ (ModuleCat.{0} ℤ)) Y n) :
    toIntegral X n (@TopCat.singularCohomologyMap (ModuleCat.{0} ℤ) _ _ _ (𝟙_ (ModuleCat.{0} ℤ))
        ℤ _ ModuleCat.instLinear (𝟙_ (ModuleCat.{0} ℤ)) X Y f n a) =
      TopCat.singularCohomologyMap f n (toIntegral Y n a) := by
  rw [toIntegral_apply, toIntegral_apply, singularCohomologyLinearCongr_naturality]
  exact ConcreteCategory.congr_hom (singularCohomologyChainCoefficientMap_naturality f ℤ
    (ModuleCat.of ℤ ℤ) integralCoeffIso.hom n) _

private lemma toIntegral_singularCup (X : TopCat.{0}) (p q n : ℕ) (h : p + q = n)
    (a : @TopCat.singularCohomology (ModuleCat.{0} ℤ) _ _ _ (𝟙_ (ModuleCat.{0} ℤ)) ℤ _
      ModuleCat.instLinear (𝟙_ (ModuleCat.{0} ℤ)) X p)
    (b : @TopCat.singularCohomology (ModuleCat.{0} ℤ) _ _ _ (𝟙_ (ModuleCat.{0} ℤ)) ℤ _
      ModuleCat.instLinear (𝟙_ (ModuleCat.{0} ℤ)) X q) :
    toIntegral X n (@TopCat.singularCup (ModuleCat.{0} ℤ) _ _ _ _ _ (𝟙_ (ModuleCat.{0} ℤ))
        (𝟙_ (ModuleCat.{0} ℤ)) (𝟙_ (ModuleCat.{0} ℤ)) (𝟙_ (ModuleCat.{0} ℤ))
        (𝟙_ (ModuleCat.{0} ℤ)) (𝟙_ (ModuleCat.{0} ℤ)) X ℤ _ ModuleCat.instLinear _
        (λ_ _).inv (λ_ _).hom p q n h a b) =
      X.integralCup p q n h (toIntegral X p a) (toIntegral X q b) := by
  rw [toIntegral_apply, toIntegral_apply, toIntegral_apply,
    singularCohomologyLinearCongr_singularCup, integralCup_singularCohomologyChainCoefficientMap]
  -- The two sides differ only in writing the cochain values as the unit `𝟙_ (ModuleCat ℤ)` or as
  -- `ModuleCat.of ℤ ℤ`, which Mathlib defines it to be.
  rfl

/- The cohomology with coefficients `ℤ` below uses the structure `ModuleCat.instLinear`, the one
that `TopCat.lerayHirsch` uses for `k = ℤ`. With Tau Ceti's integral cohomology imported, instance
search would otherwise find `CategoryTheory.Linear.preadditiveIntLinear`, the structure that
integral cohomology uses; the pull-back on integral cohomology names that structure. -/
attribute [local instance high] ModuleCat.instLinear

/-- The linear equivalence `Hⁿ(X; ℤ) ≃ X.integralCohomology n` from singular cohomology with chain
coefficients and cochain values `ℤ`, for the structure `ModuleCat.instLinear` of `ModuleCat ℤ` as
a linear category over the commutative ring `ℤ`, to integral cohomology. It is the change of
linear structure, then the change of chain coefficients along `TauCeti.integralCoeffIso`. -/
def integralCohomologyLinearEquiv (X : TopCat.{0}) (n : ℕ) :
    X.singularCohomology (𝟙_ (ModuleCat.{0} ℤ)) ℤ (𝟙_ (ModuleCat.{0} ℤ)) n ≃ₗ[ℤ]
      X.integralCohomology n :=
  toIntegral X n

private lemma integralCohomologyLinearEquiv_eq (X : TopCat.{0}) (n : ℕ) :
    X.integralCohomologyLinearEquiv n = toIntegral X n :=
  (rfl)

/-- The value of `TopCat.integralCohomologyLinearEquiv`: the change of linear structure
`TopCat.singularCohomologyLinearCongr`, from `ModuleCat.instLinear` to
`CategoryTheory.Linear.preadditiveIntLinear`, followed by the change of chain coefficients
`TopCat.singularCohomologyChainCoefficientMap` along `TauCeti.integralCoeffIso`. -/
theorem integralCohomologyLinearEquiv_apply (X : TopCat.{0}) (n : ℕ)
    (a : X.singularCohomology (𝟙_ (ModuleCat.{0} ℤ)) ℤ (𝟙_ (ModuleCat.{0} ℤ)) n) :
    X.integralCohomologyLinearEquiv n a =
      @TopCat.singularCohomologyChainCoefficientMap _ _ _ _ _ _ X ℤ _
        Linear.preadditiveIntLinear (ModuleCat.of ℤ ℤ) integralCoeffIso.hom n
        (singularCohomologyLinearCongr (Subsingleton.elim ModuleCat.instLinear _) X (𝟙_ _) (𝟙_ _) n
          a) := by
  rw [integralCohomologyLinearEquiv_eq, toIntegral_apply]

/-- The inverse of `TopCat.integralCohomologyLinearEquiv`: the change of chain coefficients
`TopCat.singularCohomologyChainCoefficientMap` along the inverse of `TauCeti.integralCoeffIso`,
followed by the change of linear structure `TopCat.singularCohomologyLinearCongr`, from
`CategoryTheory.Linear.preadditiveIntLinear` to `ModuleCat.instLinear`. -/
theorem integralCohomologyLinearEquiv_symm_apply (X : TopCat.{0}) (n : ℕ)
    (y : X.integralCohomology n) :
    (X.integralCohomologyLinearEquiv n).symm y =
      singularCohomologyLinearCongr (Subsingleton.elim _ ModuleCat.instLinear) X (𝟙_ _) (𝟙_ _) n
        (@TopCat.singularCohomologyChainCoefficientMap _ _ _ _ _ _ X ℤ _
          Linear.preadditiveIntLinear (ModuleCat.of ℤ ℤ) integralCoeffIso.symm.hom n y) := by
  rw [LinearEquiv.symm_apply_eq, integralCohomologyLinearEquiv_apply,
    singularCohomologyLinearCongr_apply_apply, singularCohomologyLinearCongr_refl,
    LinearEquiv.refl_apply, Iso.symm_hom, ← singularCohomologyChainCoefficientIso_inv,
    ← singularCohomologyChainCoefficientIso_hom]
  exact (Iso.inv_hom_id_apply _ y).symm

/-- **Naturality of `TopCat.integralCohomologyLinearEquiv`**: it commutes with the maps induced by
a continuous map `f : X ⟶ Y`. -/
theorem integralCohomologyLinearEquiv_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (a : Y.singularCohomology (𝟙_ (ModuleCat.{0} ℤ)) ℤ (𝟙_ (ModuleCat.{0} ℤ)) n) :
    X.integralCohomologyLinearEquiv n (TopCat.singularCohomologyMap f n a) =
      @TopCat.singularCohomologyMap _ _ _ _ (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ _
        Linear.preadditiveIntLinear (ModuleCat.of ℤ ℤ) X Y f n
        (Y.integralCohomologyLinearEquiv n a) := by
  rw [integralCohomologyLinearEquiv_eq, integralCohomologyLinearEquiv_eq]
  exact toIntegral_naturality f n a

/-- **`TopCat.integralCohomologyLinearEquiv` carries cup products to cup products**: the cup
product with coefficients `ℤ`, along the unitors, is carried to the integral cup product
`TopCat.integralCup`. -/
theorem integralCohomologyLinearEquiv_singularCup (X : TopCat.{0}) (p q n : ℕ) (h : p + q = n)
    (a : X.singularCohomology (𝟙_ (ModuleCat.{0} ℤ)) ℤ (𝟙_ (ModuleCat.{0} ℤ)) p)
    (b : X.singularCohomology (𝟙_ (ModuleCat.{0} ℤ)) ℤ (𝟙_ (ModuleCat.{0} ℤ)) q) :
    X.integralCohomologyLinearEquiv n (X.singularCup ℤ (λ_ _).inv (λ_ _).hom p q n h a b) =
      X.integralCup p q n h (X.integralCohomologyLinearEquiv p a)
        (X.integralCohomologyLinearEquiv q b) := by
  rw [integralCohomologyLinearEquiv_eq, integralCohomologyLinearEquiv_eq,
    integralCohomologyLinearEquiv_eq]
  exact toIntegral_singularCup X p q n h a b

/-- Cup product with a class is bijective in integral cohomology exactly when it is in cohomology
with chain coefficients and values `ℤ`: for `b` of degree `q`, `a ↦ a ⌣ b` is a bijection
`Hᵖ(X; ℤ) → Hⁿ(X; ℤ)` of `TopCat.integralCohomology`, for the image of `b` under
`TopCat.integralCohomologyLinearEquiv`, if and only if it is one for `b`. -/
theorem bijective_integralCup_integralCohomologyLinearEquiv_iff (X : TopCat.{0}) (p q n : ℕ)
    (h : p + q = n) (b : X.singularCohomology (𝟙_ (ModuleCat.{0} ℤ)) ℤ (𝟙_ (ModuleCat.{0} ℤ)) q) :
    Function.Bijective (fun a : X.integralCohomology p ↦
        X.integralCup p q n h a (X.integralCohomologyLinearEquiv q b)) ↔
      Function.Bijective (fun a ↦ X.singularCup ℤ (λ_ _).inv (λ_ _).hom p q n h a b) := by
  have hf : (fun a : X.integralCohomology p ↦
      X.integralCup p q n h a (X.integralCohomologyLinearEquiv q b)) =
      X.integralCohomologyLinearEquiv n ∘
        (fun a ↦ X.singularCup ℤ (λ_ _).inv (λ_ _).hom p q n h a b) ∘
        (X.integralCohomologyLinearEquiv p).symm := by
    funext a
    conv_lhs => rw [← LinearEquiv.apply_symm_apply (X.integralCohomologyLinearEquiv p) a]
    rw [← integralCohomologyLinearEquiv_singularCup]
    simp only [Function.comp_apply]
  rw [hf, Function.Bijective.of_comp_iff' (LinearEquiv.bijective _),
    Function.Bijective.of_comp_iff _ (LinearEquiv.bijective _)]

end IntegerCoefficients

end TopCat

end
