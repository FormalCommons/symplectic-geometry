/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.IntegralCup
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass
public import TauCeti.Algebra.Category.ModuleCat.Monoidal.Unit

/-!
# Integral cohomology with values in `ULift ℤ`

Tau Ceti writes the Euler class of a complex vector bundle (`TauCeti.complexEulerClass`) in
singular cohomology with chain coefficients and cochain values both `ULift ℤ`, while its integral
cohomology `TopCat.integralCohomology` and integral cup product `TopCat.integralCup` take cochain
values in `ℤ`. This file identifies the two.

For a morphism `g : M ⟶ M'` of cochain values, composing cochains with `g` is a cochain map, and
`TopCat.singularCohomologyValueMap` is the map it induces on singular cohomology; an isomorphism
`e : M ≅ M'` gives the isomorphism `TopCat.singularCohomologyValueIso`. This is the change of
cochain values, the counterpart of Tau Ceti's change of chain coefficients
`TopCat.singularCohomologyChainCoefficientIso`. It is natural in the space, and it carries cup
products along a pairing `μ` to cup products along a pairing `μ'` whenever `g` intertwines them,
`(g₁ ⊗ g₂) ≫ μ' = μ ≫ g`. The proof of the latter, `TopCat.singularCup_singularCohomologyValueMap`,
follows that of Tau Ceti's `TauCeti.ChainComplex.cup_naturality`, with the change of cochain values
in place of the change of chains.

Applied to `TauCeti.uliftIntIso : ULift ℤ ≅ ℤ`, it gives
`TopCat.uliftIntegralCohomologyIso X n : Hⁿ(X; ULift ℤ) ≅ Hⁿ(X; ℤ)`. Since `uliftIntIso` carries
the multiplication `ModuleCat.uliftTensorSelfIso ℤ` of `ULift ℤ` to the multiplication
`TauCeti.integralCoeffMul` of `ℤ`, this isomorphism carries the cup product with values in
`ULift ℤ` to the integral cup product.

## Main definitions

* `TopCat.singularCohomologyValueMap`, `TopCat.singularCohomologyValueIso`: the change of cochain
  values on singular cohomology.
* `TopCat.uliftIntegralCohomologyIso`: the isomorphism `Hⁿ(X; ULift ℤ) ≅ Hⁿ(X; ℤ)`.

## Main results

* `TauCeti.ChainComplex.cupCochain_comp_comp`: the cup product of cochains is natural in the
  pairing of the values.
* `TopCat.singularCup_singularCohomologyValueMap`: the change of cochain values carries cup
  products to cup products.
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

universe w v u

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

namespace ChainComplex

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]
  {A B E : ChainComplex C ℕ} [A.HasTensor B] {M N P M' N' P' : C} {k : Type*} [CommSemiring k]
  [Linear k C] [MonoidalLinear k C]

/-- **Naturality of the cup product of cochains in the pairing**: if `g₁ : M ⟶ M'`,
`g₂ : N ⟶ N'` and `g : P ⟶ P'` intertwine the pairings, `(g₁ ⊗ g₂) ≫ μ' = μ ≫ g`, then the cup
product along `μ'` of the cochains composed with `g₁` and `g₂` is the cup product along `μ`
composed with `g`. -/
theorem cupCochain_comp_comp (D : E ⟶ HomologicalComplex.tensorObj A B) {μ : M ⊗ N ⟶ P}
    {μ' : M' ⊗ N' ⟶ P'} {g₁ : M ⟶ M'} {g₂ : N ⟶ N'} {g : P ⟶ P'}
    (hμ : (g₁ ⊗ₘ g₂) ≫ μ' = μ ≫ g) (p q n : ℕ) (h : p + q = n) (φ : A.X p ⟶ M)
    (ψ : B.X q ⟶ N) :
    cupCochain k D μ' p q n h (φ ≫ g₁) (ψ ≫ g₂) = cupCochain k D μ p q n h φ ψ ≫ g := by
  rw [cupCochain_apply, cupCochain_apply, Category.assoc, tensorCochain_comp, ← hμ,
    tensorHom_def, Category.assoc, tensorCochain_whiskerRight_comp,
    tensorCochain_whiskerLeft_comp]

end ChainComplex

end TauCeti

namespace TopCat

section Values

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] {M M' M'' : C}

/-- The map `Hⁿ(X; R, M) ⟶ Hⁿ(X; R, M')` induced by a morphism `g : M ⟶ M'` of cochain values:
composition of cochains with `g`. -/
abbrev singularCohomologyValueMap (X : TopCat.{w}) (R : C) (k : Type*) [Ring k] [Linear k C]
    (g : M ⟶ M') (n : ℕ) :
    X.singularCohomology R k M n ⟶ X.singularCohomology R k M' n :=
  homologyMap (((toSSet.obj X).chainComplex R).linearYonedaObjMap k g) n

/-- The change of cochain values sends the class of a cocycle to the class of the cocycle composed
with the morphism of values (see `ChainComplex.iCycles_cyclesMap_linearYonedaObjMap_apply`). -/
theorem singularCohomologyValueMap_homologyπ (X : TopCat.{w}) (R : C) (k : Type*) [Ring k]
    [Linear k C] (g : M ⟶ M') (n : ℕ) (a : (X.singularCochainComplex R k M).cycles n) :
    X.singularCohomologyValueMap R k g n ((X.singularCochainComplex R k M).homologyπ n a) =
      (X.singularCochainComplex R k M').homologyπ n
        (cyclesMap (((toSSet.obj X).chainComplex R).linearYonedaObjMap k g) n a) :=
  ChainComplex.homologyMap_linearYonedaObjMap_homologyπ_apply (k := k) _ g n a

@[simp]
theorem singularCohomologyValueMap_id (X : TopCat.{w}) (R : C) (k : Type*) [Ring k]
    [Linear k C] (n : ℕ) :
    X.singularCohomologyValueMap R k (𝟙 M) n = 𝟙 _ := by
  simp [singularCohomologyValueMap]

@[reassoc]
theorem singularCohomologyValueMap_comp (X : TopCat.{w}) (R : C) (k : Type*) [Ring k]
    [Linear k C] (g : M ⟶ M') (g' : M' ⟶ M'') (n : ℕ) :
    X.singularCohomologyValueMap R k (g ≫ g') n =
      X.singularCohomologyValueMap R k g n ≫ X.singularCohomologyValueMap R k g' n := by
  simp [singularCohomologyValueMap, homologyMap_comp]

/-- The change of cochain values commutes with the maps induced by continuous maps. -/
@[reassoc]
theorem singularCohomologyValueMap_naturality {X Y : TopCat.{w}} (f : X ⟶ Y) (R : C)
    (k : Type*) [Ring k] [Linear k C] (g : M ⟶ M') (n : ℕ) :
    TopCat.singularCohomologyMap f n ≫ X.singularCohomologyValueMap R k g n =
      Y.singularCohomologyValueMap R k g n ≫ TopCat.singularCohomologyMap f n := by
  rw [singularCohomologyValueMap, singularCohomologyValueMap, TopCat.singularCohomologyMap,
    ← homologyMap_comp, ← homologyMap_comp]
  congr 1
  exact (ChainComplex.linearYonedaObjMap_comp_linearYonedaFunctor_map k _ g).symm

/-- The isomorphism `Hⁿ(X; R, M) ≅ Hⁿ(X; R, M')` induced by an isomorphism `e : M ≅ M'` of
cochain values, with underlying map `TopCat.singularCohomologyValueMap`. -/
def singularCohomologyValueIso (X : TopCat.{w}) (R : C) (k : Type*) [Ring k] [Linear k C]
    (e : M ≅ M') (n : ℕ) :
    X.singularCohomology R k M n ≅ X.singularCohomology R k M' n where
  hom := X.singularCohomologyValueMap R k e.hom n
  inv := X.singularCohomologyValueMap R k e.inv n
  hom_inv_id := by rw [← singularCohomologyValueMap_comp, e.hom_inv_id,
    singularCohomologyValueMap_id]
  inv_hom_id := by rw [← singularCohomologyValueMap_comp, e.inv_hom_id,
    singularCohomologyValueMap_id]

@[simp]
theorem singularCohomologyValueIso_hom (X : TopCat.{w}) (R : C) (k : Type*) [Ring k]
    [Linear k C] (e : M ≅ M') (n : ℕ) :
    (X.singularCohomologyValueIso R k e n).hom = X.singularCohomologyValueMap R k e.hom n :=
  (rfl)

@[simp]
theorem singularCohomologyValueIso_inv (X : TopCat.{w}) (R : C) (k : Type*) [Ring k]
    [Linear k C] (e : M ≅ M') (n : ℕ) :
    (X.singularCohomologyValueIso R k e n).inv = X.singularCohomologyValueMap R k e.inv n :=
  (rfl)

variable [MonoidalCategory C] [MonoidalPreadditive C] {R S T N N' P P' : C}

/-- **The change of cochain values carries cup products to cup products**: if `g₁ : M ⟶ M'`,
`g₂ : N ⟶ N'` and `g : P ⟶ P'` intertwine the pairings, `(g₁ ⊗ g₂) ≫ μ' = μ ≫ g`, then the cup
product along `μ'` of the images of `a` and `b` under `g₁` and `g₂` is the image under `g` of
their cup product along `μ`. -/
theorem singularCup_singularCohomologyValueMap (X : TopCat.{w}) (k : Type*) [CommRing k]
    [Linear k C] [MonoidalLinear k C] (u : T ⟶ R ⊗ S) {μ : M ⊗ N ⟶ P} {μ' : M' ⊗ N' ⟶ P'}
    {g₁ : M ⟶ M'} {g₂ : N ⟶ N'} {g : P ⟶ P'} (hμ : (g₁ ⊗ₘ g₂) ≫ μ' = μ ≫ g)
    (p q n : ℕ) (h : p + q = n) (a : X.singularCohomology R k M p)
    (b : X.singularCohomology S k N q) :
    X.singularCup k u μ' p q n h (X.singularCohomologyValueMap R k g₁ p a)
        (X.singularCohomologyValueMap S k g₂ q b) =
      X.singularCohomologyValueMap T k g n (X.singularCup k u μ p q n h a b) := by
  obtain ⟨a, rfl⟩ := moduleCat_homologyπ_surjective _ p a
  obtain ⟨b, rfl⟩ := moduleCat_homologyπ_surjective _ q b
  rw [singularCohomologyValueMap_homologyπ, singularCohomologyValueMap_homologyπ,
    singularCup_homologyπ, singularCup_homologyπ, singularCohomologyValueMap_homologyπ]
  congr 1
  apply moduleCat_iCycles_injective
  rw [TauCeti.ChainComplex.iCycles_cupCycles,
    ChainComplex.iCycles_cyclesMap_linearYonedaObjMap_apply,
    ChainComplex.iCycles_cyclesMap_linearYonedaObjMap_apply,
    ChainComplex.iCycles_cyclesMap_linearYonedaObjMap_apply,
    TauCeti.ChainComplex.iCycles_cupCycles]
  exact TauCeti.ChainComplex.cupCochain_comp_comp _ hμ p q n h _ _

end Values

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
  (rfl)

theorem uliftIntegralCohomologyIso_inv (n : ℕ) :
    (X.uliftIntegralCohomologyIso n).inv = X.singularCohomologyValueMap _ ℤ uliftIntIso.inv n :=
  (rfl)

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
          (ModuleCat.of ℤ (ULift.{0} ℤ))).linearYonedaObjMap ℤ uliftIntIso.hom) n a) :=
  singularCohomologyValueMap_homologyπ X _ ℤ _ n a

/-- **Naturality of `TopCat.uliftIntegralCohomologyIso`**: it commutes with the maps induced by a
continuous map `f : X ⟶ Y`. -/
@[reassoc]
theorem uliftIntegralCohomologyIso_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    TopCat.singularCohomologyMap f n ≫ (X.uliftIntegralCohomologyIso n).hom =
      (Y.uliftIntegralCohomologyIso n).hom ≫ TopCat.singularCohomologyMap f n :=
  singularCohomologyValueMap_naturality f _ ℤ _ n

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
        ((X.uliftIntegralCohomologyIso q).hom b) :=
  by
  rw [uliftIntegralCohomologyIso_hom, uliftIntegralCohomologyIso_hom,
    uliftIntegralCohomologyIso_hom, integralCup_def]
  exact (X.singularCup_singularCohomologyValueMap ℤ integralCoeffComul
    uliftTensorSelfIso_hom_comp_uliftIntIso_hom.symm p q n h a b).symm

end ULift

end TopCat

end
