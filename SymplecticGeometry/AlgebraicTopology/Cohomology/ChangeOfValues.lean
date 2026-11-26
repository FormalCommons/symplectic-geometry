/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cup.Basic
import SymplecticGeometry.Algebra.Homology.Monoidal.CupChangeOfValues

/-!
# Change of cochain values in singular cohomology

For a morphism `g : M ⟶ M'` of cochain values, composing cochains with `g` is a cochain map, and
`TopCat.singularCohomologyValueMap` is the map it induces on singular cohomology; an isomorphism
`e : M ≅ M'` gives the isomorphism `TopCat.singularCohomologyValueIso`. This is the counterpart
of Tau Ceti's change of chain coefficients `TopCat.singularCohomologyChainCoefficientIso`. It is
natural in the space, and it carries cup products along a pairing `μ` to cup products along a
pairing `μ'` whenever the morphisms of values intertwine them, `(g₁ ⊗ g₂) ≫ μ' = μ ≫ g`; this is
the singular case of `TauCeti.ChainComplex.cup_homologyMap_linearYonedaObjMap`.

## Main definitions

* `TopCat.singularCohomologyValueMap`, `TopCat.singularCohomologyValueIso`: the change of cochain
  values on singular cohomology.

## Main results

* `TopCat.singularCohomologyValueMap_naturality`: the change of values commutes with the maps
  induced by continuous maps.
* `TopCat.singularCup_singularCohomologyValueMap`: the change of cochain values carries cup
  products to cup products.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Sections 3.1 and 3.2.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex

universe w v u

namespace TopCat

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
@[reassoc, elementwise]
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
    X.singularCohomology R k M n ≅ X.singularCohomology R k M' n :=
  (homologyFunctor _ _ n).mapIso
    ((((toSSet.obj X).chainComplex R).linearYonedaObjFunctor k).mapIso e)

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
  rw [TauCeti.singularCup_def, TauCeti.singularCup_def]
  exact TauCeti.ChainComplex.cup_homologyMap_linearYonedaObjMap _ hμ p q n h a b

end TopCat

end
