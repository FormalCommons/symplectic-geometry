/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cohomology.IntegralCohomologyULift
public import TauCeti.AlgebraicTopology.Cohomology.Relative
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass
public import TauCeti.CategoryTheory.Linear.Int
import SymplecticGeometry.AlgebraicTopology.Cohomology.ChangeOfValues
import SymplecticGeometry.AlgebraicTopology.Cohomology.LinearCongr

/-!
# Change of coefficients in the singular cohomology of a pair

Relative singular cohomology `Hⁿ(X, A; R, M)` of a topological pair `P = (X, A)` depends on the
chain coefficients `R`, the cochain values `M` and a structure `Linear k C` of the category of
coefficients. This file changes each of the three, as Tau Ceti's
`TopCat.singularCohomologyChainCoefficientMap`, this library's
`TopCat.singularCohomologyValueMap` and `TopCat.singularCohomologyLinearCongr` do for spaces:

* `TopPair.singularCohomologyChainCoefficientMap P k M f n` for `f : R' ⟶ R`, the map
  `Hⁿ(X, A; R, M) ⟶ Hⁿ(X, A; R', M)` induced by the map of relative chains
  `C(X, A; R') ⟶ C(X, A; R)` of the bifunctor `SSetPair.chainComplexFunctor`;
* `TopPair.singularCohomologyValueMap P R k g n` for `g : M ⟶ M'`, the map
  `Hⁿ(X, A; R, M) ⟶ Hⁿ(X, A; R, M')` composing cochains with `g`;
* `TopPair.singularCohomologyLinearCongr e P R M n` for `e : L₁ = L₂`, the linear equivalence
  `LinearEquiv.cast` along `e`.

Each commutes with the maps induced by maps of pairs (the `_naturality` lemmas), and with the map
`TopPair.singularCohomologyπ` from relative to absolute cohomology, followed on the absolute side
by the change for spaces (the `_singularCohomologyπ` lemmas). An isomorphism of chain
coefficients or of values gives an isomorphism of cohomology
(`TopPair.singularCohomologyChainCoefficientIso`, `TopPair.singularCohomologyValueIso`).

For a pair of spaces in `Type`, the three combine, along `TauCeti.uliftIntIso : ULift ℤ ≅ ℤ`,
into `TopPair.uliftIntegralCohomologyEquiv`: the `ℤ`-linear equivalence from cohomology with
chain coefficients and values `ULift ℤ`, the convention of Tau Ceti's integral Thom and Euler
classes, to cohomology with chain coefficients and values `ℤ` and the linear structure
`ModuleCat.instLinear`, the convention of Tau Ceti's Thom map `TauCeti.thomMap`. The two linear
structures of `ModuleCat ℤ` agree by `CategoryTheory.Linear.subsingletonInt`. It commutes with
the maps induced by maps of pairs (`TopPair.uliftIntegralCohomologyEquiv_naturality`), and with
the map to absolute cohomology, followed on the absolute side by
`TopCat.uliftIntegralCohomologyIso` and Tau Ceti's `TopCat.integralCohomologyEquiv`
(`TopPair.singularCohomologyπ_uliftIntegralCohomologyEquiv`). This is the
conversion that the proof of the library's `TauCeti.bijective_integralCup_eulerClass`
(`Topology/VectorBundle/Thom/CupEulerClass.lean`) makes for a Thom class.

The proofs follow those of the same statements for spaces, in the setting of pairs: Tau Ceti's
`TopCat.singularCohomologyChainCoefficientMap_id`, `_comp` and `_naturality`, and this
library's `TopCat.singularCohomologyValueMap_naturality` and
`TopCat.singularCohomologyLinearCongr_naturality`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Sections 3.1 and 3.2.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex Opposite

universe w v u

namespace TopPair

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]

section ChainCoefficients

variable {R R' R'' : C}

/-- The map `Hⁿ(X, A; R, M) ⟶ Hⁿ(X, A; R', M)` induced by a morphism `f : R' ⟶ R` of chain
coefficients: precomposition with the induced map of relative singular chains
`C(X, A; R') ⟶ C(X, A; R)`. -/
abbrev singularCohomologyChainCoefficientMap (P : TopPair.{w}) (k : Type*) [Ring k]
    [Linear k C] (M : C) (f : R' ⟶ R) (n : ℕ) :
    P.singularCohomology R k M n ⟶ P.singularCohomology R' k M n :=
  homologyMap ((TauCeti.ChainComplex.linearYonedaFunctor k M).map
    (((SSetPair.chainComplexFunctor C).map f).app (toSSetPair.obj P)).op) n

@[simp]
theorem singularCohomologyChainCoefficientMap_id (P : TopPair.{w}) (k : Type*) [Ring k]
    [Linear k C] (M : C) (n : ℕ) :
    P.singularCohomologyChainCoefficientMap k M (𝟙 R) n = 𝟙 _ := by
  simp only [singularCohomologyChainCoefficientMap, CategoryTheory.Functor.map_id,
    NatTrans.id_app, op_id]
  exact homologyMap_id _ _

@[reassoc]
theorem singularCohomologyChainCoefficientMap_comp (P : TopPair.{w}) (k : Type*) [Ring k]
    [Linear k C] (M : C) (f : R'' ⟶ R') (g : R' ⟶ R) (n : ℕ) :
    P.singularCohomologyChainCoefficientMap k M (f ≫ g) n =
      P.singularCohomologyChainCoefficientMap k M g n ≫
        P.singularCohomologyChainCoefficientMap k M f n := by
  simp only [singularCohomologyChainCoefficientMap, Functor.map_comp, NatTrans.comp_app, op_comp]
  exact homologyMap_comp _ _ _

/-- The change of chain coefficients commutes with the maps induced by maps of pairs. -/
@[reassoc, elementwise]
theorem singularCohomologyChainCoefficientMap_naturality {P P' : TopPair.{w}} (g : P ⟶ P')
    (k : Type*) [Ring k] [Linear k C] (M : C) (f : R' ⟶ R) (n : ℕ) :
    TopPair.singularCohomologyMap g n ≫ P.singularCohomologyChainCoefficientMap k M f n =
      P'.singularCohomologyChainCoefficientMap k M f n ≫ TopPair.singularCohomologyMap g n := by
  have h := congrArg (fun φ ↦ (TauCeti.ChainComplex.linearYonedaFunctor k M).map φ.op)
    (((SSetPair.chainComplexFunctor C).map f).naturality (toSSetPair.map g))
  simp only [op_comp, Functor.map_comp] at h
  exact (homologyMap_comp _ _ _).symm.trans
    ((congrArg (homologyMap · n) h.symm).trans (homologyMap_comp _ _ _))

/-- The change of chain coefficients commutes with the map from relative to absolute
cohomology. -/
@[reassoc]
theorem singularCohomologyπ_singularCohomologyChainCoefficientMap (P : TopPair.{w})
    (k : Type*) [Ring k] [Linear k C] (M : C) (f : R' ⟶ R) (n : ℕ) :
    P.singularCohomologyπ R k M n ≫ P.fst.singularCohomologyChainCoefficientMap k M f n =
      P.singularCohomologyChainCoefficientMap k M f n ≫ P.singularCohomologyπ R' k M n := by
  have h := congrArg (fun φ ↦ (TauCeti.ChainComplex.linearYonedaFunctor k M).map φ.op)
    (P.singularChainComplexπ_coefficient_naturality f)
  -- `(a ≫ b).op` is `b.op ≫ a.op` by definition, and the ambient chains of `P` appear both as
  -- those of `P.fst` and of `(toSSetPair.obj P).right`, so the steps are stated as terms.
  exact (homologyMap_comp _ _ _).symm.trans ((congrArg (homologyMap · n)
    ((Functor.map_comp _ _ _).symm.trans (h.trans (Functor.map_comp _ _ _)))).trans
      (homologyMap_comp _ _ _))

/-- The isomorphism `Hⁿ(X, A; R, M) ≅ Hⁿ(X, A; R', M)` induced by an isomorphism `e : R' ≅ R` of
chain coefficients, with underlying map `TopPair.singularCohomologyChainCoefficientMap`. -/
def singularCohomologyChainCoefficientIso (P : TopPair.{w}) (k : Type*) [Ring k] [Linear k C]
    (M : C) (e : R' ≅ R) (n : ℕ) :
    P.singularCohomology R k M n ≅ P.singularCohomology R' k M n where
  hom := P.singularCohomologyChainCoefficientMap k M e.hom n
  inv := P.singularCohomologyChainCoefficientMap k M e.inv n
  hom_inv_id := by
    rw [← singularCohomologyChainCoefficientMap_comp, e.inv_hom_id,
      singularCohomologyChainCoefficientMap_id]
  inv_hom_id := by
    rw [← singularCohomologyChainCoefficientMap_comp, e.hom_inv_id,
      singularCohomologyChainCoefficientMap_id]

@[simp]
theorem singularCohomologyChainCoefficientIso_hom (P : TopPair.{w}) (k : Type*) [Ring k]
    [Linear k C] (M : C) (e : R' ≅ R) (n : ℕ) :
    (P.singularCohomologyChainCoefficientIso k M e n).hom =
      P.singularCohomologyChainCoefficientMap k M e.hom n :=
  (rfl)

@[simp]
theorem singularCohomologyChainCoefficientIso_inv (P : TopPair.{w}) (k : Type*) [Ring k]
    [Linear k C] (M : C) (e : R' ≅ R) (n : ℕ) :
    (P.singularCohomologyChainCoefficientIso k M e n).inv =
      P.singularCohomologyChainCoefficientMap k M e.inv n :=
  (rfl)

end ChainCoefficients

section Values

variable {M M' M'' : C}

/-- The map `Hⁿ(X, A; R, M) ⟶ Hⁿ(X, A; R, M')` induced by a morphism `g : M ⟶ M'` of cochain
values: composition of relative cochains with `g`. -/
abbrev singularCohomologyValueMap (P : TopPair.{w}) (R : C) (k : Type*) [Ring k] [Linear k C]
    (g : M ⟶ M') (n : ℕ) :
    P.singularCohomology R k M n ⟶ P.singularCohomology R k M' n :=
  homologyMap ((P.singularChainComplex R).linearYonedaObjMap k g) n

@[simp]
theorem singularCohomologyValueMap_id (P : TopPair.{w}) (R : C) (k : Type*) [Ring k]
    [Linear k C] (n : ℕ) :
    P.singularCohomologyValueMap R k (𝟙 M) n = 𝟙 _ := by
  simp [singularCohomologyValueMap]

@[reassoc]
theorem singularCohomologyValueMap_comp (P : TopPair.{w}) (R : C) (k : Type*) [Ring k]
    [Linear k C] (g : M ⟶ M') (g' : M' ⟶ M'') (n : ℕ) :
    P.singularCohomologyValueMap R k (g ≫ g') n =
      P.singularCohomologyValueMap R k g n ≫ P.singularCohomologyValueMap R k g' n := by
  simp [singularCohomologyValueMap, homologyMap_comp]

/-- The change of cochain values commutes with the maps induced by maps of pairs. -/
@[reassoc, elementwise]
theorem singularCohomologyValueMap_naturality {P P' : TopPair.{w}} (f : P ⟶ P') (R : C)
    (k : Type*) [Ring k] [Linear k C] (g : M ⟶ M') (n : ℕ) :
    TopPair.singularCohomologyMap f n ≫ P.singularCohomologyValueMap R k g n =
      P'.singularCohomologyValueMap R k g n ≫ TopPair.singularCohomologyMap f n := by
  rw [singularCohomologyValueMap, singularCohomologyValueMap, TopPair.singularCohomologyMap,
    ← homologyMap_comp, ← homologyMap_comp]
  congr 1
  exact (ChainComplex.linearYonedaObjMap_comp_linearYonedaFunctor_map k _ g).symm

/-- The change of cochain values commutes with the map from relative to absolute cohomology. -/
@[reassoc]
theorem singularCohomologyπ_singularCohomologyValueMap (P : TopPair.{w}) (R : C) (k : Type*)
    [Ring k] [Linear k C] (g : M ⟶ M') (n : ℕ) :
    P.singularCohomologyπ R k M n ≫ P.fst.singularCohomologyValueMap R k g n =
      P.singularCohomologyValueMap R k g n ≫ P.singularCohomologyπ R k M' n := by
  rw [singularCohomologyValueMap, TopCat.singularCohomologyValueMap, singularCohomologyπ,
    singularCohomologyπ, ← homologyMap_comp, ← homologyMap_comp]
  congr 1
  exact (ChainComplex.linearYonedaObjMap_comp_linearYonedaFunctor_map k _ g).symm

/-- The isomorphism `Hⁿ(X, A; R, M) ≅ Hⁿ(X, A; R, M')` induced by an isomorphism `e : M ≅ M'` of
cochain values, with underlying map `TopPair.singularCohomologyValueMap`. -/
def singularCohomologyValueIso (P : TopPair.{w}) (R : C) (k : Type*) [Ring k] [Linear k C]
    (e : M ≅ M') (n : ℕ) :
    P.singularCohomology R k M n ≅ P.singularCohomology R k M' n :=
  (homologyFunctor _ _ n).mapIso (((P.singularChainComplex R).linearYonedaObjFunctor k).mapIso e)

@[simp]
theorem singularCohomologyValueIso_hom (P : TopPair.{w}) (R : C) (k : Type*) [Ring k]
    [Linear k C] (e : M ≅ M') (n : ℕ) :
    (P.singularCohomologyValueIso R k e n).hom = P.singularCohomologyValueMap R k e.hom n :=
  (rfl)

@[simp]
theorem singularCohomologyValueIso_inv (P : TopPair.{w}) (R : C) (k : Type*) [Ring k]
    [Linear k C] (e : M ≅ M') (n : ℕ) :
    (P.singularCohomologyValueIso R k e n).inv = P.singularCohomologyValueMap R k e.inv n :=
  (rfl)

end Values

section LinearCongr

variable {k : Type*} [Ring k]

/-- The identification of relative singular cohomology `Hⁿ(X, A; R, M)` for two equal structures
`L₁ = L₂` of `C` as a `k`-linear category: Mathlib's `LinearEquiv.cast` along `e`. -/
def singularCohomologyLinearCongr {L₁ L₂ : Linear k C} (e : L₁ = L₂) (P : TopPair.{w}) (R M : C)
    (n : ℕ) :
    @TopPair.singularCohomology C _ _ _ P R k _ L₁ M n ≃ₗ[k]
      @TopPair.singularCohomology C _ _ _ P R k _ L₂ M n :=
  LinearEquiv.cast (R := k)
    (M := fun L : Linear k C ↦ @TopPair.singularCohomology C _ _ _ P R k _ L M n) e

theorem singularCohomologyLinearCongr_def {L₁ L₂ : Linear k C} (e : L₁ = L₂) (P : TopPair.{w})
    (R M : C) (n : ℕ) :
    singularCohomologyLinearCongr e P R M n = LinearEquiv.cast (R := k)
      (M := fun L : Linear k C ↦ @TopPair.singularCohomology C _ _ _ P R k _ L M n) e :=
  (rfl)

@[simp]
theorem singularCohomologyLinearCongr_refl (L : Linear k C) (P : TopPair.{w}) (R M : C)
    (n : ℕ) :
    singularCohomologyLinearCongr (rfl : L = L) P R M n = LinearEquiv.refl k _ :=
  (rfl)

@[simp]
theorem singularCohomologyLinearCongr_symm {L₁ L₂ : Linear k C} (e : L₁ = L₂)
    (P : TopPair.{w}) (R M : C) (n : ℕ) :
    (singularCohomologyLinearCongr e P R M n).symm =
      singularCohomologyLinearCongr e.symm P R M n := by
  subst e
  rfl

@[simp]
theorem singularCohomologyLinearCongr_trans {L₁ L₂ L₃ : Linear k C} (e : L₁ = L₂)
    (e' : L₂ = L₃) (P : TopPair.{w}) (R M : C) (n : ℕ) :
    (singularCohomologyLinearCongr e P R M n).trans (singularCohomologyLinearCongr e' P R M n) =
      singularCohomologyLinearCongr (e.trans e') P R M n := by
  subst e e'
  rfl

@[simp]
theorem singularCohomologyLinearCongr_apply_apply {L₁ L₂ L₃ : Linear k C} (e : L₁ = L₂)
    (e' : L₂ = L₃) (P : TopPair.{w}) (R M : C) (n : ℕ)
    (a : @TopPair.singularCohomology C _ _ _ P R k _ L₁ M n) :
    singularCohomologyLinearCongr e' P R M n (singularCohomologyLinearCongr e P R M n a) =
      singularCohomologyLinearCongr (e.trans e') P R M n a := by
  subst e e'
  rfl

/-- **Naturality of `TopPair.singularCohomologyLinearCongr`**: it commutes with the maps induced
by a map of pairs `f : P ⟶ P'`. -/
theorem singularCohomologyLinearCongr_naturality {L₁ L₂ : Linear k C} (e : L₁ = L₂)
    {P P' : TopPair.{w}} (f : P ⟶ P') (R M : C) (n : ℕ)
    (a : @TopPair.singularCohomology C _ _ _ P' R k _ L₁ M n) :
    singularCohomologyLinearCongr e P R M n
        (@TopPair.singularCohomologyMap C _ _ _ R k _ L₁ M P P' f n a) =
      @TopPair.singularCohomologyMap C _ _ _ R k _ L₂ M P P' f n
        (singularCohomologyLinearCongr e P' R M n a) := by
  subst e
  simp only [singularCohomologyLinearCongr_refl, LinearEquiv.refl_apply]

/-- `TopPair.singularCohomologyLinearCongr` commutes with the map from relative to absolute
cohomology, followed on the absolute side by `TopCat.singularCohomologyLinearCongr`. -/
theorem singularCohomologyLinearCongr_singularCohomologyπ {L₁ L₂ : Linear k C} (e : L₁ = L₂)
    (P : TopPair.{w}) (R M : C) (n : ℕ)
    (a : @TopPair.singularCohomology C _ _ _ P R k _ L₁ M n) :
    TopCat.singularCohomologyLinearCongr e P.fst R M n
        (@TopPair.singularCohomologyπ C _ _ _ P R k _ L₁ M n a) =
      @TopPair.singularCohomologyπ C _ _ _ P R k _ L₂ M n
        (singularCohomologyLinearCongr e P R M n a) := by
  subst e
  simp only [singularCohomologyLinearCongr_refl, TopCat.singularCohomologyLinearCongr_refl,
    LinearEquiv.refl_apply]

end LinearCongr

section ULiftInt

open TauCeti

/-- The `ℤ`-linear equivalence `Hⁿ(X, A; ULift ℤ) ≃ Hⁿ(X, A; ℤ)` from relative cohomology with
chain coefficients and cochain values `ULift ℤ`, and the `ℤ`-linear structure that `ModuleCat ℤ`
has as a preadditive category, to relative cohomology with chain coefficients and cochain values
`ℤ` and the structure `ModuleCat.instLinear`: the change of values along
`TauCeti.uliftIntIso : ULift ℤ ≅ ℤ`, then of chain coefficients along its inverse, then of the
linear structure. -/
def uliftIntegralCohomologyEquiv (P : TopPair.{0}) (n : ℕ) :
    P.singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ (ModuleCat.of ℤ (ULift.{0} ℤ)) n ≃ₗ[ℤ]
      @TopPair.singularCohomology (ModuleCat.{0} ℤ) _ _ _ P (ModuleCat.of ℤ ℤ) ℤ _
        ModuleCat.instLinear (ModuleCat.of ℤ ℤ) n :=
  ((P.singularCohomologyValueIso _ ℤ uliftIntIso n) ≪≫
      (P.singularCohomologyChainCoefficientIso ℤ _ uliftIntIso.symm n)).toLinearEquiv ≪≫ₗ
    singularCohomologyLinearCongr (Subsingleton.elim _ _) P _ _ _

theorem uliftIntegralCohomologyEquiv_apply (P : TopPair.{0}) (n : ℕ)
    (u : P.singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ (ModuleCat.of ℤ (ULift.{0} ℤ)) n) :
    P.uliftIntegralCohomologyEquiv n u =
      singularCohomologyLinearCongr (Subsingleton.elim _ _) P _ _ _
        (P.singularCohomologyChainCoefficientMap ℤ _ uliftIntIso.inv n
          (P.singularCohomologyValueMap _ ℤ uliftIntIso.hom n u)) :=
  (rfl)

/-- **Naturality of `TopPair.uliftIntegralCohomologyEquiv`**: it commutes with the maps induced
by a map of pairs `f : P ⟶ P'`. -/
theorem uliftIntegralCohomologyEquiv_naturality {P P' : TopPair.{0}} (f : P ⟶ P') (n : ℕ)
    (u : P'.singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
      (ModuleCat.of ℤ (ULift.{0} ℤ)) n) :
    P.uliftIntegralCohomologyEquiv n (TopPair.singularCohomologyMap f n u) =
      @TopPair.singularCohomologyMap (ModuleCat.{0} ℤ) _ _ _ (ModuleCat.of ℤ ℤ) ℤ _
        ModuleCat.instLinear (ModuleCat.of ℤ ℤ) P P' f n (P'.uliftIntegralCohomologyEquiv n u) := by
  rw [uliftIntegralCohomologyEquiv_apply, uliftIntegralCohomologyEquiv_apply,
    ← singularCohomologyLinearCongr_naturality,
    ← singularCohomologyChainCoefficientMap_naturality_apply,
    ← singularCohomologyValueMap_naturality_apply]

/-- `TopPair.uliftIntegralCohomologyEquiv` commutes with the map from relative to absolute
cohomology, followed on the absolute side by `TopCat.uliftIntegralCohomologyIso` and Tau Ceti's
`TopCat.integralCohomologyEquiv`. -/
theorem singularCohomologyπ_uliftIntegralCohomologyEquiv (P : TopPair.{0}) (n : ℕ)
    (u : P.singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
      (ModuleCat.of ℤ (ULift.{0} ℤ)) n) :
    @TopPair.singularCohomologyπ (ModuleCat.{0} ℤ) _ _ _ P (ModuleCat.of ℤ ℤ) ℤ _
        ModuleCat.instLinear (ModuleCat.of ℤ ℤ) n (P.uliftIntegralCohomologyEquiv n u) =
      P.fst.integralCohomologyEquiv n
        ((P.fst.uliftIntegralCohomologyIso n).hom (P.singularCohomologyπ _ ℤ _ n u)) := by
  rw [uliftIntegralCohomologyEquiv_apply, ← singularCohomologyLinearCongr_singularCohomologyπ,
    ← ConcreteCategory.comp_apply, ← singularCohomologyπ_singularCohomologyChainCoefficientMap,
    ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply (singularCohomologyValueMap ..),
    ← singularCohomologyπ_singularCohomologyValueMap, ConcreteCategory.comp_apply,
    TopCat.integralCohomologyEquiv_apply, TopCat.uliftIntegralCohomologyIso_hom, Iso.symm_hom,
    integralCoeffIso_inv_eq_uliftIntIso_inv]
  -- The two sides differ only in writing the coefficients `ℤ` as `ModuleCat.of ℤ ℤ` or as the
  -- unit `𝟙_ (ModuleCat ℤ)`, which Mathlib defines to be it.
  rfl

end ULiftInt

end TopPair

end
