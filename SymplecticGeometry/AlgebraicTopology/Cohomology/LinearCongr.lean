/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Basic

/-!
# Change of linear structure in singular cohomology

Singular cohomology `X.singularCohomology R k M n` depends on a structure `Linear k C` of the
category `C` of coefficients. A category can carry two such structures that are equal without
being definitionally equal: `ModuleCat ℤ` has Mathlib's `ModuleCat.instLinear` and the structure
`CategoryTheory.Linear.preadditiveIntLinear` of every preadditive category, which are equal by
`CategoryTheory.Linear.subsingletonInt`. For an equality `e : L₁ = L₂` of two structures,
`TopCat.singularCohomologyLinearCongr e X R M n` is the `k`-linear equivalence between the two
cohomology modules, Mathlib's `LinearEquiv.cast` along `e`. It is the identity for `e = rfl`
and agrees with `eqToHom` along the equality of the two modules. Through
`TopCat.singularCohomologyLinearCongr_apply`, Tau Ceti's
`TopCat.singularCohomologyMap_comp_eqToHom`,
`TopCat.singularCohomologyChainCoefficientMap_comp_eqToHom` and `TopCat.singularCup_eqToHom`
give its compatibility with the maps induced by continuous maps, with changes of chain
coefficients and with cup products.

## Main definitions

* `TopCat.singularCochainComplexLinearCongr`: the identification of singular cochains for two
  equal linear structures of the category of coefficients, the identity in each degree.
* `TopCat.singularCohomologyLinearCongr`: the identification of singular cohomology for two
  equal linear structures of the category of coefficients.

## Main results

* `TopCat.singularCohomologyLinearCongr_refl`: it is the identity for `e = rfl`.
* `TopCat.singularCohomologyLinearCongr_symm`, `TopCat.singularCohomologyLinearCongr_trans`: its
  inverse is the change along `e.symm`, and two changes compose to the change along `e.trans e'`.
* `TopCat.singularCohomologyLinearCongr_apply_apply`: the same composition law for two changes
  applied in turn to a class, so that `simp` closes round trips.
* `TopCat.singularCohomologyLinearCongr_apply`: on a class it is `eqToHom` along the equality of
  the two cohomology modules, the form in which Tau Ceti changes the linear structure.
-/

public section

noncomputable section

open CategoryTheory Limits

universe w v u

namespace TopCat

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] {k : Type*} [Ring k]

/-- The singular cochain complex `C^•(X; R, M)` for two equal structures `L₁ = L₂` of `C` as a
`k`-linear category: in each degree, the identity of cochains, which is `k`-linear for both
structures. -/
def singularCochainComplexLinearCongr {L₁ L₂ : Linear k C} (e : L₁ = L₂) (X : TopCat.{w})
    (R M : C) :
    @singularCochainComplex C _ _ _ R k _ L₁ M X ≅ @singularCochainComplex C _ _ _ R k _ L₂ M X :=
  HomologicalComplex.Hom.isoOfComponents
    (C₁ := @singularCochainComplex C _ _ _ R k _ L₁ M X)
    (C₂ := @singularCochainComplex C _ _ _ R k _ L₂ M X)
    (fun _ ↦
      { hom := ModuleCat.homEquiv.symm
          { toFun := id
            map_add' := fun _ _ ↦ rfl
            map_smul' := by subst e; exact fun _ _ ↦ rfl }
        inv := ModuleCat.homEquiv.symm
          { toFun := id
            map_add' := fun _ _ ↦ rfl
            map_smul' := by subst e; exact fun _ _ ↦ rfl } })
    fun _ _ _ ↦ rfl

theorem singularCochainComplexLinearCongr_def {L₁ L₂ : Linear k C} (e : L₁ = L₂)
    (X : TopCat.{w}) (R M : C) :
    singularCochainComplexLinearCongr e X R M =
      HomologicalComplex.Hom.isoOfComponents
        (C₁ := @singularCochainComplex C _ _ _ R k _ L₁ M X)
        (C₂ := @singularCochainComplex C _ _ _ R k _ L₂ M X)
        (fun _ ↦
          { hom := ModuleCat.homEquiv.symm
              { toFun := id
                map_add' := fun _ _ ↦ rfl
                map_smul' := by subst e; exact fun _ _ ↦ rfl }
            inv := ModuleCat.homEquiv.symm
              { toFun := id
                map_add' := fun _ _ ↦ rfl
                map_smul' := by subst e; exact fun _ _ ↦ rfl } })
        fun _ _ _ ↦ rfl :=
  (rfl)

/-- The change of linear structure on cochains is the identity on each cochain. -/
theorem singularCochainComplexLinearCongr_hom_f_apply {L₁ L₂ : Linear k C} (e : L₁ = L₂)
    (X : TopCat.{w}) (R M : C) (p : ℕ) (φ : ((toSSet.obj X).chainComplex R).X p ⟶ M) :
    (singularCochainComplexLinearCongr e X R M).hom.f p φ = φ :=
  (rfl)

/-- The inverse change of linear structure on cochains is the identity on each cochain. -/
theorem singularCochainComplexLinearCongr_inv_f_apply {L₁ L₂ : Linear k C} (e : L₁ = L₂)
    (X : TopCat.{w}) (R M : C) (p : ℕ) (φ : ((toSSet.obj X).chainComplex R).X p ⟶ M) :
    (singularCochainComplexLinearCongr e X R M).inv.f p φ = φ :=
  (rfl)

/-- The identification of singular cohomology `Hⁿ(X; R, M)` for two equal structures
`L₁ = L₂` of `C` as a `k`-linear category: Mathlib's `LinearEquiv.cast` along `e`, for cohomology
as a family indexed by the structure. It is the identity when the two structures are the same
(`TopCat.singularCohomologyLinearCongr_refl`). -/
def singularCohomologyLinearCongr {L₁ L₂ : Linear k C} (e : L₁ = L₂) (X : TopCat.{w}) (R M : C)
    (n : ℕ) :
    @TopCat.singularCohomology C _ _ _ R k _ L₁ M X n ≃ₗ[k]
      @TopCat.singularCohomology C _ _ _ R k _ L₂ M X n :=
  LinearEquiv.cast (R := k)
    (M := fun L : Linear k C ↦ @TopCat.singularCohomology C _ _ _ R k _ L M X n) e

theorem singularCohomologyLinearCongr_def {L₁ L₂ : Linear k C} (e : L₁ = L₂) (X : TopCat.{w})
    (R M : C) (n : ℕ) :
    singularCohomologyLinearCongr e X R M n = LinearEquiv.cast (R := k)
      (M := fun L : Linear k C ↦ @TopCat.singularCohomology C _ _ _ R k _ L M X n) e :=
  (rfl)

@[simp]
theorem singularCohomologyLinearCongr_refl (L : Linear k C) (X : TopCat.{w}) (R M : C) (n : ℕ) :
    singularCohomologyLinearCongr (rfl : L = L) X R M n = LinearEquiv.refl k _ :=
  (rfl)

@[simp]
theorem singularCohomologyLinearCongr_symm {L₁ L₂ : Linear k C} (e : L₁ = L₂) (X : TopCat.{w})
    (R M : C) (n : ℕ) :
    (singularCohomologyLinearCongr e X R M n).symm =
      singularCohomologyLinearCongr e.symm X R M n := by
  subst e
  rfl

@[simp]
theorem singularCohomologyLinearCongr_trans {L₁ L₂ L₃ : Linear k C} (e : L₁ = L₂)
    (e' : L₂ = L₃) (X : TopCat.{w}) (R M : C) (n : ℕ) :
    (singularCohomologyLinearCongr e X R M n).trans (singularCohomologyLinearCongr e' X R M n) =
      singularCohomologyLinearCongr (e.trans e') X R M n := by
  subst e e'
  rfl

@[simp]
theorem singularCohomologyLinearCongr_apply_apply {L₁ L₂ L₃ : Linear k C} (e : L₁ = L₂)
    (e' : L₂ = L₃) (X : TopCat.{w}) (R M : C) (n : ℕ)
    (a : @TopCat.singularCohomology C _ _ _ R k _ L₁ M X n) :
    singularCohomologyLinearCongr e' X R M n (singularCohomologyLinearCongr e X R M n a) =
      singularCohomologyLinearCongr (e.trans e') X R M n a := by
  subst e e'
  rfl

/-- `TopCat.singularCohomologyLinearCongr e` acts on a class as `eqToHom` along the equality of
the two cohomology modules that `e` gives, the form in which Tau Ceti changes the linear structure
(`TopCat.singularCohomologyMap_comp_eqToHom`, `TopCat.integralCohomologyEquiv`). -/
theorem singularCohomologyLinearCongr_apply {L₁ L₂ : Linear k C} (e : L₁ = L₂) (X : TopCat.{w})
    (R M : C) (n : ℕ) (a : @TopCat.singularCohomology C _ _ _ R k _ L₁ M X n) :
    singularCohomologyLinearCongr e X R M n a =
      eqToHom (congrArg (fun L : Linear k C ↦
        @TopCat.singularCohomology C _ _ _ R k _ L M X n) e) a := by
  subst e
  simp

end TopCat

end
