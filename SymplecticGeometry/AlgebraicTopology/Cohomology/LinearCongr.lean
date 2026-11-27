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
cohomology modules, Mathlib's `LinearEquiv.cast` along `e`. It is the identity for `e = rfl`,
agrees with `eqToHom` along the equality of the two modules, and commutes with the maps induced
by continuous maps. Through `TopCat.singularCohomologyLinearCongr_apply`, Tau Ceti's
`TopCat.singularCohomologyChainCoefficientMap_comp_eqToHom` and `TopCat.singularCup_eqToHom`
give its compatibility with changes of chain coefficients and with cup products.

## Main definitions

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
* `TopCat.singularCohomologyLinearCongr_naturality`: it commutes with
  `TopCat.singularCohomologyMap`.
-/

public section

noncomputable section

open CategoryTheory Limits

universe w v u

namespace TopCat

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] {k : Type*} [Ring k]

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

/-- **Naturality of `TopCat.singularCohomologyLinearCongr`**: it commutes with the maps induced
by a continuous map `f : X ⟶ Y`. -/
theorem singularCohomologyLinearCongr_naturality {L₁ L₂ : Linear k C} (e : L₁ = L₂)
    {X Y : TopCat.{w}} (f : X ⟶ Y) (R M : C) (n : ℕ)
    (a : @TopCat.singularCohomology C _ _ _ R k _ L₁ M Y n) :
    singularCohomologyLinearCongr e X R M n
        (@TopCat.singularCohomologyMap C _ _ _ R k _ L₁ M X Y f n a) =
      @TopCat.singularCohomologyMap C _ _ _ R k _ L₂ M X Y f n
        (singularCohomologyLinearCongr e Y R M n a) := by
  subst e
  simp only [singularCohomologyLinearCongr_refl, LinearEquiv.refl_apply]

end TopCat

end
