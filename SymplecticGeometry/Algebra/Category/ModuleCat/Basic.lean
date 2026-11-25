/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Negatives and multiples of morphisms of modules

Multiplying a morphism of `ModuleCat R` by a unit of `ℤ`, such as a sign `(-1)^k`, does not change
whether it is bijective. Diagram chases use this when a square commutes only up to a sign. The
negative of a linear map is the negative of the morphism it defines (`ModuleCat.ofHom_neg`).

## Main results

* `ModuleCat.bijective_zsmul_iff`
* `ModuleCat.ofHom_neg`
-/

public section

open CategoryTheory

namespace ModuleCat

universe v

variable {R : Type*} [Ring R]

/-- Multiplying a morphism of modules by a unit of `ℤ` does not change whether it is bijective. -/
theorem bijective_zsmul_iff {M N : ModuleCat R} (f : M ⟶ N) {u : ℤ} (hu : IsUnit u) :
    Function.Bijective (u • f) ↔ Function.Bijective f := by
  have h : ⇑(ConcreteCategory.hom (u • f)) = (u • ·) ∘ ⇑(ConcreteCategory.hom f) := by
    ext x
    simp
  rw [h]
  exact Function.Bijective.of_comp_iff' hu.smul_bijective _

/-- `ModuleCat.ofHom` commutes with negation. -/
@[simp]
theorem ofHom_neg {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) : ofHom (-f) = -ofHom f :=
  (rfl)

end ModuleCat
