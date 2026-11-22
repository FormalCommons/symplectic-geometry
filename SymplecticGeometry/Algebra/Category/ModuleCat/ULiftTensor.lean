/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Monoidal.Unit

/-!
# Associativity of the multiplication of `ULift R`

Tau Ceti's `ModuleCat.uliftTensorSelfIso R` identifies `ULift R ⊗ ULift R` with `ULift R` by
`a ⊗ b ↦ a * b`. This multiplication is associative as a morphism of `ModuleCat R`
(`ModuleCat.uliftTensorSelfIso_hom_assoc`): the two ways of multiplying three factors agree after
the associator of the tensor product.
-/

public section

open CategoryTheory MonoidalCategory
open scoped TensorProduct

universe u

namespace ModuleCat

variable (R : Type u) [CommRing R]

/-- The multiplication `ULift R ⊗ ULift R ⟶ ULift R` of `ModuleCat.uliftTensorSelfIso` is
associative: `(a * b) * c = a * (b * c)`, after the associator of the tensor product. -/
theorem uliftTensorSelfIso_hom_assoc :
    ((uliftTensorSelfIso R).hom ▷ of R (ULift.{u} R)) ≫ (uliftTensorSelfIso R).hom =
      (α_ _ _ _).hom ≫ (of R (ULift.{u} R) ◁ (uliftTensorSelfIso R).hom) ≫
        (uliftTensorSelfIso R).hom := by
  refine MonoidalCategory.tensor_ext₃' fun a b c ↦ ?_
  -- the whiskerings and the associator act on pure tensors by definition
  -- (`ModuleCat.MonoidalCategory.whiskerRight_apply` and its neighbours), which `simp` does not
  -- see through the carrier of `ModuleCat.of R (ULift R)`
  change (uliftTensorSelfIso R).hom ((uliftTensorSelfIso R).hom (a ⊗ₜ b) ⊗ₜ c) =
    (uliftTensorSelfIso R).hom (a ⊗ₜ (uliftTensorSelfIso R).hom (b ⊗ₜ c))
  rw [uliftTensorSelfIso_hom_tmul R a b, uliftTensorSelfIso_hom_tmul R b c,
    uliftTensorSelfIso_hom_tmul, uliftTensorSelfIso_hom_tmul]
  exact congrArg ULift.up (mul_assoc _ _ _)

end ModuleCat
