/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import TauCeti.LinearAlgebra.FiniteDimensional.Extension

/-!
# Extending an injective linear map to a linear equivalence

Let `i : F → V` and `j : F → W` be injective linear maps into finite-dimensional vector spaces of
the same dimension. Then some linear equivalence `A : V ≃ W` satisfies `A ∘ i = j`
(`LinearMap.exists_linearEquiv_comp_eq_of_injective`).

This is Tau Ceti's `TauCeti.exists_linearEquiv_comp_eq_of_injective`, which treats the case
`W = V`, transported along a linear equivalence `V ≃ W` given by the equality of dimensions.
-/

public section

open Module

namespace LinearMap

variable {K V W F : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [AddCommGroup W]
  [Module K W] [AddCommGroup F] [Module K F] [FiniteDimensional K V] [FiniteDimensional K W]

/-- An injective linear map `j : F → W` extends along an injective linear map `i : F → V`, into a
space of the same finite dimension, to a linear equivalence `A : V ≃ W` with `A ∘ i = j`. -/
theorem exists_linearEquiv_comp_eq_of_injective {i : F →ₗ[K] V} {j : F →ₗ[K] W}
    (hi : Function.Injective i) (hj : Function.Injective j)
    (h : finrank K V = finrank K W) : ∃ A : V ≃ₗ[K] W, A.toLinearMap ∘ₗ i = j := by
  have : FiniteDimensional K F := Module.Finite.of_injective i hi
  let E := LinearEquiv.ofFinrankEq V W h
  obtain ⟨e, he⟩ := TauCeti.exists_linearEquiv_comp_eq_of_injective (f₂ := E.symm.toLinearMap ∘ₗ j)
    hi (by simpa using E.symm.injective.comp hj)
  refine ⟨e.trans E, LinearMap.ext fun s ↦ ?_⟩
  have hs := LinearMap.congr_fun he s
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply] at hs
  simp [hs]

end LinearMap
