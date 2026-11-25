/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Injective linear parametrizations of a subspace

A finite-dimensional subspace `W` of a vector space `E` is the range of an injective linear map
out of any finite-dimensional space `F` with `dim F = dim W`
(`Submodule.exists_linearMap_injective_range_eq`): compose a linear isomorphism `F ≃ W`
(`LinearEquiv.ofFinrankEq`) with the inclusion of `W`.
-/

public section

open Module

namespace Submodule

variable {K E F : Type*} [DivisionRing K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- A finite-dimensional subspace `W` of `E` is the range of an injective linear map
`L : F →ₗ[K] E`, for any finite-dimensional `F` with `dim F = dim W`. -/
theorem exists_linearMap_injective_range_eq (W : Submodule K E) [FiniteDimensional K W]
    (h : finrank K F = finrank K W) :
    ∃ L : F →ₗ[K] E, Function.Injective L ∧ LinearMap.range L = W := by
  let e := LinearEquiv.ofFinrankEq F W h
  exact ⟨W.subtype ∘ₗ e.toLinearMap, W.injective_subtype.comp e.injective, by
    rw [LinearMap.range_comp_of_range_eq_top _ e.range, range_subtype]⟩

end Submodule

end
