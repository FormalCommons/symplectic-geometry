/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Injectivity from a complement of the range

Let `f : V →ₗ[K] W` be a linear map from a finite-dimensional vector space, and let `P` be a
complement of its range in `W`. Then `f` is injective as soon as the dimensions of `V` and `P`
add up to that of `W` (`LinearMap.injective_of_isCompl_range`): the range then has the
dimension of `V`, so by rank–nullity the kernel is zero.
-/

public section

open Module

namespace LinearMap

variable {K V W : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [AddCommGroup W]
  [Module K W]

/-- A linear map `f : V → W` out of a finite-dimensional space is injective if its range has a
complement `P` with `dim V + dim P = dim W`. -/
theorem injective_of_isCompl_range [FiniteDimensional K V] {f : V →ₗ[K] W}
    {P : Submodule K W} (h : IsCompl (range f) P)
    (hd : finrank K V + finrank K P = finrank K W) : Function.Injective f := by
  rw [← ker_eq_bot, ← Submodule.finrank_eq_zero]
  have hrk := finrank_range_add_finrank_ker f
  by_cases hW : FiniteDimensional K W
  · have := Submodule.finrank_add_eq_of_isCompl h
    omega
  · rw [finrank_of_not_finite hW] at hd
    omega

end LinearMap

end
