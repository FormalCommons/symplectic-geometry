/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars

/-!
# Restricting the scalars of continuous linear maps is injective

A continuous `A`-linear map is determined by the continuous `R`-linear map that it defines, since
both have the same underlying function. This file states this for Mathlib's
`ContinuousLinearMap.restrictScalars`. The results are the continuous counterparts of Mathlib's
`LinearMap.restrictScalars_injective` and `LinearMap.restrictScalars_inj`.

## Main results

* `ContinuousLinearMap.restrictScalars_injective`, `ContinuousLinearMap.restrictScalars_inj`:
  restricting the scalars of continuous linear maps is injective.
-/

public section

namespace ContinuousLinearMap

variable {A M₁ M₂ : Type*} (R : Type*) [Semiring A] [Semiring R]
  [AddCommMonoid M₁] [Module A M₁] [Module R M₁] [TopologicalSpace M₁]
  [AddCommMonoid M₂] [Module A M₂] [Module R M₂] [TopologicalSpace M₂]
  [LinearMap.CompatibleSMul M₁ M₂ R A]

/-- A continuous `A`-linear map is determined by its restriction of scalars to `R`. -/
theorem restrictScalars_injective :
    Function.Injective (restrictScalars R : (M₁ →L[A] M₂) → M₁ →L[R] M₂) :=
  fun _ _ h ↦ ext fun x ↦ by simpa using DFunLike.congr_fun h x

/-- Two continuous `A`-linear maps are equal if and only if their restrictions of scalars to `R`
are. -/
@[simp]
theorem restrictScalars_inj (f g : M₁ →L[A] M₂) :
    f.restrictScalars R = g.restrictScalars R ↔ f = g :=
  (restrictScalars_injective R).eq_iff

end ContinuousLinearMap
