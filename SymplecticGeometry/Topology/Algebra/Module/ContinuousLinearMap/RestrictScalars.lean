/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Restricting the scalars of continuous linear maps is injective

A continuous `A`-linear map is determined by the continuous `R`-linear map that it defines, since
both have the same underlying function. This file states this for Mathlib's
`ContinuousLinearMap.restrictScalars` and for its continuous linear version
`ContinuousLinearMap.restrictScalarsL`. They are the continuous counterparts of Mathlib's
`LinearMap.restrictScalars_injective`.

## Main results

* `ContinuousLinearMap.restrictScalars_injective`, `ContinuousLinearMap.restrictScalars_inj`:
  restricting the scalars of continuous linear maps is injective.
* `ContinuousLinearMap.restrictScalarsL_injective`: so is its continuous linear version.
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

/-- `ContinuousLinearMap.restrictScalarsL`, which restricts the scalars of continuous linear maps
from `𝕜` to `𝕜'` as a continuous `𝕜''`-linear map, is injective. -/
theorem restrictScalarsL_injective (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E F : Type*)
    [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E] [ContinuousSMul 𝕜 E]
    [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F] [Module 𝕜 F]
    (𝕜' : Type*) [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜' 𝕜]
    [Module 𝕜' E] [IsScalarTower 𝕜' 𝕜 E] [Module 𝕜' F] [IsScalarTower 𝕜' 𝕜 F]
    (𝕜'' : Type*) [Ring 𝕜''] [Module 𝕜'' F] [ContinuousConstSMul 𝕜'' F]
    [SMulCommClass 𝕜 𝕜'' F] [SMulCommClass 𝕜' 𝕜'' F] :
    Function.Injective (restrictScalarsL 𝕜 E F 𝕜' 𝕜'') := by
  rw [coe_restrict_scalarsL']
  exact restrictScalars_injective 𝕜'

end ContinuousLinearMap
