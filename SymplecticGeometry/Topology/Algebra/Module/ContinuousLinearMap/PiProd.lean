/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import SymplecticGeometry.LinearAlgebra.Prod

/-!
# Injectivity of a continuous linear map with one column added

Over a topological division ring `K`, a continuous linear map `A : V →L[K] W` and a vector
`z : W` give the continuous linear map `A.coprod (toSpanSingleton K z) : V × K →L[K] W`,
`(v, t) ↦ A v + t • z`. It is injective exactly when `A` is injective and `z` is not in the
range of `A` (`ContinuousLinearMap.injective_coprod_toSpanSingleton_iff`); this is
`LinearMap.injective_coprod_toSpanSingleton_iff` for the underlying linear maps.
-/

public section

open Function

/-- Over a topological division ring, the continuous linear map `(v, t) ↦ A v + t • z` is
injective exactly when `A` is injective and `z` is not in the range of `A`. -/
theorem ContinuousLinearMap.injective_coprod_toSpanSingleton_iff {K V W : Type*}
    [DivisionRing K] [TopologicalSpace K] [AddCommGroup V] [Module K V] [TopologicalSpace V]
    [AddCommGroup W] [Module K W] [TopologicalSpace W] [ContinuousAdd W] [ContinuousSMul K W]
    (A : V →L[K] W) (z : W) :
    Injective (A.coprod (ContinuousLinearMap.toSpanSingleton K z)) ↔
      Injective A ∧ z ∉ A.range :=
  LinearMap.injective_coprod_toSpanSingleton_iff (A : V →ₗ[K] W) z

end
