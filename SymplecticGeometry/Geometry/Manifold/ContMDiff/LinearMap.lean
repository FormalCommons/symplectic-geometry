/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiff.FiniteDimension

/-!
# Smooth families of linear maps on a finite-dimensional space

A linear map `f : E →ₗ[𝕜] F` on a finite-dimensional normed space `E` is continuous, and
Mathlib's `LinearMap.toContinuousLinearMap` reads it as a point of `E →L[𝕜] F`. This file shows
that a family `p ↦ f p` of such maps, indexed by a manifold, is `C^n` as a family of continuous
linear maps exactly when each of its values `p ↦ f p v` is `C^n`
(`LinearMap.contMDiff_toContinuousLinearMap_iff`). It is Tau Ceti's
`TauCeti.contMDiffAt_clm_apply` for families given as linear maps.
-/

public section

open scoped Manifold

namespace LinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {EN HN : Type*} [NormedAddCommGroup EN] [NormedSpace 𝕜 EN] [TopologicalSpace HN]
  {J : ModelWithCorners 𝕜 EN HN} {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
  {n : WithTop ℕ∞} {f : N → E →ₗ[𝕜] F}

/-- A family of linear maps on a finite-dimensional space, read as continuous linear maps, is
`C^n` exactly when its values at every fixed vector are. -/
theorem contMDiff_toContinuousLinearMap_iff :
    ContMDiff J 𝓘(𝕜, E →L[𝕜] F) n (fun p ↦ LinearMap.toContinuousLinearMap (f p)) ↔
      ∀ v, ContMDiff J 𝓘(𝕜, F) n fun p ↦ f p v := by
  simp only [ContMDiff, TauCeti.contMDiffAt_clm_apply, LinearMap.coe_toContinuousLinearMap']
  exact ⟨fun h v p ↦ h p v, fun h p v ↦ h v p⟩

end LinearMap

end
