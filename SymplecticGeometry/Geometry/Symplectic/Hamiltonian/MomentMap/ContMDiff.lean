/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.ContMDiff.Dual
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap

/-!
# Smoothness of a moment map with values in a normed space

A moment map `μ : M → 𝔤*` takes values in `Module.Dual ℝ 𝔤`, which carries no topology, and
Tau Ceti's `TauCeti.SmoothTwoForm.IsMomentMap` asks only that each component `x ↦ μ x Z` be
smooth. When `𝔤` is finite-dimensional, this file reads `μ` through a linear map
`f : 𝔤* → V` into a real normed space and shows that `f ∘ μ` is smooth, hence continuous. Every
functional on `𝔤*` is the evaluation at an element of `𝔤` (Mathlib's `Module.evalEquiv`), so it
takes `μ` to a smooth function, and `SymplecticGeometry.contMDiff_linearMap_comp_of_dual`
concludes.

## Main results

* `TauCeti.SmoothTwoForm.IsMomentMap.contMDiff_linearMap_comp`: `f ∘ μ` is smooth.
* `TauCeti.SmoothTwoForm.IsMomentMap.continuous_linearMap_comp`: `f ∘ μ` is continuous.
-/

public section

open Module
open scoped ContDiff Manifold

namespace TauCeti.SmoothTwoForm.IsMomentMap

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [FiniteDimensional ℝ 𝔤]
  {σ : SmoothTwoForm I M} {a : InfinitesimalAction 𝔤 I M} {μ : M → Module.Dual ℝ 𝔤}
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {F : Type*} [FunLike F (Module.Dual ℝ 𝔤) V] [LinearMapClass F ℝ (Module.Dual ℝ 𝔤) V]

/-- **A moment map read through a linear map is smooth.** Let `μ : M → 𝔤*` be a moment map, with
`𝔤` finite-dimensional, and let `f : 𝔤* → V` be linear (a linear map, a linear equivalence, or
any `LinearMapClass`), with `V` a real normed space. Then `f ∘ μ : M → V` is smooth. -/
theorem contMDiff_linearMap_comp (h : σ.IsMomentMap a μ) (f : F) :
    ContMDiff I 𝓘(ℝ, V) ∞ (f ∘ μ) :=
  SymplecticGeometry.contMDiff_linearMap_comp_of_dual (fun g ↦ by
    simpa using h.contMDiff ((evalEquiv ℝ 𝔤).symm g)) f

/-- **A moment map read through a linear map is continuous.** Let `μ : M → 𝔤*` be a moment map,
with `𝔤` finite-dimensional, and let `f : 𝔤* → V` be linear, with `V` a real normed space. Then
`f ∘ μ : M → V` is continuous. -/
theorem continuous_linearMap_comp (h : σ.IsMomentMap a μ) (f : F) :
    Continuous (f ∘ μ) :=
  (h.contMDiff_linearMap_comp f).continuous

end TauCeti.SmoothTwoForm.IsMomentMap

end
