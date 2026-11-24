/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap

/-!
# Smoothness of a moment map with values in a normed space

A moment map `μ : M → 𝔤*` takes values in `Module.Dual ℝ 𝔤`, which carries no topology, and
Tau Ceti's `TauCeti.SmoothTwoForm.IsMomentMap` asks only that each component `x ↦ μ x Z` be
smooth. When `𝔤` is finite-dimensional, this file reads `μ` through a linear map
`f : 𝔤* → V` into a real normed space and shows that `f ∘ μ` is smooth, hence continuous. The
proof writes `f ∘ μ` as a continuous linear map applied to the components of `μ` in a basis of
`𝔤`, as Tau Ceti's `TauCeti.SmoothTwoForm.IsMomentMap.contMDiff_sub` reads a moment map in a basis.

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
    ContMDiff I 𝓘(ℝ, V) ∞ (f ∘ μ) := by
  let b := Module.finBasis ℝ 𝔤
  let L : (Fin (finrank ℝ 𝔤) → ℝ) →L[ℝ] V :=
    LinearMap.toContinuousLinearMap
      ((f : Module.Dual ℝ 𝔤 →ₗ[ℝ] V) ∘ₗ b.dualBasis.equivFun.symm.toLinearMap)
  have hμ : f ∘ μ = L ∘ fun x i ↦ μ x (b i) := by
    funext x
    have hx : b.dualBasis.equivFun (μ x) = fun i ↦ μ x (b i) := funext (b.dualBasis_equivFun _)
    rw [Function.comp_apply, Function.comp_apply, ← hx, LinearMap.coe_toContinuousLinearMap',
      LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.coe_ofClass]
  rw [hμ]
  exact L.contMDiff.comp (contMDiff_pi_module_iff.2 fun i ↦ h.contMDiff (b i))

/-- **A moment map read through a linear map is continuous.** Let `μ : M → 𝔤*` be a moment map,
with `𝔤` finite-dimensional, and let `f : 𝔤* → V` be linear, with `V` a real normed space. Then
`f ∘ μ : M → V` is continuous. -/
theorem continuous_linearMap_comp (h : σ.IsMomentMap a μ) (f : F) :
    Continuous (f ∘ μ) :=
  (h.contMDiff_linearMap_comp f).continuous

end TauCeti.SmoothTwoForm.IsMomentMap

end
