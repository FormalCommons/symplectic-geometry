/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.NormSq
import SymplecticGeometry.Geometry.Manifold.ContMDiff.Dual

/-!
# Smoothness of a moment map with values in a normed space

A moment map `μ : M → 𝔤*` takes values in `Module.Dual ℝ 𝔤`, which carries no topology, and
Tau Ceti's `TauCeti.SmoothTwoForm.IsMomentMap` asks only that each component `x ↦ μ x Z` be
smooth. When `𝔤` is finite-dimensional, this file reads `μ` through a linear map
`f : 𝔤* → V` into a real normed space and shows that `f ∘ μ` is smooth, hence continuous. Every
functional on `𝔤*` is the evaluation at an element of `𝔤` (Mathlib's `Module.evalEquiv`), so it
takes `μ` to a smooth function, and `SymplecticGeometry.contMDiff_linearMap_comp_of_dual`
concludes.

It also records that the components of `μ` are smooth when `-μ` is a moment map, the sign
convention of many texts, and that their derivatives are then values of `σ`. The norm square
`TauCeti.momentNormSq μ K` of `μ` is smooth when `-μ` is a moment map, as Tau Ceti's
`TauCeti.SmoothTwoForm.IsMomentMap.contMDiff_momentNormSq` shows when `μ` is one.

## Main results

* `TauCeti.SmoothTwoForm.IsMomentMap.contMDiff_linearMap_comp`: `f ∘ μ` is smooth.
* `TauCeti.SmoothTwoForm.IsMomentMap.continuous_linearMap_comp`: `f ∘ μ` is continuous.
* `TauCeti.SmoothTwoForm.IsMomentMap.contMDiff_of_neg`: if `-μ` is a moment map, the components
  of `μ` are smooth.
* `TauCeti.SmoothTwoForm.IsMomentMap.mvfderiv_apply_of_neg`: if `-μ` is a moment map for the
  infinitesimal action `a`, the derivative of `x ↦ μ x Z` in the direction `v` is `-σ(a Z x, v)`.
* `TauCeti.SmoothTwoForm.IsMomentMap.contMDiff_momentNormSq_of_neg`: the norm square of `μ` is
  smooth if `-μ` is a moment map.
* `TauCeti.SmoothTwoForm.IsMomentMap.exists_pos_forall_sqrt_momentNormSq_le_of_neg`: on a compact
  manifold, the root of the norm square of `μ` is bounded.
-/

public section

open Module
open scoped ContDiff Manifold

namespace TauCeti.SmoothTwoForm.IsMomentMap

/-- If `-μ` is a moment map, each component `x ↦ μ x Z` of `μ` is smooth. -/
theorem contMDiff_of_neg {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] {σ : SmoothTwoForm I M}
    {a : InfinitesimalAction 𝔤 I M} {μ : M → Module.Dual ℝ 𝔤}
    (h : σ.IsMomentMap a fun x ↦ -μ x) (Z : 𝔤) :
    ContMDiff I 𝓘(ℝ) ∞ fun x ↦ μ x Z := by
  simpa using (h.contMDiff Z).neg

/-- If `-μ` is a moment map for `σ` and the infinitesimal action `a`, the derivative at `x` of
the component `y ↦ μ y Z` of `μ`, in the direction `v`, is `-σ(a Z x, v)`. -/
theorem mvfderiv_apply_of_neg {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] {σ : SmoothTwoForm I M}
    {a : InfinitesimalAction 𝔤 I M} {μ : M → Module.Dual ℝ 𝔤}
    (h : σ.IsMomentMap a fun x ↦ -μ x) (Z : 𝔤) (x : M) (v : TangentSpace I x) :
    mvfderiv I (fun y ↦ μ y Z) x v = -SmoothBundleForm.eval₂ σ x (a Z x) v := by
  rw [h.eval₂_apply Z x v, show (fun y ↦ μ y Z) = fun y ↦ -(-μ y) Z by ext; simp,
    mvfderiv_fun_neg, neg_apply]

section NormSq

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [FiniteDimensional ℝ 𝔤]
  {σ : SmoothTwoForm I M} {a : InfinitesimalAction 𝔤 I M} {μ : M → Module.Dual ℝ 𝔤}

/-- If `-μ` is a moment map, the norm square `x ↦ μ x (K (μ x))` of `μ` is smooth, for any
linear map `K : 𝔤* → 𝔤`. -/
theorem contMDiff_momentNormSq_of_neg {K : Module.Dual ℝ 𝔤 →ₗ[ℝ] 𝔤}
    (h : σ.IsMomentMap a fun x ↦ -μ x) : ContMDiff I 𝓘(ℝ) ∞ (momentNormSq μ K) := by
  simpa only [SymplecticGeometry.momentNormSq_neg'] using h.contMDiff_momentNormSq (K := K)

/-- If `-μ` is a moment map on a compact manifold, the root `√(μ x (K (μ x)))` of the norm square
of `μ` has a positive upper bound on `M`, for any linear map `K : 𝔤* → 𝔤`. -/
theorem exists_pos_forall_sqrt_momentNormSq_le_of_neg [CompactSpace M]
    {K : Module.Dual ℝ 𝔤 →ₗ[ℝ] 𝔤} (h : σ.IsMomentMap a fun x ↦ -μ x) :
    ∃ L, 0 < L ∧ ∀ x, √(momentNormSq μ K x) ≤ L := by
  obtain ⟨L, hL⟩ := isCompact_univ.bddAbove_image
    (h.contMDiff_momentNormSq_of_neg (K := K)).continuous.sqrt.continuousOn
  exact ⟨max L 1, lt_max_of_lt_right one_pos,
    fun x ↦ le_max_of_le_left (hL ⟨x, Set.mem_univ x, rfl⟩)⟩

end NormSq

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
