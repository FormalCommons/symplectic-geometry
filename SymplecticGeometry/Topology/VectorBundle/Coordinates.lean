/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.VectorBundle.Constructions
public import Mathlib.Topology.VectorBundle.Hom
public import SymplecticGeometry.Topology.Algebra.Module.BilinearForm

/-!
# Coordinate expressions on vector bundles

Let `V` be a topological vector bundle over `B` with model fibre `F`. A continuous bilinear form
`σ : V x →L[𝕜] V x →L[𝕜] 𝕜` is a point of the bundle of continuous bilinear forms on `V`, the hom
bundle from `V` to the hom bundle from `V` to `Bundle.Trivial B 𝕜`. This file shows that its
coordinate expression in the trivialization at `x₀`, wherever `x` lies in its base set, is `σ`
carried in both arguments along the fibre equivalence of that trivialization
(`ContinuousLinearMap.inCoordinates_eq_bilinearCongr`).

It is the counterpart for bilinear forms of Tau Ceti's
`ContinuousLinearMap.inCoordinates_eq_conjContinuousAlgEquiv`, for endomorphisms.

The file also gives a way to compute the coordinate expression of any fibrewise continuous
linear map `ϕ : E₁ x →L[𝕜] E₂ y`: it is `c : F₁ →L[𝕜] F₂` as soon as `ϕ` takes each vector with
coordinate `w` to one with coordinate `c w`
(`ContinuousLinearMap.inCoordinates_eq_of_forall_apply`).
-/

public section

open Bundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : B → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- A continuous bilinear form on `V x`, read in the trivialization at `x₀` whose base set
contains `x`, is the form carried in both arguments along the fibre equivalence of that
trivialization. -/
theorem ContinuousLinearMap.inCoordinates_eq_bilinearCongr {x₀ x : B}
    (hx : x ∈ (trivializationAt F V x₀).baseSet) (σ : V x →L[𝕜] V x →L[𝕜] 𝕜) :
    ContinuousLinearMap.inCoordinates F V (F →L[𝕜] 𝕜) (fun y ↦ V y →L[𝕜] Trivial B 𝕜 y)
        x₀ x x₀ x σ =
      ((trivializationAt F V x₀).continuousLinearEquivAt 𝕜 x hx).bilinearCongr σ := by
  ext v w
  rw [inCoordinates_apply_eq₂ (E₃ := Trivial B 𝕜) hx hx (Set.mem_univ _)]
  simp

section OfForallApply

variable {B' : Type*} [TopologicalSpace B']
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {E₁ : B → Type*} [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [∀ x, TopologicalSpace (E₁ x)] [TopologicalSpace (TotalSpace F₁ E₁)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₂ : B' → Type*} [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [∀ x, TopologicalSpace (E₂ x)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

/-- Let `x` lie in the base set of the trivialization of `E₁` at `x₀`, and `y` in that of the
trivialization of `E₂` at `y₀`. If a continuous linear map `ϕ : E₁ x →L[𝕜] E₂ y` sends each
vector to one whose coordinate at `y₀` is the image under `c` of its coordinate at `x₀`, then
`ϕ` read in these trivializations is `c`. -/
theorem ContinuousLinearMap.inCoordinates_eq_of_forall_apply {x₀ x : B} {y₀ y : B'}
    {ϕ : E₁ x →L[𝕜] E₂ y} {c : F₁ →L[𝕜] F₂}
    (hx : x ∈ (trivializationAt F₁ E₁ x₀).baseSet)
    (hy : y ∈ (trivializationAt F₂ E₂ y₀).baseSet)
    (h : ∀ v : E₁ x,
      (trivializationAt F₂ E₂ y₀ ⟨y, ϕ v⟩).2 = c (trivializationAt F₁ E₁ x₀ ⟨x, v⟩).2) :
    ContinuousLinearMap.inCoordinates F₁ E₁ F₂ E₂ x₀ x y₀ y ϕ = c := by
  ext w
  simp only [inCoordinates, comp_apply, Trivialization.symmL_apply _ hx,
    Trivialization.continuousLinearMapAt_apply_of_mem _ _ hy, h,
    Trivialization.apply_mk_symm _ hx]

end OfForallApply

end
