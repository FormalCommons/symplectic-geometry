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
# Coordinates of bilinear forms on a vector bundle

Let `V` be a topological vector bundle over `B` with model fibre `F`. A continuous bilinear form
`σ : V x →L[𝕜] V x →L[𝕜] 𝕜` is a point of the bundle of continuous bilinear forms on `V`, the hom
bundle from `V` to the hom bundle from `V` to `Bundle.Trivial B 𝕜`. This file shows that its
coordinate expression in the trivialization at `x₀`, wherever `x` lies in its base set, is `σ`
carried in both arguments along the fibre equivalence of that trivialization
(`ContinuousLinearMap.inCoordinates_eq_bilinearCongr`).

It is the counterpart for bilinear forms of Tau Ceti's
`ContinuousLinearMap.inCoordinates_eq_conjContinuousAlgEquiv`, for endomorphisms.
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

end
