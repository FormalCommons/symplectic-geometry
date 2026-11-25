/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Sigma
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# The inclusion of a component of a disjoint union as a local diffeomorphism

For a family `M i` of `C^n` manifolds on a common model, the inclusion `Sigma.mk i` of the
component `M i` into the disjoint union `Σ i, M i` (Tau Ceti's `ChartedSpace.sigma`) is a `C^n`
local diffeomorphism: near `x`, it is the chart of `M i` at `x` followed by the inverse of the
chart of `Σ i, M i` at `⟨i, x⟩`, since the second is the first read on the copy of `M i`
(`ChartedSpace.sigma_chartAt_mk_apply`).

## Main results

* `TauCeti.isLocalDiffeomorph_sigmaMk`: the inclusion of a component of a disjoint union is a
  `C^n` local diffeomorphism.
-/

public section

open Set Topology Manifold

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {n : WithTop ℕ∞} {ι : Type*} {M : ι → Type*} [∀ i, TopologicalSpace (M i)]
  [∀ i, ChartedSpace H (M i)] [∀ i, IsManifold I n (M i)]

/-- The inclusion `Sigma.mk i` of the component `M i` into the disjoint union `Σ i, M i` is a
`C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_sigmaMk (i : ι) :
    IsLocalDiffeomorph I I n (Sigma.mk i : M i → Σ i, M i) := fun x ↦ by
  have hx : (⟨i, x⟩ : Σ i, M i) ∈ (chartAt H (⟨i, x⟩ : Σ i, M i)).source :=
    mem_chart_source H _
  have h₁ : IsLocalDiffeomorphAt I I n (chartAt H x) x :=
    (chartAt H x).isLocalDiffeomorphAt_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas x) (mem_chart_source H x)
  have h₂ : IsLocalDiffeomorphAt I I n (chartAt H (⟨i, x⟩ : Σ i, M i)).symm (chartAt H x x) := by
    rw [← ChartedSpace.sigma_chartAt_mk_apply]
    exact (chartAt H _).isLocalDiffeomorphAt_symm_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas _) ((chartAt H _).map_source hx)
  refine (h₁.comp (hg := h₂)).congr_of_eventuallyEq ?_
  filter_upwards [(chartAt H x).open_source.mem_nhds (mem_chart_source H x)] with y hy
  have hy' : (⟨i, y⟩ : Σ i, M i) ∈ (chartAt H (⟨i, x⟩ : Σ i, M i)).source := by
    rw [ChartedSpace.sigma_chartAt_source]
    exact mem_image_of_mem _ hy
  rw [Function.comp_apply, ← ChartedSpace.sigma_chartAt_mk_apply (x := x),
    (chartAt H _).left_inv hy']

end TauCeti

end
