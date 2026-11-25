/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Hom

/-!
# Finite bundle atlases: chart images and chart readings

Four facts about Tau Ceti's finite bundle atlases `TauCeti.FiniteBundleAtlas`.

* `TauCeti.FiniteBundleAtlas.image_subset_target_inter_preimage_symm`: the image of chart `i` lies
  in the chart target, and the inverse chart takes it into the base set of bundle chart `i`. This
  is the open set on which the chart readings of smooth sections are smooth.
* `TauCeti.FiniteBundleAtlas.coord_sub`: on the image of a chart, the chart reading of a
  difference of sections is the difference of their readings, next to Tau Ceti's
  `TauCeti.FiniteBundleAtlas.coord_add` and `TauCeti.FiniteBundleAtlas.coord_smul`.
* `TauCeti.FiniteBundleAtlas.coord_hom_apply_self`: Tau Ceti's
  `TauCeti.FiniteBundleAtlas.coord_hom_apply` for a section of the endomorphism bundle of `V`,
  with the result read in `A` itself rather than in `A.ofBaseSet A.closure_dom_subset_baseSet`.
* `TauCeti.FiniteBundleAtlas.contMDiff_of_contDiffOn_coord`: a section whose readings are `Cᵏ` on
  every chart image is `Cᵏ`, a converse of Tau Ceti's `TauCeti.FiniteBundleAtlas.contDiffOn_coord`.
-/

public section

namespace TauCeti

namespace FiniteBundleAtlas

open Bundle

section Atlas

variable {E : Type*} [TopologicalSpace E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {F : Type*} [TopologicalSpace F] {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] (A : FiniteBundleAtlas E M F V)

/-- The image of chart `i` lies in the chart target, and the inverse chart takes it into the
base set of bundle chart `i`. -/
theorem image_subset_target_inter_preimage_symm (i : Fin A.n) :
    (A.image i : Set E) ⊆ (A.chart i).target ∩ (A.chart i).symm ⁻¹' (A.triv i).baseSet :=
  (A.image_subset_chart_image_closure_dom i).trans (A.chart_image_closure_dom_subset i)

end Atlas

section Linear

variable {E : Type*} [TopologicalSpace E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  (A : FiniteBundleAtlas E M F V)

/-- On the image of chart `i`, the chart reading of `s - t` is the difference of the readings of
`s` and `t`. -/
theorem coord_sub (i : Fin A.n) (s t : ∀ x, V x) {y : E} (hy : y ∈ A.image i) :
    A.coord i (s - t) y = A.coord i s y - A.coord i t y := by
  rw [eq_sub_iff_add_eq, ← A.coord_add i _ _ hy, sub_add_cancel]

end Linear

section Hom

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [TopologicalSpace E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  (A : FiniteBundleAtlas E M F V)

/-- Tau Ceti's `TauCeti.FiniteBundleAtlas.coord_hom_apply` for a section `φ` of the bundle of
endomorphisms of `V`: on the image of chart `i`, the reading of `φ` applied to the reading of a
section `s` is the reading in `A` of the section `x ↦ φ x (s x)`. -/
theorem coord_hom_apply_self (i : Fin A.n) (φ : ∀ x, V x →L[𝕜] V x) (s : ∀ x, V x) {y : E}
    (hy : y ∈ A.image i) :
    (A.hom A.closure_dom_subset_baseSet).coord i φ y (A.coord i s y) =
      A.coord i (fun x ↦ φ x (s x)) y :=
  -- `A.ofBaseSet A.closure_dom_subset_baseSet` is `A` by the eta rule for structures. A rewrite
  -- cannot replace it, since the type `Fin _` of the chart index depends on the atlas.
  coord_hom_apply _ _ i φ s hy

end Hom

section Smooth

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  {k : WithTop ℕ∞} [IsManifold 𝓘(ℝ, E) k M] [ContMDiffVectorBundle k F V 𝓘(ℝ, E)]
  (A : FiniteBundleAtlas E M F V)

/-- **A section with `Cᵏ` chart readings is `Cᵏ`.** If the reading `A.coord i s` of a section `s`
is `Cᵏ` on the image of chart `i`, for every chart `i` of `A`, then `s` is a `Cᵏ` section. This is
a converse of Tau Ceti's `TauCeti.FiniteBundleAtlas.contDiffOn_coord`. -/
theorem contMDiff_of_contDiffOn_coord {s : ∀ x, V x}
    (hs : ∀ i, ContDiffOn ℝ k (A.coord i s) (A.image i)) :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F)) k fun x ↦ TotalSpace.mk' F x (s x) := by
  intro x
  obtain ⟨i, hx⟩ := A.exists_mem_dom x
  rw [(A.triv i).contMDiffAt_section_iff (A.dom_subset_baseSet i hx)]
  -- Near `x`, the reading of `s` in the bundle chart is `A.coord i s ∘ A.chart i`.
  have hchart : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) k (A.chart i) x := by
    simpa using contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := k)
      (A.dom_subset_chart_source i hx)
  have hc : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) k (A.coord i s ∘ A.chart i) x :=
    ((hs i).contDiffAt ((A.image i).isOpen.mem_nhds
      (A.mem_image.2 ⟨x, hx, rfl⟩))).comp_contMDiffAt hchart
  exact hc.congr_of_eventuallyEq <| Filter.eventually_of_mem ((A.isOpen_dom i).mem_nhds hx)
    fun y hy ↦ (A.coord_chart s hy).symm

end Smooth

end FiniteBundleAtlas

end TauCeti

end
