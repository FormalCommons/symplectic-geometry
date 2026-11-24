/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Basic

/-!
# Finite bundle atlases: chart images and chart readings

Two facts about Tau Ceti's finite bundle atlases `TauCeti.FiniteBundleAtlas`.

* `TauCeti.FiniteBundleAtlas.image_subset_target_inter_preimage_symm`: the image of chart `i` lies
  in the chart target, and the inverse chart takes it into the base set of bundle chart `i`. This
  is the open set on which the chart readings of smooth sections are smooth.
* `TauCeti.FiniteBundleAtlas.coord_sub`: on the image of a chart, the chart reading of a
  difference of sections is the difference of their readings, next to Tau Ceti's
  `TauCeti.FiniteBundleAtlas.coord_add` and `TauCeti.FiniteBundleAtlas.coord_smul`.
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

end FiniteBundleAtlas

end TauCeti

end
