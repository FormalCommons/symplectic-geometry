/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Charts

/-!
# Boundary points in the extended charts of the half-space model

For a manifold `W` modelled on the half-space `𝓡∂ (n + 1)`, the extended chart at any point
reads a point of its target as a boundary point of `W` exactly when its zeroth coordinate
vanishes. This complements Tau Ceti's `TauCeti.ModelWithCorners.mem_boundary_euclideanHalfSpace_iff`
(in `TauCeti/Geometry/Manifold/Boundary/Charts.lean`), stated there for points of a chart source.

## Main results

* `TauCeti.extChartAt_symm_mem_boundary_iff`: a point of the target is read as a boundary point
  exactly when its zeroth coordinate vanishes.
* `TauCeti.extChartAt_symm_mem_interior`: a point of the target with positive zeroth coordinate is
  read as an interior point.
* `TauCeti.extChartAt_self_apply_zero`: the extended chart at a boundary point sends it to the
  hyperplane where the zeroth coordinate vanishes.
-/

public section

open Set Function
open scoped Manifold

namespace TauCeti

variable {n : ℕ} {W : Type*} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]

/-- The extended chart of a manifold modelled on the half-space reads a point of its target as a
boundary point exactly when its zeroth coordinate vanishes. -/
theorem extChartAt_symm_mem_boundary_iff {q : W} {z : EuclideanSpace ℝ (Fin (n + 1))}
    (hz : z ∈ (extChartAt (𝓡∂ (n + 1)) q).target) :
    (extChartAt (𝓡∂ (n + 1)) q).symm z ∈ (𝓡∂ (n + 1)).boundary W ↔ z 0 = 0 := by
  have hs := (extChartAt (𝓡∂ (n + 1)) q).map_target hz
  rw [extChartAt_source] at hs
  rw [ModelWithCorners.mem_boundary_euclideanHalfSpace_iff hs]
  have h := (extChartAt (𝓡∂ (n + 1)) q).right_inv hz
  rw [extChartAt_coe, comp_apply, modelWithCornersEuclideanHalfSpace_apply] at h
  rw [h]

/-- A point of the target of an extended chart whose zeroth coordinate is positive is read by the
inverse chart as an interior point. -/
theorem extChartAt_symm_mem_interior {q : W} {z : EuclideanSpace ℝ (Fin (n + 1))}
    (hz : z ∈ (extChartAt (𝓡∂ (n + 1)) q).target) (hz0 : 0 < z 0) :
    (extChartAt (𝓡∂ (n + 1)) q).symm z ∈ (𝓡∂ (n + 1)).interior W := by
  rw [← ModelWithCorners.compl_boundary, mem_compl_iff, extChartAt_symm_mem_boundary_iff hz]
  exact hz0.ne'

/-- The extended chart at a boundary point sends it to the boundary hyperplane. -/
theorem extChartAt_self_apply_zero {q : W} (hq : q ∈ (𝓡∂ (n + 1)).boundary W) :
    extChartAt (𝓡∂ (n + 1)) q q 0 = 0 := by
  have h := (extChartAt_symm_mem_boundary_iff (W := W) (n := n)
    (mem_extChartAt_target (I := 𝓡∂ (n + 1)) q)).1
  rw [extChartAt_to_inv] at h
  exact h hq

end TauCeti

end
