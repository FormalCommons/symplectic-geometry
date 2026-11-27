/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt

/-!
# Balls of an extended chart

For a point `x` of a manifold `M` modelled by `I : ModelWithCorners 𝕜 E H` and `r : ℝ`,
`SymplecticGeometry.chartBall I x r` is the open set of points `y` in the source of
`extChartAt I x` whose chart point lies in the ball of radius `r` about the chart point of `x`.
It is a neighbourhood of `x` for `0 < r` (`chartBall_mem_nhds`). When the part of this ball in
`range I` lies in the chart target, the chart carries it onto that part
(`extChartAt_image_chartBall`), and every neighbourhood of `x` contains such a chart ball
(`exists_chartBall_subset`).

This is Tau Ceti's `OpenPartialHomeomorph.chartBall` for the extended chart, which is only a
partial equivalence onto a subset of `range I`; `extChartAt_image_chartBall` is the analogue of
Tau Ceti's `OpenPartialHomeomorph.image_chartBall`, with the ball cut down to `range I`.

## Main definitions

* `SymplecticGeometry.chartBall`: the preimage, in the source of the extended chart at `x`, of a
  ball about the chart point of `x`, as an open set of `M`.

## Main results

* `SymplecticGeometry.extChartAt_image_chartBall`: the image of a chart ball under the chart.
* `SymplecticGeometry.exists_chartBall_subset`: every neighbourhood of `x` contains a chart ball
  about `x` of positive radius whose ball, within `range I`, lies in the chart target.
-/

public section

open Set Filter
open scoped Topology

namespace SymplecticGeometry

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) [TopologicalSpace M]
  [ChartedSpace H M]

/-- The points of the chart source at `x` whose chart point lies in the ball of radius `r`
around the chart point of `x`, as an open set of `M`. -/
def chartBall (x : M) (r : ℝ) : TopologicalSpace.Opens M :=
  ⟨(extChartAt I x).source ∩ extChartAt I x ⁻¹' Metric.ball (extChartAt I x x) r,
    isOpen_extChartAt_preimage' x Metric.isOpen_ball⟩

theorem coe_chartBall (x : M) (r : ℝ) :
    (chartBall I x r : Set M) =
      (extChartAt I x).source ∩ extChartAt I x ⁻¹' Metric.ball (extChartAt I x x) r :=
  (rfl)

@[simp]
theorem mem_chartBall_iff {x y : M} {r : ℝ} :
    y ∈ chartBall I x r ↔
      y ∈ (extChartAt I x).source ∧ extChartAt I x y ∈ Metric.ball (extChartAt I x x) r :=
  (Iff.rfl)

theorem chartBall_subset_source (x : M) (r : ℝ) :
    (chartBall I x r : Set M) ⊆ (extChartAt I x).source :=
  inter_subset_left

theorem mem_chartBall_self (x : M) {r : ℝ} (hr : 0 < r) : x ∈ chartBall I x r :=
  (mem_chartBall_iff I).2 ⟨mem_extChartAt_source x, Metric.mem_ball_self hr⟩

theorem chartBall_mem_nhds (x : M) {r : ℝ} (hr : 0 < r) : (chartBall I x r : Set M) ∈ 𝓝 x :=
  (chartBall I x r).isOpen.mem_nhds (mem_chartBall_self I x hr)

/-- If the points of `range I` in the ball of radius `r` about the chart point of `x` lie in the
chart target, the chart carries `chartBall I x r` onto them. -/
theorem extChartAt_image_chartBall {x : M} {r : ℝ}
    (hr : Metric.ball (extChartAt I x x) r ∩ range I ⊆ (extChartAt I x).target) :
    extChartAt I x '' chartBall I x r = Metric.ball (extChartAt I x x) r ∩ range I := by
  rw [coe_chartBall, (PartialEquiv.IsImage.of_preimage_eq rfl).image_eq]
  exact Subset.antisymm (fun z hz ↦ ⟨hz.2, extChartAt_target_subset_range x hz.1⟩)
    fun z hz ↦ ⟨hr hz, hz.1⟩

/-- Every neighbourhood `V` of `x` contains the chart ball about `x` of some positive radius `r`
such that the points of `range I` in the ball of radius `r` about the chart point of `x` lie in
the chart target. -/
theorem exists_chartBall_subset {x : M} {V : Set M} (hV : V ∈ 𝓝 x) :
    ∃ r > 0, Metric.ball (extChartAt I x x) r ∩ range I ⊆ (extChartAt I x).target ∧
      (chartBall I x r : Set M) ⊆ V := by
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhdsWithin_iff.1 (Filter.inter_mem
    (extChartAt_target_mem_nhdsWithin (I := I) x)
    (mem_nhdsWithin_of_mem_nhds (extChartAt_preimage_mem_nhds (I := I) hV)))
  refine ⟨r, hr, fun z hz ↦ (hsub hz).1, fun y hy ↦ ?_⟩
  have h := (hsub ⟨hy.2, extChartAt_target_subset_range x ((extChartAt I x).map_source hy.1)⟩).2
  rwa [mem_preimage, (extChartAt I x).left_inv hy.1] at h

end SymplecticGeometry

end
