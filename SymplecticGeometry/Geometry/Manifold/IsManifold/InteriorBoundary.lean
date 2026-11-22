/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.Analysis.Convex.Topology
public import SymplecticGeometry.Topology.Connected.Clopen
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# The interior of a manifold with boundary

For a `C¹` manifold `M` with boundary or corners, modelled by `I`, Mathlib shows that the
interior `I.interior M` is open. This file shows that it is dense, makes it an open submanifold
`I.interiorOpens M` without boundary, and shows that it is connected when `M` is.

Connectedness is checked in charts: near any point `x` of `M`, the interior points of a small
chart neighbourhood of `x` correspond to the intersection of a ball with the interior of the
range of `I`, which is convex since the range is. No hypothesis on the dimension is needed: in
dimension zero, every point is an interior point.

It also extends two facts about charts of the atlas to the maximal atlas: Mathlib's
`ModelWithCorners.isInteriorPoint_iff_of_mem_atlas`, through Mathlib's
`IsLocalDiffeomorphAt.isInteriorPoint_iff`, and Tau Ceti's
`OpenPartialHomeomorph.isOpen_extend_target_of_mem_atlas`, whose proof is followed.

## Main definitions and results

* `ModelWithCorners.isInteriorPoint_extChartAt_symm_iff`: a point of a chart target is the image
  of an interior point if and only if it lies in the interior of the range of `I`.
* `ModelWithCorners.isInteriorPoint_iff_of_mem_maximalAtlas`: the interior points in the source of
  a chart of the maximal atlas are those it sends into the interior of its target. So in a
  boundaryless manifold such charts have open targets
  (`OpenPartialHomeomorph.isOpen_extend_target_of_mem_maximalAtlas`).
* `ModelWithCorners.dense_interior`: the interior of `M` is dense.
* `ModelWithCorners.interiorOpens`: the interior of `M` as an open subset.
* `ModelWithCorners.BoundarylessManifold.interior`: the interior of `M` is a manifold without
  boundary.
* `ModelWithCorners.isConnected_interior`: the interior of a connected manifold is connected.

## References

These facts are standard. The library uses them to reduce questions about bundles over a
surface with boundary, as in §2.6 of the reference below, to its interior.

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017]
-/

public section

open Set Topology TopologicalSpace Filter

namespace ModelWithCorners

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M]
  [ChartedSpace H M] {n : WithTop ℕ∞}

/-- In a `C¹` manifold, a point `z` of the target of the extended chart at `x` is the image of an
interior point if and only if `z` lies in the interior of the range of the model. -/
theorem isInteriorPoint_extChartAt_symm_iff [IsManifold I n M] (hn : n ≠ 0) {x : M} {z : E}
    (hz : z ∈ (extChartAt I x).target) :
    I.IsInteriorPoint ((extChartAt I x).symm z) ↔ z ∈ interior (range I) := by
  have hy : (extChartAt I x).symm z ∈ (chartAt H x).source := by
    simpa using (extChartAt I x).map_target hz
  rw [I.isInteriorPoint_iff_of_mem_atlas hn (chart_mem_atlas H x) hy, ← extChartAt,
    (extChartAt I x).right_inv hz]
  refine ⟨fun h ↦ (chartAt H x).interior_extend_target_subset_interior_range h, fun h ↦ ?_⟩
  obtain ⟨w, hw, rfl⟩ : z ∈ I '' (chartAt H x).target := by
    rwa [← (chartAt H x).extend_target', ← extChartAt]
  exact (chartAt H x).mem_interior_extend_target hw h

/-- In a `C¹` manifold, a point `x` in the source of a chart `e` of the maximal atlas is an interior
point if and only if the extended chart sends it into the interior of its target. This is
Mathlib's `ModelWithCorners.isInteriorPoint_iff_of_mem_atlas` for the maximal atlas. -/
theorem isInteriorPoint_iff_of_mem_maximalAtlas [IsManifold I n M] (hn : n ≠ 0)
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I n M) {x : M}
    (hx : x ∈ e.source) :
    I.IsInteriorPoint x ↔ e.extend I x ∈ interior (e.extend I).target := by
  rw [(e.isLocalDiffeomorphAt_of_mem_maximalAtlas he hx).isInteriorPoint_iff hn,
    isInteriorPoint_iff]
  simp only [extChartAt, chartAt_self_eq, OpenPartialHomeomorph.extend_coe, Function.comp_apply,
    OpenPartialHomeomorph.extend_target, OpenPartialHomeomorph.refl_target, preimage_univ,
    univ_inter, OpenPartialHomeomorph.refl_apply, id]
  rw [← OpenPartialHomeomorph.extend_target]
  exact ⟨e.mem_interior_extend_target (e.map_source hx),
    fun h ↦ e.interior_extend_target_subset_interior_range h⟩

/-- In a boundaryless `C¹` manifold, every chart of the maximal atlas has an open extended target.
This is Tau Ceti's `OpenPartialHomeomorph.isOpen_extend_target_of_mem_atlas` for the maximal
atlas. -/
theorem _root_.OpenPartialHomeomorph.isOpen_extend_target_of_mem_maximalAtlas [IsManifold I n M]
    [BoundarylessManifold I M] (hn : n ≠ 0) {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I n M) : IsOpen (e.extend I).target := by
  refine isOpen_iff_mem_nhds.2 fun y hy ↦ ?_
  have hx : (e.extend I).symm y ∈ e.source := by
    simpa only [OpenPartialHomeomorph.extend_source] using (e.extend I).map_target hy
  have h := (I.isInteriorPoint_iff_of_mem_maximalAtlas hn he hx).1
    BoundarylessManifold.isInteriorPoint
  rw [(e.extend I).right_inv hy] at h
  exact mem_interior_iff_mem_nhds.1 h

/-- The interior of a `C¹` manifold is dense. -/
theorem dense_interior [IsManifold I n M] (hn : n ≠ 0) : Dense (I.interior M) := by
  intro x
  rw [mem_closure_iff_nhds]
  intro t ht
  set e := extChartAt I x
  have hS : e.symm ⁻¹' t ∩ e.target ∈ 𝓝[interior (range I)] e x :=
    nhdsWithin_mono _ interior_subset <| inter_mem
      (by rwa [← map_extChartAt_symm_nhdsWithin_range (I := I) x] at ht)
      (extChartAt_target_mem_nhdsWithin x)
  have hx : e x ∈ closure (interior (range I)) :=
    I.range_subset_closure_interior (extChartAt_target_subset_range x (mem_extChartAt_target x))
  obtain ⟨w, ⟨hwt, hwT⟩, hwi⟩ :=
    (mem_closure_iff_nhdsWithin_neBot.1 hx).nonempty_of_mem (inter_mem hS self_mem_nhdsWithin)
  exact ⟨e.symm w, hwt, (I.isInteriorPoint_extChartAt_symm_iff hn hwT).2 hwi⟩

/-- Near every point `x` of a `C¹` manifold, the interior points of a small neighbourhood of `x`
form a preconnected set. This is the local input to `isPreconnected_interior`. -/
theorem exists_mem_nhds_isPreconnected_inter_interior [NormedSpace ℝ E] [IsManifold I n M]
    (hn : n ≠ 0) (x : M) : ∃ t ∈ 𝓝 x, IsPreconnected (t ∩ I.interior M) := by
  set e := extChartAt I x
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhdsWithin_iff.mp (extChartAt_target_mem_nhdsWithin (I := I) x)
  set C := Metric.ball (e x) ε ∩ interior (range I)
  have hCT : C ⊆ e.target := fun w hw ↦ hsub ⟨hw.1, interior_subset hw.2⟩
  refine ⟨e.source ∩ e ⁻¹' Metric.ball (e x) ε, inter_mem (extChartAt_source_mem_nhds x)
    ((continuousAt_extChartAt x).preimage_mem_nhds (Metric.ball_mem_nhds _ hε)), ?_⟩
  have heq : e.source ∩ e ⁻¹' Metric.ball (e x) ε ∩ I.interior M = e.symm '' C := by
    ext y
    constructor
    · rintro ⟨⟨hys, hyb⟩, hyi⟩
      refine ⟨e y, ⟨hyb, ?_⟩, e.left_inv hys⟩
      rw [← I.isInteriorPoint_extChartAt_symm_iff hn (e.map_source hys), e.left_inv hys]
      exact hyi
    · rintro ⟨w, hw, rfl⟩
      refine ⟨⟨e.map_target (hCT hw), ?_⟩,
        (I.isInteriorPoint_extChartAt_symm_iff hn (hCT hw)).2 hw.2⟩
      simpa [mem_preimage, e.right_inv (hCT hw)] using hw.1
  rw [heq]
  exact ((convex_ball _ _).inter I.convex_range.interior).isPreconnected.image _
    ((continuousOn_extChartAt_symm x).mono hCT)

/-- The interior of a preconnected `C¹` manifold is preconnected. -/
theorem isPreconnected_interior [IsManifold I n M] [PreconnectedSpace M] (hn : n ≠ 0) :
    IsPreconnected (I.interior M) := by
  by_cases h : IsRCLikeNormedField 𝕜
  · let := h.rclike 𝕜
    let := NormedSpace.restrictScalars ℝ 𝕜 E
    exact (I.dense_interior hn).isPreconnected_of_forall_exists_mem_nhds
      (I.exists_mem_nhds_isPreconnected_inter_interior hn)
  · -- Over a field that is not `RCLike`, the model has full range, so every point is interior.
    have : I.Boundaryless := ⟨I.range_eq_univ_of_not_isRCLikeNormedField h⟩
    rw [I.interior_eq_univ]
    exact isPreconnected_univ

/-- The interior of a connected `C¹` manifold is connected. -/
theorem isConnected_interior [IsManifold I n M] [ConnectedSpace M]
    (hn : n ≠ 0) : IsConnected (I.interior M) :=
  ⟨(I.dense_interior hn).nonempty, I.isPreconnected_interior hn⟩

variable (I M) in
/-- The interior of a `C¹` manifold, as an open subset. As an open subset of `M`, it is a manifold
without boundary (`ModelWithCorners.BoundarylessManifold.interior`). -/
def interiorOpens [IsManifold I 1 M] : Opens M :=
  ⟨I.interior M, I.isOpen_interior one_ne_zero⟩

@[simp]
theorem coe_interiorOpens [IsManifold I 1 M] : (I.interiorOpens M : Set M) = I.interior M :=
  (rfl)

@[simp]
theorem mem_interiorOpens [IsManifold I 1 M] {x : M} :
    x ∈ I.interiorOpens M ↔ I.IsInteriorPoint x :=
  (Iff.rfl)

/-- The interior of a `C¹` manifold, as an open submanifold, has no boundary. -/
instance BoundarylessManifold.interior [IsManifold I 1 M] :
    BoundarylessManifold I (I.interiorOpens M) :=
  ⟨fun x ↦ I.isInteriorPoint_iff_isInteriorPoint_val.2 x.property⟩

/-- The interior of a connected `C¹` manifold, as an open submanifold, is connected. -/
instance connectedSpace_interiorOpens [IsManifold I 1 M] [ConnectedSpace M] :
    ConnectedSpace (I.interiorOpens M) :=
  isConnected_iff_connectedSpace.1 (I.isConnected_interior one_ne_zero)

end ModelWithCorners

end
