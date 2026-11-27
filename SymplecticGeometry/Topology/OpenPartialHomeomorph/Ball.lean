/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Continuity

/-!
# Balls in the target of an open partial homeomorphism

For an open partial homeomorphism `e : X → Y` into a pseudometric space and a point `x` of its
source, every small enough ball about `e x` lies in the target of `e`, and the inverse of `e`
carries it into any given neighbourhood of `x`
(`OpenPartialHomeomorph.exists_ball_subset_target_mapsTo_symm`). The proof combines Mathlib's
`OpenPartialHomeomorph.symm_map_nhds_eq` with `Metric.mem_nhds_iff`.
-/

public section

open Set Filter
open scoped Topology

namespace OpenPartialHomeomorph

variable {X Y : Type*} [TopologicalSpace X] [PseudoMetricSpace Y] (e : OpenPartialHomeomorph X Y)

/-- For `x` in the source of an open partial homeomorphism `e` into a pseudometric space and a
neighbourhood `T` of `x`, some ball of positive radius about `e x` lies in the target of `e` and
is carried into `T` by the inverse of `e`. -/
theorem exists_ball_subset_target_mapsTo_symm {x : X} (hx : x ∈ e.source) {T : Set X}
    (hT : T ∈ 𝓝 x) :
    ∃ ε > 0, Metric.ball (e x) ε ⊆ e.target ∧ MapsTo e.symm (Metric.ball (e x) ε) T := by
  have h : e.target ∩ e.symm ⁻¹' T ∈ 𝓝 (e x) :=
    inter_mem (e.open_target.mem_nhds (e.map_source hx))
      (by rwa [← mem_map, e.symm_map_nhds_eq hx])
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 h
  exact ⟨ε, hε, fun _ hy ↦ (hball hy).1, fun _ hy ↦ (hball hy).2⟩

end OpenPartialHomeomorph
