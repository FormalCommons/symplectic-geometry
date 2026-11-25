/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Continuity
import Mathlib.Order.Filter.Bases.Finite
import Mathlib.Topology.Separation.Hausdorff

/-!
# Disjoint balls about finitely many chart centres

Let `Φ i`, for `i` in a finite type, be open partial homeomorphisms from pseudo-metric spaces
`E i` to a Hausdorff space `M`, and let `p i` lie in the source of `Φ i`, with distinct images
`Φ i (p i)`. Then there are radii `c i > 0` such that each ball `ball (p i) (c i)` lies in the
source of `Φ i` and the images `Φ i '' ball (p i) (c i)` are pairwise disjoint
(`OpenPartialHomeomorph.exists_pairwise_disjoint_image_ball`).

The neighbourhood filters of the distinct points `Φ i (p i)` are pairwise disjoint, and so are
the images under `Φ i` of the neighbourhood filters of the `p i`, which are finer since each
`Φ i` is continuous at `p i`. Mathlib's `Pairwise.exists_mem_filter_basis_of_disjoint` then
chooses pairwise disjoint members of the bases of these filters given by the balls about the
`p i` inside the sources.
-/

public section

open Set Metric Filter Topology

namespace OpenPartialHomeomorph

/-- For finitely many open partial homeomorphisms `Φ i` from pseudo-metric spaces to a Hausdorff
space, and points `p i` of their sources with pairwise distinct images `Φ i (p i)`, there are
radii `c i > 0` such that each ball `ball (p i) (c i)` lies in the source of `Φ i` and the images
`Φ i '' ball (p i) (c i)` are pairwise disjoint. -/
theorem exists_pairwise_disjoint_image_ball {ι : Type*} [Finite ι] {E : ι → Type*}
    [∀ i, PseudoMetricSpace (E i)] {M : Type*} [TopologicalSpace M] [T2Space M]
    (Φ : ∀ i, OpenPartialHomeomorph (E i) M) {p : ∀ i, E i} (hp : ∀ i, p i ∈ (Φ i).source)
    (hinj : Function.Injective fun i ↦ Φ i (p i)) :
    ∃ c : ι → ℝ, (∀ i, 0 < c i) ∧ (∀ i, ball (p i) (c i) ⊆ (Φ i).source) ∧
      Pairwise fun i j ↦ Disjoint (Φ i '' ball (p i) (c i)) (Φ j '' ball (p j) (c j)) := by
  have hd : Pairwise (Function.onFun Disjoint fun i ↦ map (Φ i) (𝓝 (p i))) :=
    fun i j hij ↦ (disjoint_nhds_nhds.2 (hinj.ne hij)).mono ((Φ i).continuousAt (hp i))
      ((Φ j).continuousAt (hp j))
  obtain ⟨c, hc, hcd⟩ := hd.exists_mem_filter_basis_of_disjoint fun i ↦
    (nhds_basis_ball.restrict_subset ((Φ i).open_source.mem_nhds (hp i))).map _
  exact ⟨c, fun i ↦ (hc i).1, fun i ↦ (hc i).2, hcd⟩

end OpenPartialHomeomorph

end
