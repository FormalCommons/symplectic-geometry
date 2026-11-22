/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Order.SupClosed
public import Mathlib.Topology.Sets.Opens

/-!
# Open sets inside a chart

For a charted space `M` modelled on `H`, the open sets of `M` contained in the source of some
chart are closed under intersection
(`TopologicalSpace.Opens.infClosed_setOf_subset_chartAt_source`), and they cover `M`
(`TopologicalSpace.Opens.sSup_setOf_subset_chartAt_source_eq_top`).
Each of them embeds openly into the model through its chart (Tau Ceti's
`OpenPartialHomeomorph.isOpenEmbedding_comp`). Over this family, a Mayer–Vietoris induction
carries a statement about open subsets of the model to the whole manifold, as in the proof of
Poincaré duality.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3, the proof of
  Theorem 3.35.
-/

public section

open Set

namespace TopologicalSpace.Opens

variable (H : Type*) {M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]

/-- The open sets of a charted space that lie in the source of some chart are closed under
intersection. -/
theorem infClosed_setOf_subset_chartAt_source :
    InfClosed {W : Opens M | ∃ x, (W : Set M) ⊆ (chartAt H x).source} := by
  rintro V ⟨x, hx⟩ W -
  exact ⟨x, inter_subset_left.trans hx⟩

/-- The open sets of a charted space that lie in the source of some chart cover the space. -/
theorem sSup_setOf_subset_chartAt_source_eq_top :
    sSup {W : Opens M | ∃ x, (W : Set M) ⊆ (chartAt H x).source} = ⊤ :=
  eq_top_iff.2 fun x _ ↦ Opens.mem_sSup.2
    ⟨⟨(chartAt H x).source, (chartAt H x).open_source⟩, ⟨x, subset_rfl⟩, mem_chart_source H x⟩

end TopologicalSpace.Opens
