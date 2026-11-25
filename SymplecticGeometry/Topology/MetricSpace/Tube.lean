/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Compactness.Compact

/-!
# The tube lemma with a metric ball

For a compact set `K` of a topological space and a point `y` of a pseudometric space, an open set
of the product that contains `K ×ˢ {y}` contains `K ×ˢ ball y ε` for some `ε > 0`; the same holds
with the factors exchanged. These are Mathlib's `generalized_tube_lemma` for `K` and the
singleton `{y}`, followed by `Metric.isOpen_iff` for the open neighbourhood of `y` it gives.

## Main results

* `IsCompact.exists_prod_ball_subset`: `K ×ˢ {y} ⊆ U` gives `K ×ˢ ball y ε ⊆ U`.
* `IsCompact.exists_ball_prod_subset`: `{x} ×ˢ K ⊆ U` gives `ball x ε ×ˢ K ⊆ U`.

## References

* J. R. Munkres, *Topology*, 2nd ed., Prentice Hall, 2000, Lemma 26.8 (the tube lemma)
-/

public section

open Set Metric

variable {X Y : Type*}

namespace IsCompact

/-- **Tube lemma with a ball on the right.** An open set of `X × Y` containing `K ×ˢ {y}`, for
a compact `K`, contains `K ×ˢ ball y ε` for some `ε > 0`. -/
theorem exists_prod_ball_subset [TopologicalSpace X] [PseudoMetricSpace Y] {K : Set X}
    (hK : IsCompact K) {y : Y} {U : Set (X × Y)} (hU : IsOpen U) (hKU : K ×ˢ {y} ⊆ U) :
    ∃ ε > 0, K ×ˢ ball y ε ⊆ U := by
  obtain ⟨u, v, -, hv, hKu, hyv, huv⟩ := generalized_tube_lemma hK isCompact_singleton hU hKU
  obtain ⟨ε, hε, hεv⟩ := Metric.isOpen_iff.1 hv y (hyv rfl)
  exact ⟨ε, hε, (prod_mono hKu hεv).trans huv⟩

/-- **Tube lemma with a ball on the left.** An open set of `X × Y` containing `{x} ×ˢ K`, for
a compact `K`, contains `ball x ε ×ˢ K` for some `ε > 0`. -/
theorem exists_ball_prod_subset [PseudoMetricSpace X] [TopologicalSpace Y] {K : Set Y}
    (hK : IsCompact K) {x : X} {U : Set (X × Y)} (hU : IsOpen U) (hKU : {x} ×ˢ K ⊆ U) :
    ∃ ε > 0, ball x ε ×ˢ K ⊆ U := by
  obtain ⟨u, v, hu, -, hxu, hKv, huv⟩ := generalized_tube_lemma isCompact_singleton hK hU hKU
  obtain ⟨ε, hε, hεu⟩ := Metric.isOpen_iff.1 hu x (hxu rfl)
  exact ⟨ε, hε, (prod_mono hεu hKv).trans huv⟩

end IsCompact

end
