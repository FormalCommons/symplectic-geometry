/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Dynamics.Flow.Stable

/-!
# Stable sets of a flow that are a single point

Let `φ` be a flow of `ℝ` on a topological space and `p` a rest point of `φ`. If, near `p`, the
only point of the stable set of `p` is `p` itself, then the stable set of `p` is `{p}`
(`Flow.stableSet_eq_singleton_of_eventually`): the orbit of any point of the stable set enters
that neighbourhood, where it can only be at `p`, and flowing back from the rest point `p` gives
the point itself.

This local-to-global step is the end of the proof of Tau Ceti's
`TauCeti.IsAdaptedPseudoGradient.unstableSet_eq_singleton_of_manifoldMorseIndex_eq_zero`
(`TauCeti/Geometry/Manifold/Morse/Stable/Manifold.lean`), there written inline for unstable sets.
The proof here takes the same steps for stable sets of an arbitrary flow.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  §2.1.d.
-/

public section

open Filter Set Topology

namespace Flow

variable {α : Type*} [TopologicalSpace α]

/-- **A stable set that is locally a point is a point.** Let `p` be a rest point of a flow `φ`
of `ℝ`. If every point of the stable set of `p` close enough to `p` is `p`, then the stable set
of `p` is `{p}`. -/
theorem stableSet_eq_singleton_of_eventually {φ : Flow ℝ α} {p : α} (hfix : ∀ t, φ t p = p)
    (h : ∀ᶠ y in 𝓝 p, y ∈ stableSet φ p → y = p) :
    stableSet φ p = {p} := by
  refine Subset.antisymm (fun x hx ↦ ?_) (singleton_subset_iff.2 ?_)
  · obtain ⟨T, hT⟩ := ((mem_stableSet.1 hx).eventually h).exists
    rw [mem_singleton_iff, ← φ.map_neg_apply_map T x,
      hT ((apply_mem_stableSet_iff φ T).2 hx), hfix]
  · simpa [mem_stableSet, hfix] using tendsto_const_nhds

end Flow

end
