/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.LocallyFinite

/-!
# Locally finite families of disjoint closed sets

A locally finite family of pairwise disjoint closed sets is discrete: every point has a
neighbourhood that meets at most one member of the family.

## Main results

* `LocallyFinite.exists_mem_nhds_subsingleton`: each point of the space has a neighbourhood
  meeting at most one member of a locally finite family of pairwise disjoint closed sets.

## References

* R. Engelking, *General Topology*, Section 5.1 (discrete families of sets)
-/

public section

open Set Function Topology

variable {ι X : Type*} [TopologicalSpace X]

/-- If `R` is a locally finite family of pairwise disjoint closed sets, then every point `x` has a
neighbourhood `U` that meets `R i` for at most one index `i`. -/
theorem LocallyFinite.exists_mem_nhds_subsingleton {R : ι → Set X} (hlf : LocallyFinite R)
    (hR : ∀ i, IsClosed (R i)) (hdisj : Pairwise (Disjoint on R)) (x : X) :
    ∃ U ∈ 𝓝 x, {i | (U ∩ R i).Nonempty}.Subsingleton := by
  obtain ⟨U, hU, hUs⟩ := (hlf.eventually_subset hR x).exists_mem
  refine ⟨U, hU, fun i ⟨y, hyU, hyi⟩ j ⟨z, hzU, hzj⟩ ↦ ?_⟩
  by_contra hij
  exact (hdisj hij).notMem_of_mem_left (hUs y hyU hyi) (hUs z hzU hzj)

end
