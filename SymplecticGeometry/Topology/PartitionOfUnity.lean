/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.PartitionOfUnity

/-!
# Partitions of unity near a compact set

Only finitely many functions of a partition of unity are nonzero somewhere on a compact set, since
the family of their supports is locally finite.

## Main results

* `PartitionOfUnity.exists_finset_finsupport_subset_of_isCompact`: one finite set of indices
  contains the pointwise supports `ρ.finsupport y` at all points `y` of a compact set.
-/

public section

open Set

namespace PartitionOfUnity

variable {ι X : Type*} [TopologicalSpace X] {s : Set X}

/-- On a compact set `K`, the indices `i` with `ρ i y ≠ 0` for some `y ∈ K` form a finite set:
there is a finite set `t` containing `ρ.finsupport y` for every `y ∈ K`. -/
theorem exists_finset_finsupport_subset_of_isCompact (ρ : PartitionOfUnity ι X s) {K : Set X}
    (hK : IsCompact K) : ∃ t : Finset ι, ∀ y ∈ K, ρ.finsupport y ⊆ t := by
  have hfin := ρ.locallyFinite.finite_nonempty_inter_compact hK
  exact ⟨hfin.toFinset, fun y hy i hi ↦ hfin.mem_toFinset.2 ⟨y, (ρ.mem_finsupport y).1 hi, hy⟩⟩

end PartitionOfUnity

end
