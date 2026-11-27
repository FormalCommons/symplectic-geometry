/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.Dimension.Covering
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The covering dimension of a finite union of closed sets

If finitely many closed sets `K i` of a topological space each have covering dimension at most
`n`, as subspaces, then so does their union. This is Tau Ceti's sum theorem
`TauCeti.hasCoveringDimensionLE_of_iUnion_eq_univ`, applied in the subspace `⋃ i, K i`, whose
closed pieces `K i` it sees through the homeomorphisms between the preimages of `K i` in the
union and `K i` itself (Mathlib's `Topology.IsEmbedding.homeomorphOfSubsetRange`).

## Main declarations

* `TauCeti.hasCoveringDimensionLE_iUnion`: the finite union of closed sets.

## References

* J. R. Munkres, *Topology*, 2nd ed., Prentice Hall, 2000, Theorem 50.2
-/

public section

open Set Topology

namespace TauCeti

variable {X : Type*} [TopologicalSpace X]

/-- If each of finitely many closed sets `K i` has covering dimension at most `n`, then so has
their union. -/
theorem hasCoveringDimensionLE_iUnion {ι : Type*} [Finite ι] {K : ι → Set X}
    (hK : ∀ i, IsClosed (K i)) {n : ℕ} (h : ∀ i, HasCoveringDimensionLE (K i) n) :
    HasCoveringDimensionLE (⋃ i, K i : Set X) n := by
  refine hasCoveringDimensionLE_of_iUnion_eq_univ
    (F := fun i => ((↑) : (⋃ i, K i : Set X) → X) ⁻¹' K i)
    (fun i => (hK i).preimage continuous_subtypeVal)
    (by rw [← preimage_iUnion, Subtype.coe_preimage_self]) fun i => ?_
  -- The preimage of `K i` in the union is homeomorphic to `K i`.
  exact (IsEmbedding.subtypeVal.homeomorphOfSubsetRange (by
    rw [Subtype.range_coe]; exact subset_iUnion K i)).isHomeomorph.hasCoveringDimensionLE_iff.2
    (h i)

end TauCeti

end
