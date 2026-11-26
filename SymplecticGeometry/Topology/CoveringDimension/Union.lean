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
`TauCeti.hasCoveringDimensionLE_of_iUnion_eq_univ`, applied in the subspace `⋃ i ∈ s, K i`,
whose closed pieces `K i` it sees through the homeomorphisms between the preimages of `K i` in
the union and `K i` itself.

## Main declarations

* `TauCeti.hasCoveringDimensionLE_biUnion`: the finite union of closed sets.

## References

* J. R. Munkres, *Topology*, 2nd ed., Prentice Hall, 2000, Theorem 50.2
-/

public section

open Set Topology

namespace TauCeti

variable {X : Type*} [TopologicalSpace X]

/-- If each closed set `K i`, for `i` in a finite set `s`, has covering dimension at most `n`,
then so has their union. -/
theorem hasCoveringDimensionLE_biUnion {ι : Type*} {s : Finset ι} {K : ι → Set X}
    (hK : ∀ i ∈ s, IsClosed (K i)) {n : ℕ} (h : ∀ i ∈ s, HasCoveringDimensionLE (K i) n) :
    HasCoveringDimensionLE (⋃ i ∈ s, K i : Set X) n := by
  set Y := ⋃ i ∈ s, K i
  refine hasCoveringDimensionLE_of_iUnion_eq_univ (ι := s)
    (F := fun i => ((↑) : Y → X) ⁻¹' K i)
    (fun i => (hK i i.property).preimage continuous_subtypeVal)
    (eq_univ_of_forall fun y => ?_) fun i => ?_
  · obtain ⟨i, hi, hy⟩ := mem_iUnion₂.1 y.property
    exact mem_iUnion.2 ⟨⟨i, hi⟩, hy⟩
  · -- The preimage of `K i` in `Y` is homeomorphic to `K i`.
    have hf : IsHomeomorph (codRestrict (fun y : ((↑) : Y → X) ⁻¹' K i => (y : Y).val) (K i)
        fun y => y.property) := by
      rw [isHomeomorph_iff_isEmbedding_surjective]
      exact ⟨(IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal).codRestrict _ _,
        fun x => ⟨⟨⟨x, mem_iUnion₂.2 ⟨i, i.property, x.property⟩⟩, x.property⟩, rfl⟩⟩
    exact hf.hasCoveringDimensionLE_iff.2 (h i i.property)

end TauCeti

end
