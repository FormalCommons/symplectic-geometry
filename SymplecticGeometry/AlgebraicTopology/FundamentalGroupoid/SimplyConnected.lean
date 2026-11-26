/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

import TauCeti.AlgebraicTopology.FundamentalGroup.VanKampen.Basic

/-!
# Unions of simply connected sets

The union of two open simply connected sets of a topological space whose intersection is path
connected is simply connected. This is the form for subsets of a space of Tau Ceti's two-set
criterion `TauCeti.simplyConnectedSpace_of_interior_union`, applied inside the union, where the
two sets are open and so cover it by their interiors.

## Main results

* `IsSimplyConnected.union_of_isOpen`: the union of two open simply connected sets with path
  connected intersection is simply connected.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Cambridge University Press, 2002, Theorem 1.20.
-/

public section

open Set Topology

variable {X : Type*} [TopologicalSpace X] {A B : Set X}

/-- **Van Kampen for simply connected sets.** The union of two open simply connected sets whose
intersection is path connected is simply connected. -/
theorem IsSimplyConnected.union_of_isOpen (hA : IsSimplyConnected A) (hB : IsSimplyConnected B)
    (hAo : IsOpen A) (hBo : IsOpen B) (hAB : IsPathConnected (A ∩ B)) :
    IsSimplyConnected (A ∪ B) := by
  -- Inside `A ∪ B`, the preimages of `A` and `B` are homeomorphic to `A` and `B`.
  have hsub {s : Set X} (hs : s ⊆ A ∪ B) (h : IsSimplyConnected s) :
      SimplyConnectedSpace (Subtype.val ⁻¹' s : Set ↥(A ∪ B)) :=
    (IsEmbedding.subtypeVal.isSimplyConnected_image.1 (by
      rwa [Subtype.image_preimage_coe, inter_eq_right.2 hs])).simplyConnectedSpace
  have := hsub subset_union_left hA
  have := hsub subset_union_right hB
  unfold IsSimplyConnected
  refine TauCeti.simplyConnectedSpace_of_interior_union (A := Subtype.val ⁻¹' A)
    (B := Subtype.val ⁻¹' B) ?_ ?_
  · rw [(hAo.preimage continuous_subtypeVal).interior_eq,
      (hBo.preimage continuous_subtypeVal).interior_eq, ← preimage_union]
    exact preimage_eq_univ_iff.2 Subtype.range_coe.subset
  · rw [← preimage_inter, IsInducing.subtypeVal.isPathConnected_iff, Subtype.image_preimage_coe,
      inter_eq_right.2 (inter_subset_left.trans subset_union_left)]
    exact hAB

end
