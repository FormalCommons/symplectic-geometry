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

* `IsSimplyConnected.preimage_coe`: a simply connected set contained in `U` is simply connected
  as a subset of `U`.
* `IsSimplyConnected.union_of_isOpen`: the union of two open simply connected sets with path
  connected intersection is simply connected.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Cambridge University Press, 2002, Theorem 1.20.
-/

public section

open Set Topology

variable {X : Type*} [TopologicalSpace X] {A B : Set X}

/-- A simply connected set `W` contained in `U` is simply connected as a subset of `U`: its
preimage under the inclusion `U → X` is simply connected. -/
theorem IsSimplyConnected.preimage_coe {U W : Set X} (hW : IsSimplyConnected W) (hWU : W ⊆ U) :
    IsSimplyConnected (((↑) : U → X) ⁻¹' W) := by
  rwa [← IsEmbedding.subtypeVal.isSimplyConnected_image, Subtype.image_preimage_val,
    inter_eq_right.2 hWU]

/-- **Van Kampen for simply connected sets.** The union of two open simply connected sets whose
intersection is path connected is simply connected. -/
theorem IsSimplyConnected.union_of_isOpen (hA : IsSimplyConnected A) (hB : IsSimplyConnected B)
    (hAo : IsOpen A) (hBo : IsOpen B) (hAB : IsPathConnected (A ∩ B)) :
    IsSimplyConnected (A ∪ B) := by
  have := (hA.preimage_coe (subset_union_left (t := B))).simplyConnectedSpace
  have := (hB.preimage_coe (subset_union_right (s := A))).simplyConnectedSpace
  refine TauCeti.simplyConnectedSpace_of_interior_union (A := Subtype.val ⁻¹' A)
    (B := Subtype.val ⁻¹' B) ?_ ?_
  · rw [(hAo.preimage continuous_subtypeVal).interior_eq,
      (hBo.preimage continuous_subtypeVal).interior_eq, ← preimage_union]
    exact preimage_eq_univ_iff.2 Subtype.range_coe.subset
  · rw [← preimage_inter]
    exact hAB.preimage_coe (inter_subset_left.trans subset_union_left)

end
