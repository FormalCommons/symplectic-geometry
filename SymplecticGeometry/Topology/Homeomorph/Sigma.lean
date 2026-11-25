/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# A set covered by disjoint open subsets is their disjoint union

If pairwise disjoint open subsets `s i` of a space lie in a set `t` and cover it, then the map
`Σ i, s i → t` that includes each `s i` into `t` is a homeomorphism
(`Set.isHomeomorph_sigma_inclusion`). For `t = ⋃ i, s i` this is the inverse of Mathlib's
`Homeomorph.Set.iUnion`, from which it is derived; the version with a general `t` applies where
`t` is not syntactically a union, such as the preimage of a union.

## Main results

* `Set.isHomeomorph_sigma_inclusion`: a set covered by pairwise disjoint open subsets is
  homeomorphic to their disjoint union.
-/

public section

open Set Function

/-- A subset `t` of a space that is the union of pairwise disjoint open subsets `s i ⊆ t` is
homeomorphic to their disjoint union, by the map that includes each `s i` into `t`. For
`t = ⋃ i, s i` this is the inverse of Mathlib's `Homeomorph.Set.iUnion`. -/
theorem Set.isHomeomorph_sigma_inclusion {X : Type*} [TopologicalSpace X] {ι : Type*}
    {s : ι → Set X} {t : Set X} (hs : ∀ i, IsOpen (s i)) (hd : Pairwise (Disjoint on s))
    (hst : ∀ i, s i ⊆ t) (ht : t ⊆ ⋃ i, s i) :
    IsHomeomorph fun x : Σ i, s i ↦ inclusion (hst x.1) x.2 :=
  ((Homeomorph.Set.iUnion fun i ↦ ⟨s i, (hs i).mem_nhdsSet.2 subset_rfl,
    fun _ hj ↦ hd hj.symm⟩).symm.trans
    (Homeomorph.setCongr (ht.antisymm (iUnion_subset hst))).symm).isHomeomorph

end
