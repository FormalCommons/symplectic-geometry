/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.OpenPartialHomeomorph.Basic

/-!
# Fibres of the restriction of an open partial homeomorphism to its source

Tau Ceti's `OpenPartialHomeomorph.sourceRestrict` is the restriction of an open partial
homeomorphism `e : X → Y` to its source, as a continuous map `e.source → Y`. Since `e` is
injective on its source, the fibre of this map over `e a`, for `a ∈ e.source`, is the single point
`⟨a, ha⟩` of the subtype (`OpenPartialHomeomorph.sourceRestrict_preimage_singleton`). Tau Ceti's
`OpenPartialHomeomorph.sourceRestrict_preimage` gives the same inclusion read in `X`, through the
inclusion of the source.

The file also records how a point of the source is located by its image: if `e a = y` with
`a ∈ e.source`, and `e.symm` maps a set `S ∋ y` into `T`, then `a ∈ T`
(`OpenPartialHomeomorph.mem_of_mapsTo_symm`).
-/

public section

namespace OpenPartialHomeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : OpenPartialHomeomorph X Y)

/-- For `a` in the source of `e`, the restriction of `e` to its source takes the value `e a` at
the point `⟨a, ha⟩` only. -/
theorem sourceRestrict_preimage_singleton {a : X} (ha : a ∈ e.source) :
    e.sourceRestrict ⁻¹' {e a} = {(⟨a, ha⟩ : e.source)} :=
  Set.Subset.antisymm (fun _ hx ↦ Subtype.ext (e.sourceRestrict_preimage ha hx))
    (Set.singleton_subset_iff.2 (Set.mem_singleton_iff.2 (e.sourceRestrict_apply _)))

/-- If `e` sends a point `a` of its source to `y`, and `e.symm` maps a set `S` containing `y` into
`T`, then `a ∈ T`. -/
theorem mem_of_mapsTo_symm {a : X} (ha : a ∈ e.source) {y : Y} (hy : e a = y) {S : Set Y}
    {T : Set X} (hST : Set.MapsTo e.symm S T) (hyS : y ∈ S) : a ∈ T := by
  rw [← e.left_inv ha, hy]
  exact hST hyS

end OpenPartialHomeomorph

end
