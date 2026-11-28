/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Connected

/-!
# Identity components of subgroups under continuous maps

A continuous map `f : G → G'` of topological groups that sends `1` to `1` and a subgroup `H` into
a subgroup `K` sends the identity component of `H` into that of `K`. This extends Tau Ceti's
`Subgroup.mapsTo_ambientConnectedComponentOfOne`, which treats a self-map of `G` and one
subgroup, to two groups and two subgroups, with the same proof.

## Main results

* `Subgroup.mapsTo_ambientConnectedComponentOfOne_of_mapsTo`: the identity component of `H` maps
  into that of `K`.
-/

public section

/-- A continuous map `f : G → G'` with `f 1 = 1` that maps a subgroup `H` of `G` into a subgroup
`K` of `G'` maps the identity component of `H` into that of `K`. -/
theorem Subgroup.mapsTo_ambientConnectedComponentOfOne_of_mapsTo {G G' : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G']
    [IsTopologicalGroup G'] {H : Subgroup G} {K : Subgroup G'} {f : G → G'} (hf : Continuous f)
    (hfH : Set.MapsTo f H K) (hf1 : f 1 = 1) :
    Set.MapsTo f H.ambientConnectedComponentOfOne K.ambientConnectedComponentOfOne := by
  rw [Subgroup.coe_ambientConnectedComponentOfOne, Subgroup.coe_ambientConnectedComponentOfOne]
  have h := (hf.continuousOn.mapsTo_connectedComponentIn H.one_mem).mono_right
    (connectedComponentIn_mono _ (Set.mapsTo_iff_image_subset.1 hfH))
  rwa [hf1] at h

end
