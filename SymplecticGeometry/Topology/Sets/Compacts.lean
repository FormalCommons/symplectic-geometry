/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Sets.Compacts

/-!
# Compact preimages under inducing maps

For an inducing map `f : α → β` and a compact set `S ⊆ β` contained in the range of `f`, the
preimage `f ⁻¹' S` is compact (`Topology.IsInducing.isCompact_preimage'`). This file packages it
as an element of `TopologicalSpace.Compacts α` (`Topology.IsInducing.preimageCompacts`), whose
image under `f` contains `S` again (`Topology.IsInducing.subset_map_preimageCompacts`).

These declarations are from Tau Ceti's main branch (`TauCeti/Topology/Sets/Compacts.lean`, same
names), as of the commit `e48a7f81a81426270765022681d165be592a3231`, not yet in the pinned
release; they are stated here under their Tau Ceti names, so that moving Tau Ceti past them
deletes this file without renames.
-/

public section

namespace Topology.IsInducing

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {f : α → β}

/-- The compact preimage of a compact set contained in the range of an inducing map.
Its carrier is definitionally the preimage, as for `Compacts.compactNhdsOfSubsetInterior`. -/
@[expose, simps] def preimageCompacts (hf : IsInducing f) {S : Set β} (hS : IsCompact S)
    (hSf : S ⊆ Set.range f) : TopologicalSpace.Compacts α :=
  ⟨f ⁻¹' S, hf.isCompact_preimage' hS hSf⟩

/-- A compact set in the range of an inducing map lies in the image of its compact preimage. -/
lemma subset_map_preimageCompacts (hf : IsInducing f) {S : Set β} (hS : IsCompact S)
    (hSf : S ⊆ Set.range f) :
    S ⊆ ((hf.preimageCompacts hS hSf).map f hf.continuous : Set β) :=
  (Set.image_preimage_eq_of_subset hSf).ge

end Topology.IsInducing

end
