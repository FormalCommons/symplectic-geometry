/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.FiberBundle.Proper

/-!
# Compactness of the total space of a fibre bundle

A fibre bundle whose model fibre and base are compact has a compact total space: its projection
is proper by Tau Ceti's `FiberBundle.isProperMap_proj`, and the preimage of the compact base
under a proper map is compact.

## Main results

* `FiberBundle.compactSpace_totalSpace`: the total space of a fibre bundle with compact fibre
  over a compact base is compact.

## References

* D. Husemoller, *Fibre Bundles*, 3rd ed., Graduate Texts in Mathematics 20, Springer, 1994,
  Chapter 4 (general fibre bundles).
-/

public section

open Bundle

namespace FiberBundle

variable {B F : Type*} {E : B → Type*} [TopologicalSpace B] [TopologicalSpace F]
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]

/-- The total space of a fibre bundle with compact model fibre over a compact base is compact. -/
instance compactSpace_totalSpace [CompactSpace F] [CompactSpace B] :
    CompactSpace (TotalSpace F E) where
  isCompact_univ := by
    simpa using (isProperMap_proj F E).isCompact_preimage (isCompact_univ (X := B))

end FiberBundle

end
