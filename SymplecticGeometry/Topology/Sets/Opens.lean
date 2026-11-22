/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Topology.Sets.Opens

/-!
# Covers of a space by an empty family of open sets

If the supremum of a family of open sets of `X` is `⊤` and the family is empty, then `X` is
empty (`TopologicalSpace.Opens.isEmpty_of_iSup_eq_top`).

This is a lemma of Tau Ceti's main branch (`TauCeti/Topology/Sets/Opens.lean`, same name), as of the
commit `b9a3084bbb4cc2ac2c5a0b3ae0323198b47a34b8`, not yet in the pinned release; it is stated here
under its Tau Ceti name, so that moving Tau Ceti past it deletes this file without renames.
-/

public section

namespace TopologicalSpace.Opens

variable {X : Type*} [TopologicalSpace X]

/-- A family of open sets indexed by an empty type covers only the empty space. -/
theorem isEmpty_of_iSup_eq_top {ι : Sort*} [IsEmpty ι] {U : ι → Opens X}
    (hcover : ⨆ i, U i = ⊤) : IsEmpty X :=
  ⟨fun x ↦ isEmptyElim (Opens.mem_iSup.1 (hcover ▸ Opens.mem_top x)).choose⟩

end TopologicalSpace.Opens

end
