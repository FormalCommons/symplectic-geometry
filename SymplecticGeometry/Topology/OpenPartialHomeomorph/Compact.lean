/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# Compact images under an open partial homeomorphism

An open partial homeomorphism `e : X → Y` is continuous on its source, so it sends a compact
subset of its source to a compact subset of `Y`
(`OpenPartialHomeomorph.isCompact_image_of_subset_source`). This is the compact counterpart of
Mathlib's `OpenPartialHomeomorph.isOpen_image_of_subset_source`.
-/

public section

namespace OpenPartialHomeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : OpenPartialHomeomorph X Y)

/-- The image under an open partial homeomorphism of a compact subset of its source is
compact. -/
theorem isCompact_image_of_subset_source {s : Set X} (hs : IsCompact s) (h : s ⊆ e.source) :
    IsCompact (e '' s) :=
  hs.image_of_continuousOn (e.continuousOn.mono h)

end OpenPartialHomeomorph

end
