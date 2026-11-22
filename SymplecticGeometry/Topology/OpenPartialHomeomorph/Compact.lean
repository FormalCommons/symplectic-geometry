/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Basic
import TauCeti.Topology.OpenPartialHomeomorph.Basic

/-!
# Compact images under an open partial homeomorphism

An open partial homeomorphism `e : X → Y` is continuous on its source, so it sends a compact
subset of its source to a compact subset of `Y`
(`OpenPartialHomeomorph.isCompact_image_of_subset_source`). This is the compact counterpart of
Mathlib's `OpenPartialHomeomorph.isOpen_image_of_subset_source`.

When `X` is Hausdorff and the closure of `s ⊆ Y` is compact and lies in `e.target`, the image
`e.symm '' s` has closure `e.symm '' closure s`
(`OpenPartialHomeomorph.closure_symm_image_of_isCompact`) and, if `s` is open, frontier
`e.symm '' frontier s` (`OpenPartialHomeomorph.frontier_symm_image_of_isCompact`). The two
proofs follow those of Tau Ceti's `OpenPartialHomeomorph.closure_image_norm_lt_bundle` and
`OpenPartialHomeomorph.frontier_image_norm_lt_bundle`, for a general set in place of a fibre
disc bundle.
-/

public section

namespace OpenPartialHomeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : OpenPartialHomeomorph X Y)

/-- The image under an open partial homeomorphism of a compact subset of its source is
compact. -/
theorem isCompact_image_of_subset_source {s : Set X} (hs : IsCompact s) (h : s ⊆ e.source) :
    IsCompact (e '' s) :=
  hs.image_of_continuousOn (e.continuousOn.mono h)

/-- If `X` is Hausdorff and the closure of `s` is compact and lies in the target of `e`, then the
closure of `e.symm '' s` is the image under `e.symm` of the closure of `s`. -/
theorem closure_symm_image_of_isCompact [T2Space X] {s : Set Y} (hs : IsCompact (closure s))
    (h : closure s ⊆ e.target) : closure (e.symm '' s) = e.symm '' closure s :=
  subset_antisymm
    (closure_minimal (Set.image_mono subset_closure) (e.isClosed_image_symm_of_isCompact hs h))
    (e.continuousOn_symm.mono h).image_closure

/-- If `X` is Hausdorff and `s` is an open set whose closure is compact and lies in the target
of `e`, then the frontier of `e.symm '' s` is the image under `e.symm` of the frontier of `s`. -/
theorem frontier_symm_image_of_isCompact [T2Space X] {s : Set Y} (hso : IsOpen s)
    (hs : IsCompact (closure s)) (h : closure s ⊆ e.target) :
    frontier (e.symm '' s) = e.symm '' frontier s := by
  rw [frontier, e.closure_symm_image_of_isCompact hs h,
    (e.isOpen_image_symm_of_subset_target hso (subset_closure.trans h)).interior_eq,
    hso.frontier_eq, (e.symm.injOn.mono h).image_sdiff_subset subset_closure]

end OpenPartialHomeomorph

end
