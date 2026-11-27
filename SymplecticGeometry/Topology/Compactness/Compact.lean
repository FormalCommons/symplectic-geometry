/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Compactness.Compact

/-!
# The tube lemma for a compact subset

For an open set `W ⊆ Λ × X` and a compact set `T ⊆ X`, the parameters `l` with
`(l, x) ∈ W` for every `x ∈ T` form an open subset of `Λ`
(`IsCompact.isOpen_setOfPred_forall_prodMk_mem`). This is Mathlib's
`IsCompact.eventually_forall_of_forall_eventually` applied to the membership in `W`.

Tau Ceti's `TauCeti.isOpen_forall_prodMk_mem` proves the same statement with the points `x`
ranging over a continuous image of a compact space. The lemma here restates it for a compact
subset, and its proof follows the proof of that lemma.

## Main results

* `IsCompact.isOpen_setOfPred_forall_prodMk_mem`: the set of parameters whose slice over a
  compact set lies in a given open set of the product is open.
-/

public section

variable {Λ X : Type*} [TopologicalSpace Λ] [TopologicalSpace X]

/-- For a compact `T ⊆ X` and an open `W ⊆ Λ × X`, the set of `l : Λ` with `(l, x) ∈ W` for
every `x ∈ T` is open. -/
theorem IsCompact.isOpen_setOfPred_forall_prodMk_mem {T : Set X} (hT : IsCompact T)
    {W : Set (Λ × X)} (hW : IsOpen W) : IsOpen {l | ∀ x ∈ T, (l, x) ∈ W} :=
  isOpen_iff_eventually.2 fun _ hl ↦ hT.eventually_forall_of_forall_eventually
    (P := fun l x ↦ (l, x) ∈ W) fun x hx ↦ hW.mem_nhds (hl x hx)

end
