/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Logic.Equiv.PartialEquiv

/-!
# Partial equivalences and actions

Let `G` act on two types `α` and `β`. A partial equivalence `e` from `α` to `β` that commutes with
the actions at the points of its source, and whose source is invariant under `G`, has a target
invariant under `G`: a point of the target is `e x` for `x` in the source, and `g • e x` is
`e (g • x)`.

## Main results

* `PartialEquiv.smul_mem_target`: an equivariant partial equivalence with invariant source has
  invariant target.
-/

public section

namespace PartialEquiv

/-- A partial equivalence that commutes with the actions of `G` at the points of its source, and
whose source is invariant under `G`, has a target invariant under `G`. -/
theorem smul_mem_target {α β G : Type*} [SMul G α] [SMul G β] {e : PartialEquiv α β}
    (he : ∀ (g : G), ∀ x ∈ e.source, e (g • x) = g • e x)
    (hs : ∀ (g : G), ∀ x ∈ e.source, g • x ∈ e.source) (g : G) {y : β} (hy : y ∈ e.target) :
    g • y ∈ e.target := by
  rw [← e.right_inv hy, ← he g _ (e.map_target hy)]
  exact e.map_source (hs g _ (e.map_target hy))

end PartialEquiv

end
