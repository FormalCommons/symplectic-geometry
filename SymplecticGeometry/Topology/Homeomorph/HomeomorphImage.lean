/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Coercion lemmas for the homeomorphism onto the image of an embedding

For an embedding `f : X → Y` and a set `s` of `X`, Mathlib's
`Topology.IsEmbedding.homeomorphImage` is the homeomorphism `s ≃ₜ f '' s` given by `f`. This file
states how it and its inverse act on points, seen in `Y` and in `X`:
`Topology.IsEmbedding.homeomorphImage_apply_coe` and
`Topology.IsEmbedding.apply_homeomorphImage_symm_apply`. They are the counterparts for
`homeomorphImage` of Mathlib's `Topology.IsEmbedding.homeomorphOfSubsetRange_apply_coe`.

## Main results

* `Topology.IsEmbedding.homeomorphImage_apply_coe`: `(hf.homeomorphImage s x : Y) = f x`.
* `Topology.IsEmbedding.apply_homeomorphImage_symm_apply`:
  `f ((hf.homeomorphImage s).symm y) = y`.
-/

public section

namespace Topology.IsEmbedding

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

/-- The homeomorphism `s ≃ₜ f '' s` of an embedding `f` sends a point `x` of `s` to `f x`. -/
@[simp]
theorem homeomorphImage_apply_coe (hf : IsEmbedding f) (s : Set X) (x : s) :
    (hf.homeomorphImage s x : Y) = f x :=
  (rfl)

/-- The inverse of the homeomorphism `s ≃ₜ f '' s` of an embedding `f` sends a point `y` of
`f '' s` to a point of `s` that `f` maps to `y`. -/
theorem apply_homeomorphImage_symm_apply (hf : IsEmbedding f) (s : Set X) (y : f '' s) :
    f ((hf.homeomorphImage s).symm y) = y := by
  rw [← homeomorphImage_apply_coe hf s, Homeomorph.apply_symm_apply]

end Topology.IsEmbedding

end
