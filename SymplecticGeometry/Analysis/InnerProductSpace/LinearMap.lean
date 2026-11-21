/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# The real inner product as a bilinear map

This file complements Mathlib's `Mathlib/Analysis/InnerProductSpace/LinearMap.lean`, which
defines `innerSL` and proves `innerSL_apply_apply`. Over `ℝ` the map
`innerSL ℝ : E →L⋆[ℝ] E →L[ℝ] ℝ` is also a term of the real bilinear type
`E →L[ℝ] E →L[ℝ] ℝ`, and is often used at that type, for example as an element of a set of
continuous bilinear forms. Mathlib's `innerSL_apply_apply` is stated for the coercion at the
conjugate-linear type, so `simp` cannot use it for the coercion at the bilinear type.

## Main results

* `innerSL_real_apply_apply`: `innerSL ℝ`, coerced to a function at the type
  `E →L[ℝ] E →L[ℝ] ℝ`, evaluates at `u` and `v` to `⟪u, v⟫`.
-/

public section

/-- The inner product of a real inner product space, read as a real bilinear map
`E →L[ℝ] E →L[ℝ] ℝ` rather than as the conjugate-linear map `innerSL ℝ : E →L⋆[ℝ] E →L[ℝ] ℝ`,
evaluates at `u` and `v` to `⟪u, v⟫`. -/
@[simp]
theorem innerSL_real_apply_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) :
    -- The coercion is given at the type `E →L[ℝ] E →L[ℝ] ℝ`, so that the left side matches
    -- `innerSL ℝ` used as a term of that type, where `innerSL_apply_apply` does not apply.
    @DFunLike.coe (E →L[ℝ] E →L[ℝ] ℝ) E (fun _ ↦ E →L[ℝ] ℝ) _ (innerSL ℝ) u v = inner ℝ u v :=
  innerSL_apply_apply ..

end
