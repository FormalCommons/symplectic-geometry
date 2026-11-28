/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic

/-!
# `ℝ` as an `RCLike` normed field

Mathlib proves `IsRCLikeNormedField 𝕜` from `RCLike 𝕜` by one instance, whose `NormedField 𝕜`
argument is the one of the `RCLike` structure. Finding that instance for `ℝ` therefore asks the
unifier to solve for the `RCLike ℝ` instance while it compares the two normed field structures.
When the search runs inside unification, as when `rw` or `simp` match a lemma whose type class
arguments are instantiated by unification, that nested search exceeds Lean's default
`maxSynthPendingDepth` of `1`, and it fails.

This happens in files that obtain `LieGroup I (minSmoothness ℝ 3) G` from `LieGroup I ∞ G`
through Tau Ceti's local instance `LieGroup.minSmoothness_of_isRCLikeNormedField`: there
Mathlib's lemmas that take a `LieRingModule` instance (`lie_zero`, `lie_neg`, `lie_add`,
`lie_sub`, `lie_smul`) do not rewrite on `GroupLieAlgebra I G`. The instance below gives
`IsRCLikeNormedField ℝ` directly, so that the search needs no nested step.

## Main results

* `Real.isRCLikeNormedField`: `ℝ` is an `RCLike` normed field, as a direct instance.
-/

public section

/-- `ℝ` is an `RCLike` normed field. Mathlib's instance gives this from `Real.instRCLike`; this
direct instance lets a type class search that runs during unification, as in `rw` and `simp`,
find it without solving for the `RCLike ℝ` instance. -/
instance Real.isRCLikeNormedField : IsRCLikeNormedField ℝ :=
  inferInstance

end
