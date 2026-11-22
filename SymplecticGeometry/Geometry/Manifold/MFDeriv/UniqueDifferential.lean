/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
# Maps that agree on a set of unique differentiability

Two maps that are differentiable at a point `x` of a set `s` of unique differentiability at `x`,
and agree on `s`, have the same differential at `x`
(`UniqueMDiffWithinAt.mfderiv_eq_of_eqOn`). For example, by Mathlib's `uniqueDiffWithinAt_convex`,
two smooth maps out of a normed space that agree on a closed ball of positive radius have the same
differential at each point of the ball, its boundary included.

This is the form, for `mfderiv`, of Mathlib's `UniqueMDiffWithinAt.eq`, which compares two
derivatives of one map within `s`.
-/

public section

open Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H M E' H' M' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} [TopologicalSpace M'] [ChartedSpace H' M']

/-- Two maps that are differentiable at a point `x` of a set `s` of unique differentiability at
`x`, and agree on `s`, have the same differential at `x`. -/
theorem UniqueMDiffWithinAt.mfderiv_eq_of_eqOn {s : Set M} {x : M} {f g : M → M'}
    (hs : UniqueMDiffWithinAt I s x) (hx : x ∈ s) (hf : MDifferentiableAt I I' f x)
    (hg : MDifferentiableAt I I' g x) (h : EqOn f g s) :
    mfderiv I I' f x = mfderiv I I' g x :=
  hs.eq hf.hasMFDerivAt.hasMFDerivWithinAt
    (hg.hasMFDerivAt.hasMFDerivWithinAt.congr_mono (fun _ hy ↦ h hy) (h hx) subset_rfl)
