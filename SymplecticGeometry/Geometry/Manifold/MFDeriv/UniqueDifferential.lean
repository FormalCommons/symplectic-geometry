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

Composed with a map `ι : N → M`, it computes the differential of a map `f` on the image of a
tangent vector. Let `x` be a point of a set `s` of unique differentiability at `x`, and `f`
differentiable at `ι x`. If `f ∘ ι` agrees on `s` with a map `g`, and `ι` and `g` have derivatives
`ι'` and `g'` within `s` at `x`, then `df` at `ι x` sends `ι' v` to `g' v`
(`UniqueMDiffWithinAt.mfderiv_apply_eq_of_eqOn_comp`). For `ι` a line `r ↦ (r, y)` in a product
of vector spaces and `s` a closed interval, this is the derivative of `f` in the direction of the
first factor, read off from a map `g` that `f` extends along the line.
-/

public section

open Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H M E' H' M' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} [TopologicalSpace M'] [ChartedSpace H' M']
  {F G N : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} [TopologicalSpace N] [ChartedSpace G N]

/-- Two maps that are differentiable at a point `x` of a set `s` of unique differentiability at
`x`, and agree on `s`, have the same differential at `x`. -/
theorem UniqueMDiffWithinAt.mfderiv_eq_of_eqOn {s : Set M} {x : M} {f g : M → M'}
    (hs : UniqueMDiffWithinAt I s x) (hx : x ∈ s) (hf : MDifferentiableAt I I' f x)
    (hg : MDifferentiableAt I I' g x) (h : EqOn f g s) :
    mfderiv I I' f x = mfderiv I I' g x :=
  hs.eq hf.hasMFDerivAt.hasMFDerivWithinAt
    (hg.hasMFDerivAt.hasMFDerivWithinAt.congr_mono (fun _ hy ↦ h hy) (h hx) subset_rfl)

/-- Let `ι : N → M` have derivative `ι'` within `s` at a point `x` of a set `s` of unique
differentiability at `x`, and let `f : M → M'` be differentiable at `ι x`. If `f ∘ ι` agrees on
`s` with a map `g` that has derivative `g'` within `s` at `x`, then the differential of `f` at
`ι x` sends `ι' v` to `g' v`. -/
theorem UniqueMDiffWithinAt.mfderiv_apply_eq_of_eqOn_comp {s : Set N} {x : N} {ι : N → M}
    {ι' : TangentSpace J x →L[𝕜] TangentSpace I (ι x)} {f : M → M'} {g : N → M'}
    {g' : TangentSpace J x →L[𝕜] TangentSpace I' (g x)}
    (hs : UniqueMDiffWithinAt J s x) (hx : x ∈ s) (hf : MDifferentiableAt I I' f (ι x))
    (hι : HasMFDerivWithinAt J I ι s x ι') (hg : HasMFDerivWithinAt J I' g s x g')
    (h : EqOn (f ∘ ι) g s) (v : TangentSpace J x) : mfderiv I I' f (ι x) (ι' v) = g' v :=
  DFunLike.congr_fun (hs.eq (hf.hasMFDerivAt.comp_hasMFDerivWithinAt x hι)
    (hg.congr_mono (fun _ hy ↦ h hy) (h hx) subset_rfl)) v
