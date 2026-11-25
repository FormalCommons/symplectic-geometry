/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Partial derivatives of a map on a product manifold

For a map `f : M × M' → M''` that is differentiable at `p`, the derivative of `f` at `p` on a
tangent vector `(v, 0)` is the derivative at `p.1` of the slice `z ↦ f (z, p.2)` on `v`
(`MDifferentiableAt.mfderiv_curry_left_apply`). This is the counterpart, for the first factor, of
Tau Ceti's `MDifferentiableAt.mfderiv_uncurry_apply_zero_mk`, which treats tangent vectors
`(0, w)`, and has the proof of Tau Ceti's lemma with the two summands of Mathlib's
`mfderiv_prod_eq_add_apply` exchanged.

The differentiability hypothesis cannot be dropped: if `f` is not differentiable at `p`, its
`mfderiv` is `0`, while a slice can still be differentiable with a nonzero derivative.
-/

public section

open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {H'' : Type*}
  [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''} {M'' : Type*}
  [TopologicalSpace M''] [ChartedSpace H'' M'']

namespace MDifferentiableAt

variable {f : M × M' → M''} {p : M × M'}

/-- The derivative of a map on a product, differentiable at `p`, on a vector `(v, 0)` is the
derivative of its slice `z ↦ f (z, p.2)` at `p.1` on `v`. -/
theorem mfderiv_curry_left_apply (hf : MDifferentiableAt (I.prod I') I'' f p)
    (v : E) :
    mfderiv (I.prod I') I'' f p (v, (0 : E')) =
      mfderiv I I'' (fun z ↦ f (z, p.2)) p.1 v :=
  (mfderiv_prod_eq_add_apply hf).trans <| (congrArg (_ + ·) (map_zero _)).trans (add_zero _)

end MDifferentiableAt

end
