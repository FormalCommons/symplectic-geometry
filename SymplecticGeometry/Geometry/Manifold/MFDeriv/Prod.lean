/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Partial derivatives of a map on a product manifold

For a family `f : M → M' → M''` whose uncurried form is differentiable at `(x, y)`, the
derivative of `Function.uncurry f` at `(x, y)` on a tangent vector `(v, 0)` is the derivative at
`x` of the slice `z ↦ f z y` on `v` (`MDifferentiableAt.mfderiv_uncurry_apply_mk_zero`). This is
the counterpart, for the first factor, of Tau Ceti's
`MDifferentiableAt.mfderiv_uncurry_apply_zero_mk`, which treats tangent vectors `(0, w)`. It is
stated in the same form, and has the proof of Tau Ceti's lemma with the two summands of Mathlib's
`mfderiv_prod_eq_add_apply` exchanged.

The differentiability hypothesis cannot be dropped: if `Function.uncurry f` is not differentiable
at `(x, y)`, its `mfderiv` is `0`, while a slice can still be differentiable with a nonzero
derivative.
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

variable {f : M → M' → M''} {x : M} {y : M'}

/-- The differential of an uncurried family `(x, y) ↦ f x y`, differentiable at `(x, y)`, on a
horizontal tangent vector `(v, 0)` is the differential of the slice `z ↦ f z y` at `x` on `v`. -/
theorem mfderiv_uncurry_apply_mk_zero
    (hf : MDifferentiableAt (I.prod I') I'' (Function.uncurry f) (x, y)) (v : TangentSpace I x) :
    mfderiv (I.prod I') I'' (Function.uncurry f) (x, y) (v, 0) =
      mfderiv I I'' (fun z ↦ f z y) x v :=
  (mfderiv_prod_eq_add_apply hf).trans <| (congrArg (_ + ·) (map_zero _)).trans (add_zero _)

end MDifferentiableAt

end
