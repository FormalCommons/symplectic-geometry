/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

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

Read through Tau Ceti's identification `TauCeti.Manifold.tangentSpaceProdEquiv` of the tangent
space of a product with the product of the tangent spaces, the differential of the slice inclusion
`y ↦ (x, y)` sends `w` to `(0, w)` (`TauCeti.Manifold.tangentSpaceProdEquiv_mfderiv_prodMk_right`)
and that of `x ↦ (x, y)` sends `v` to `(v, 0)`
(`TauCeti.Manifold.tangentSpaceProdEquiv_mfderiv_prodMk_left`). These restate Mathlib's
`mfderiv_prod_right` and `mfderiv_prod_left` on vectors, so that proofs need not unfold the tangent
space of a product to the product of the model spaces. They sit next to Tau Ceti's
`TauCeti.Manifold.tangentSpaceProdEquiv_mfderiv_prodMap_id`, which treats `Prod.map id φ`.

That identification is the identity map, so the same two facts also hold with the tangent vector of
`M × M'` written directly as a pair (`mfderiv_prodMk_right_apply`, `mfderiv_prodMk_left_apply`).
These are the forms that `rw` and `simp` can use on the differential of a slice inclusion applied
to a vector.
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

namespace TauCeti.Manifold

variable {x : M} {y : M'}

/-- Under the identification of the tangent space of `M × M'` with the product of the tangent
spaces, the differential at `y` of the slice inclusion `z ↦ (x, z)` sends `w` to `(0, w)`. -/
theorem tangentSpaceProdEquiv_mfderiv_prodMk_right (w : TangentSpace I' y) :
    tangentSpaceProdEquiv (x, y) (mfderiv I' (I.prod I') (fun z ↦ (x, z)) y w) = (0, w) := by
  rw [mfderiv_prod_right, tangentSpaceProdEquiv_apply]
  exact ContinuousLinearMap.inr_apply ..

/-- Under the identification of the tangent space of `M × M'` with the product of the tangent
spaces, the differential at `x` of the slice inclusion `z ↦ (z, y)` sends `v` to `(v, 0)`. -/
theorem tangentSpaceProdEquiv_mfderiv_prodMk_left (v : TangentSpace I x) :
    tangentSpaceProdEquiv (x, y) (mfderiv I (I.prod I') (fun z ↦ (z, y)) x v) = (v, 0) := by
  rw [mfderiv_prod_left, tangentSpaceProdEquiv_apply]
  exact ContinuousLinearMap.inl_apply ..

end TauCeti.Manifold

variable {x : M} {y : M'}

/-- The differential at `y` of the slice inclusion `z ↦ (x, z)` sends `w` to the tangent vector
`(0, w)` of `M × M'` at `(x, y)`. -/
theorem mfderiv_prodMk_right_apply (w : TangentSpace I' y) :
    mfderiv I' (I.prod I') (fun z ↦ (x, z)) y w = (0, w) :=
  (TauCeti.Manifold.tangentSpaceProdEquiv_apply _ _).symm.trans
    (TauCeti.Manifold.tangentSpaceProdEquiv_mfderiv_prodMk_right w)

/-- The differential at `x` of the slice inclusion `z ↦ (z, y)` sends `v` to the tangent vector
`(v, 0)` of `M × M'` at `(x, y)`. -/
theorem mfderiv_prodMk_left_apply (v : TangentSpace I x) :
    mfderiv I (I.prod I') (fun z ↦ (z, y)) x v = (v, 0) :=
  (TauCeti.Manifold.tangentSpaceProdEquiv_apply _ _).symm.trans
    (TauCeti.Manifold.tangentSpaceProdEquiv_mfderiv_prodMk_left v)

end
