/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorField.ModelChart
public import TauCeti.Geometry.Manifold.VectorField.Prod

/-!
# Values of product vector fields

The tangent space of a product `M × N` in the model `I.prod J` is `E × E'`, so the value of
Tau Ceti's product field `TauCeti.Manifold.prodVectorField X Y` at `p` is the pair
`(X p.1, Y p.2)` of `E × E'`, for any models `I` and `J`.

In particular, let `v` be a vector of a real normed space `E` and `N` a manifold over a model
`J`. The product field `(v, 0)` on `E × N`, built from the constant field
`TauCeti.constVectorField v` of `E` and the zero field of `N`, takes the value `(v, 0)` of
`E × E'` at every point. For `E = ℝ` and `v = 1` this is the field `∂_s` on `ℝ × N`; written as
`(1, 0)` its image under a differential is the derivative of a slice `s ↦ f (s, y)`
(`MDifferentiableAt.mfderiv_curry_left_apply`).

## Main results

* `TauCeti.Manifold.prodVectorField_apply`: the value of a product field `(X, Y)` at `p` is the
  pair `(X p.1, Y p.2)` of the model space.
* `TauCeti.Manifold.prodVectorField_constVectorField_zero_apply`: the value of `(v, 0)`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 8
  (vector fields).
-/

public section

open Manifold
open scoped Manifold

namespace TauCeti.Manifold

section Apply

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

/-- The value of the product field `(X, Y)` at `p` is the pair `(X p.1, Y p.2)` of the model
space `E × E'`. -/
theorem prodVectorField_apply (X : Π x : M, TangentSpace I x) (Y : Π y : N, TangentSpace J y)
    (p : M × N) : prodVectorField X Y p = ((X p.1, Y p.2) : E × E') :=
  Prod.ext (prodVectorField_fst _ _ _) (prodVectorField_snd _ _ _)

end Apply

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

/-- The product of the constant field `v` of `E` and the zero field of `N` takes the value
`(v, 0)` at every point of `E × N`. -/
theorem prodVectorField_constVectorField_zero_apply (v : E) (p : E × N) :
    prodVectorField (constVectorField v) (0 : Π y : N, TangentSpace J y) p = (v, (0 : E')) := by
  rw [prodVectorField_apply, constVectorField_apply, NormedSpace.fromTangentSpace_symm_apply,
    Pi.zero_apply]
  -- The zero of `TangentSpace J p.2` is that of `E'` under another name of the instance.
  rfl

end TauCeti.Manifold

end
