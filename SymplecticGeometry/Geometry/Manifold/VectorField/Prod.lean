/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorField.ModelChart
public import TauCeti.Geometry.Manifold.VectorField.Prod

/-!
# Product vector fields with a constant first factor

Let `v` be a vector of a real normed space `E` and `N` a manifold over a model `J`. The product
field `(v, 0)` on `E × N`, built by Tau Ceti's `TauCeti.Manifold.prodVectorField` from the
constant field `TauCeti.constVectorField v` of `E` and the zero field of `N`, takes the value
`(v, 0)` of `E × E'` at every point, the tangent space of `E × N` being `E × E'` in the model
`𝓘(ℝ, E).prod J`. For `E = ℝ` and `v = 1` this is the field `∂_s` on `ℝ × N`; written as
`(1, 0)` its image under a differential is the derivative of a slice `s ↦ f (s, y)`
(`MDifferentiableAt.mfderiv_curry_left_apply`).

## Main results

* `TauCeti.Manifold.prodVectorField_constVectorField_zero_apply`: the value of `(v, 0)`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 8
  (vector fields).
-/

public section

open Manifold
open scoped Manifold

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

/-- The product of the constant field `v` of `E` and the zero field of `N` takes the value
`(v, 0)` at every point of `E × N`. -/
theorem prodVectorField_constVectorField_zero_apply (v : E) (p : E × N) :
    prodVectorField (constVectorField v) (0 : Π y : N, TangentSpace J y) p = (v, (0 : E')) :=
  -- Both components are equal in the model spaces, where the tangent spaces are `E` and `E'`.
  Prod.ext (by simp only [prodVectorField_fst, constVectorField_apply]; rfl)
    (by simp only [prodVectorField_snd, Pi.zero_apply]; rfl)

end TauCeti.Manifold

end
