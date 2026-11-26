/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The exterior derivative of a function on a normed space

On a real normed space `E`, regarded as a manifold with the model `𝓘(ℝ, E)`, the exterior
derivative of the `0`-form of a function `f` takes on a single vector `v 0` the value of the
Fréchet derivative, `fderiv ℝ f x (v 0)` (`TauCeti.mextDeriv_ofFunction_modelSpace_apply`). It
is Tau Ceti's `TauCeti.mextDeriv_ofFunction_apply` together with
`TauCeti.mvfderiv_eq_fderiv_apply`, stated for every `v : Fin 1 → E` rather than for `![v]`.

## Main results

* `TauCeti.mextDeriv_ofFunction_modelSpace_apply`: `df(x)(v) = fderiv ℝ f x (v 0)` on a normed
  space.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 14 (the differential of a function).
-/

public section

open scoped Manifold

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- On a normed space `E`, the exterior derivative of the `0`-form of `f : E → F` at `x` takes
on `v : Fin 1 → E` the value `fderiv ℝ f x (v 0)`. -/
theorem mextDeriv_ofFunction_modelSpace_apply (f : E → F) (x : E)
    (v : Fin 1 → TangentSpace 𝓘(ℝ, E) x) :
    mextDeriv (RoughForm.ofFunction 𝓘(ℝ, E) f) x v = fderiv ℝ f x (v 0) := by
  rw [mextDeriv_ofFunction, ContinuousAlternatingMap.ofSubsingleton_apply_apply,
    mvfderiv_eq_fderiv_apply]

end TauCeti

end
