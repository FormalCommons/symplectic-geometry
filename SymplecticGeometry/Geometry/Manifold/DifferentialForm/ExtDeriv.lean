/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The exterior derivative of functions

Facts about the exterior derivative `df` of the `0`-form of a function `f` that Tau Ceti does
not state.

At a point where `f` and `g` are differentiable, `d(f + g) = df + dg` and `d(f - g) = df - dg`
(`TauCeti.mextDeriv_ofFunction_add_apply`, `TauCeti.mextDeriv_ofFunction_sub_apply`). So for
differentiable functions `d(f - g) = df - dg` (`TauCeti.mextDeriv_ofFunction_sub`), as Tau
Ceti's `TauCeti.mextDeriv_ofFunction_add` says for sums; the pointwise proofs are those of
`TauCeti.mextDeriv_ofFunction_add`, at one point. Negating a function negates its
exterior derivative (`TauCeti.mextDeriv_ofFunction_neg`, `TauCeti.mextDeriv_ofFunction_fun_neg`),
by Tau Ceti's `TauCeti.mextDeriv_neg` and `TauCeti.RoughForm.ofFunction_neg`
(`DifferentialForm/Basic.lean`). As for Mathlib's
`fderiv_fun_neg` and `fderiv_neg`, the form for `fun x ↦ -f x` is a simp lemma and the form for
`-f` is not.

On a real normed space `E`, regarded as a manifold with the model `𝓘(ℝ, E)`, `df` at `x` takes
on a single vector `v 0` the value of the Fréchet derivative, `fderiv ℝ f x (v 0)`
(`TauCeti.mextDeriv_ofFunction_modelSpace_apply`). It is Tau Ceti's
`TauCeti.mextDeriv_ofFunction_apply` together with `TauCeti.mvfderiv_eq_fderiv_apply`, stated
for every `v : Fin 1 → E` rather than for `![v]`.

## Main results

* `TauCeti.mextDeriv_ofFunction_add_apply`, `TauCeti.mextDeriv_ofFunction_sub_apply`:
  `d(f + g) = df + dg` and `d(f - g) = df - dg` at a point where `f` and `g` are differentiable.
* `TauCeti.mextDeriv_ofFunction_sub`: `d(f - g) = df - dg` for differentiable functions.
* `TauCeti.mextDeriv_ofFunction_neg`, `TauCeti.mextDeriv_ofFunction_fun_neg`: `d(-f) = -df`.
* `TauCeti.mextDeriv_ofFunction_modelSpace_apply`: `df(x)(v) = fderiv ℝ f x (v 0)` on a normed
  space.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 11 (the differential of a function).
-/

public section

open scoped Manifold

namespace TauCeti

section Manifold

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- At a point where two functions are differentiable, the exterior derivative of the `0`-form
of their sum is the sum of their exterior derivatives. -/
theorem mextDeriv_ofFunction_add_apply {f g : M → F} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, F) f x) (hg : MDifferentiableAt I 𝓘(ℝ, F) g x) :
    mextDeriv (RoughForm.ofFunction I (f + g)) x =
      mextDeriv (RoughForm.ofFunction I f) x + mextDeriv (RoughForm.ofFunction I g) x := by
  ext v
  simp [mextDeriv_ofFunction, mvfderiv_add hf hg]

/-- At a point where two functions are differentiable, the exterior derivative of the `0`-form
of their difference is the difference of their exterior derivatives. -/
theorem mextDeriv_ofFunction_sub_apply {f g : M → F} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, F) f x) (hg : MDifferentiableAt I 𝓘(ℝ, F) g x) :
    mextDeriv (RoughForm.ofFunction I (f - g)) x =
      mextDeriv (RoughForm.ofFunction I f) x - mextDeriv (RoughForm.ofFunction I g) x := by
  ext v
  simp [mextDeriv_ofFunction, mvfderiv_sub hf hg]

/-- The exterior derivative of the `0`-form of a difference of differentiable functions is the
difference of their exterior derivatives. -/
theorem mextDeriv_ofFunction_sub {f g : M → F} (hf : MDifferentiable I 𝓘(ℝ, F) f)
    (hg : MDifferentiable I 𝓘(ℝ, F) g) :
    mextDeriv (RoughForm.ofFunction I (f - g)) =
      mextDeriv (RoughForm.ofFunction I f) - mextDeriv (RoughForm.ofFunction I g) :=
  funext fun x ↦ mextDeriv_ofFunction_sub_apply (hf x) (hg x)

/-- The exterior derivative of the `0`-form of `-f` is minus that of `f`. -/
theorem mextDeriv_ofFunction_neg (f : M → F) :
    mextDeriv (RoughForm.ofFunction I (-f)) = -mextDeriv (RoughForm.ofFunction I f) := by
  rw [RoughForm.ofFunction_neg, mextDeriv_neg]

/-- The exterior derivative of the `0`-form of `fun x ↦ -f x` is minus that of `f`. -/
@[simp]
theorem mextDeriv_ofFunction_fun_neg (f : M → F) :
    mextDeriv (RoughForm.ofFunction I fun x ↦ -f x) = -mextDeriv (RoughForm.ofFunction I f) :=
  mextDeriv_ofFunction_neg f

end Manifold

section NormedSpace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- On a normed space `E`, the exterior derivative of the `0`-form of `f : E → F` at `x` takes
on `v : Fin 1 → E` the value `fderiv ℝ f x (v 0)`. -/
theorem mextDeriv_ofFunction_modelSpace_apply (f : E → F) (x : E)
    (v : Fin 1 → TangentSpace 𝓘(ℝ, E) x) :
    mextDeriv (RoughForm.ofFunction 𝓘(ℝ, E) f) x v = fderiv ℝ f x (v 0) := by
  rw [mextDeriv_ofFunction, ContinuousAlternatingMap.ofSubsingleton_apply_apply,
    mvfderiv_eq_fderiv_apply]

end NormedSpace

end TauCeti

end
