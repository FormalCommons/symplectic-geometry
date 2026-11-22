/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.ChangeOfVariables
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Positivity of the Riemannian Jacobian

Tau Ceti's `TauCeti.riemannianJacobian b f x` of a map `f` from a finite-dimensional real normed
space `F` to a manifold with a Riemannian metric is the square root of the determinant of the
Gram matrix of the images of the basis `b` under `mfderiv f x`. This file shows that it is
positive where that differential is injective: the images of the basis are then linearly
independent, so their Gram matrix is positive definite.

## Main results

* `TauCeti.riemannianJacobian_pos`: the Riemannian Jacobian is positive where the differential is
  injective.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 2.
-/

public section

open Bundle
open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace TauCeti

/-- The Riemannian Jacobian of `f` at `x` is positive when the differential of `f` at `x` is
injective. -/
theorem riemannianJacobian_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ F) {f : F → M} {x : F}
    (hf : Function.Injective (mfderiv 𝓘(ℝ, F) I f x)) :
    0 < riemannianJacobian (I := I) b f x := by
  rw [riemannianJacobian_eq_sqrt_det_gram, Real.sqrt_pos]
  refine (Matrix.posDef_gram_of_linearIndependent ?_).det_pos
  exact b.linearIndependent.map' (mfderiv 𝓘(ℝ, F) I f x).toLinearMap
    (LinearMap.ker_eq_bot.2 hf)

end TauCeti

end
