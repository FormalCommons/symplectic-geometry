/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.Analysis.MvPolynomial.Jacobian

/-!
# The gradient of a real polynomial function

For a real polynomial `P` in the variables `ι`, read as a function on `EuclideanSpace ℝ ι`, the
gradient at `x` is the vector of the formal partial derivatives of `P` evaluated at `x`
(`MvPolynomial.gradient_eval`), so its norm is the square root of the sum of their squares
(`MvPolynomial.norm_gradient_eval`). This refines Tau Ceti's
`MvPolynomial.fderiv_eval_euclidean_single`, which computes the derivative in each coordinate
direction.
-/

public section

namespace MvPolynomial

variable {ι : Type*} [Fintype ι]

/-- The gradient of a real polynomial function on Euclidean space is the vector of its formal
partial derivatives, evaluated at the point. -/
@[simp]
theorem gradient_eval (P : MvPolynomial ι ℝ) (x : EuclideanSpace ℝ ι) :
    gradient (fun y : EuclideanSpace ℝ ι ↦ eval y P) x =
      WithLp.toLp 2 (fun i ↦ eval x (pderiv i P)) := by
  classical
  ext i
  trans fderiv ℝ (fun y : EuclideanSpace ℝ ι ↦ eval y P) x (EuclideanSpace.single i 1)
  · rw [← toDual_gradient, InnerProductSpace.toDual_apply_apply, real_inner_comm,
      EuclideanSpace.inner_single_left]
    simp
  · simp

/-- The norm of the gradient of a real polynomial function on Euclidean space is the square root
of the sum of the squares of its formal partial derivatives, evaluated at the point. -/
theorem norm_gradient_eval (P : MvPolynomial ι ℝ) (x : EuclideanSpace ℝ ι) :
    ‖gradient (fun y : EuclideanSpace ℝ ι ↦ eval y P) x‖ = √(∑ i, eval x (pderiv i P) ^ 2) := by
  simp [gradient_eval, EuclideanSpace.norm_eq]

end MvPolynomial

end
