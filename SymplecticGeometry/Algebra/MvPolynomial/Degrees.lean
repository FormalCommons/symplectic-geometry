/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Total degree of a multivariate polynomial with a zero

A polynomial of total degree zero is a constant `C r`, by Mathlib's
`MvPolynomial.totalDegree_eq_zero_iff_eq_C`. So a nonzero polynomial that vanishes at some point
has positive total degree.

* `MvPolynomial.totalDegree_ne_zero_of_eval_eq_zero`: the statement above.
-/

public section

namespace MvPolynomial

/-- A nonzero polynomial that vanishes somewhere is not constant. -/
theorem totalDegree_ne_zero_of_eval_eq_zero {σ R : Type*} [CommSemiring R]
    {P : MvPolynomial σ R} (hP : P ≠ 0) {x : σ → R} (hx : eval x P = 0) :
    P.totalDegree ≠ 0 := fun h ↦ by
  rw [totalDegree_eq_zero_iff_eq_C] at h
  rw [h, eval_C] at hx
  exact hP (by rw [h, hx, map_zero])

end MvPolynomial

end
