/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Polynomial
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Differentiating the linear forms of a matrix

For a matrix `M : Matrix m n R`, Mathlib's `Matrix.toMvPolynomial M` is the family of linear forms
`∑ j, M i j * X j` in the variables indexed by `n`. Substituting it into a polynomial `q` in the
variables indexed by `m` pulls `q` back along the linear map `v ↦ M *ᵥ v`; Tau Ceti's
`Matrix.eval_aeval_toMvPolynomial` says how the pullback evaluates. This file records how the
linear forms differentiate.

## Main results

* `Matrix.pderiv_toMvPolynomial`: `pderiv j (M.toMvPolynomial i) = C (M i j)`.
-/

public section

open MvPolynomial

namespace Matrix

variable {m n R : Type*} [CommSemiring R] [Fintype n]

/-- The partial derivative in the variable `j` of the `i`-th linear form of `M` is the constant
`M i j`. -/
@[simp]
theorem pderiv_toMvPolynomial (M : Matrix m n R) (i : m) (j : n) :
    pderiv j (M.toMvPolynomial i) = C (M i j) := by
  classical
  simp [toMvPolynomial, ← C_mul_X_eq_monomial, pderiv_X, Pi.single_apply]

end Matrix

end
