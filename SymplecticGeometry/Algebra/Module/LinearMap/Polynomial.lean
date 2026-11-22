/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Polynomial
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Pulling polynomials back along a matrix

For a matrix `M : Matrix m n R`, Mathlib's `Matrix.toMvPolynomial M` is the family of linear forms
`∑ j, M i j * X j` in the variables indexed by `n`. Substituting it into a polynomial `q` in the
variables indexed by `m` pulls `q` back along the linear map `v ↦ M *ᵥ v`. This file records how
the pullback evaluates and how the linear forms differentiate.

## Main results

* `Matrix.eval_aeval_toMvPolynomial`: `eval v (aeval M.toMvPolynomial q) = eval (M *ᵥ v) q`.
* `Matrix.pderiv_toMvPolynomial`: `pderiv j (M.toMvPolynomial i) = C (M i j)`.

The first lemma states, for a general matrix, a step of the proof of Tau Ceti's
`TauCeti.preimage_map_complexProjectiveZeroLocus`.
-/

public section

open MvPolynomial
open scoped Matrix

namespace Matrix

variable {m n R : Type*} [CommSemiring R] [Fintype n]

/-- Evaluating at `v` the pullback of `q` along the linear forms of `M` is evaluating `q` at
`M *ᵥ v`. -/
theorem eval_aeval_toMvPolynomial (M : Matrix m n R) (v : n → R) (q : MvPolynomial m R) :
    eval v (aeval M.toMvPolynomial q) = eval (M *ᵥ v) q := by
  simpa only [aeval_eq_eval, toMvPolynomial_eval_eq_apply] using
    comp_aeval_apply M.toMvPolynomial (aeval v) q

/-- The partial derivative in the variable `j` of the `i`-th linear form of `M` is the constant
`M i j`. -/
@[simp]
theorem pderiv_toMvPolynomial (M : Matrix m n R) (i : m) (j : n) :
    pderiv j (M.toMvPolynomial i) = C (M i j) := by
  classical
  simp [toMvPolynomial, ← C_mul_X_eq_monomial, pderiv_X, Pi.single_apply]

end Matrix

end
