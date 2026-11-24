/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Algebra.MvPolynomial.Rename

/-!
# Polynomials with multivariable polynomial coefficients as multivariable polynomials

A polynomial `Q : (MvPolynomial σ R)[X]` in one variable, with coefficients polynomials in the
variables `σ`, is turned into a polynomial in the variables `σ ⊕ Unit` by sending the variables of
the coefficients to `σ` and the outer variable to the extra variable. This file computes the value
of the result at a point: it is the value of `Q`, with coefficients evaluated at the `σ`
coordinates, at the extra coordinate.

* `MvPolynomial.eval_eval₂_rename_inl_X_inr`: the statement above.

This is how a polynomial relation `Q (x, f x) = 0` between the coordinates and the value of a
function becomes the vanishing of one polynomial on the graph of the function. The proof
reduces to Tau Ceti's `Polynomial.map_eval_map_rename`.
-/

public section

namespace MvPolynomial

open scoped Polynomial in
/-- Turning `Q : (MvPolynomial σ R)[X]` into a polynomial in the variables `σ ⊕ Unit`, with the
outer variable as the extra variable, and evaluating at `p` gives the value at `p (.inr ())` of
`Q` with coefficients evaluated at `p ∘ Sum.inl`. -/
theorem eval_eval₂_rename_inl_X_inr {σ R : Type*} [CommSemiring R]
    (Q : (MvPolynomial σ R)[X]) (p : σ ⊕ Unit → R) :
    eval p (Q.eval₂ (rename Sum.inl).toRingHom (X (.inr ()))) =
      (Q.map (eval (p ∘ Sum.inl))).eval (p (.inr ())) := by
  rw [Polynomial.hom_eval₂, ← Polynomial.eval_map, ← Polynomial.map_map,
    Polynomial.map_eval_map_rename, eval_X]

end MvPolynomial

end
