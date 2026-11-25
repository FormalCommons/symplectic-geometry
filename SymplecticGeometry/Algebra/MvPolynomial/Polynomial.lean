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
variables `σ`, is turned into a polynomial in the variables `τ` by renaming the variables of the
coefficients along a map `f : σ → τ` and sending the outer variable to a variable `t : τ`. This
file computes the value of the result at a point `p`: it is the value at `p t` of `Q`, with
coefficients evaluated at `p ∘ f`.

* `MvPolynomial.eval_eval₂_rename_X`: the statement above.

This is how a polynomial relation `Q (x, f x) = 0` between the coordinates and the value of a
function becomes the vanishing of one polynomial on the graph of the function, with
`f = Sum.inl : σ → σ ⊕ Unit` and `t = Sum.inr ()`. The proof reduces to Tau Ceti's
`Polynomial.map_eval_map_rename`.
-/

public section

namespace MvPolynomial

open scoped Polynomial in
/-- Turning `Q : (MvPolynomial σ R)[X]` into a polynomial in the variables `τ`, by renaming the
variables of the coefficients along `f` and sending the outer variable to `X t`, and evaluating at
`p` gives the value at `p t` of `Q` with coefficients evaluated at `p ∘ f`. -/
@[simp]
theorem eval_eval₂_rename_X {σ τ R : Type*} [CommSemiring R] (f : σ → τ) (t : τ)
    (Q : (MvPolynomial σ R)[X]) (p : τ → R) :
    eval p (Q.eval₂ ((rename f : MvPolynomial σ R →ₐ[R] MvPolynomial τ R) :
      MvPolynomial σ R →+* MvPolynomial τ R) (X t)) =
      (Q.map (eval (p ∘ f))).eval (p t) := by
  rw [Polynomial.hom_eval₂, ← Polynomial.eval_map, ← Polynomial.map_map,
    ← AlgHom.toRingHom_eq_coe, Polynomial.map_eval_map_rename, eval_X]

end MvPolynomial

end
