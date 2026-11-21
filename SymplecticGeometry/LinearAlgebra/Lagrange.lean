/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Lagrange

/-!
# Evaluating the Lagrange basis

Two facts about Mathlib's Lagrange basis polynomials `Lagrange.basis s v i`, for a finite set
`s` of indices and nodes `v : ι → F` in a field `F`.

* `Lagrange.eval_basis`: the value of `basis s v i` at any point `x` is the product
  `∏ j ∈ s.erase i, (x - v j) / (v i - v j)`. This needs no injectivity: if two nodes coincide,
  both sides vanish.
* `Lagrange.sum_eval_basis_mul_eval`: for distinct nodes, the Lagrange weights
  `(basis s v i).eval x` reproduce every polynomial of degree less than `#s`, that is
  `∑ i ∈ s, (basis s v i).eval x * P.eval (v i) = P.eval x`; and
  `Lagrange.sum_eval_basis_mul_pow` is its case `P = X ^ n`, for `n < #s`.

The reproduction identity is Mathlib's `Lagrange.eq_interpolate` evaluated at `x`. Tau Ceti's
`TauCeti.sum_higherReflectionCoeff_mul_eval` makes the same argument for its reflection nodes
in `ℝ` at `x = 1`.
-/

public section

open Finset Polynomial

namespace Lagrange

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → F}

/-- The value of the Lagrange basis polynomial `basis s v i` at a point `x` is
`∏ j ∈ s.erase i, (x - v j) / (v i - v j)`. -/
theorem eval_basis (s : Finset ι) (v : ι → F) (i : ι) (x : F) :
    (Lagrange.basis s v i).eval x = ∏ j ∈ s.erase i, (x - v j) / (v i - v j) := by
  rw [Lagrange.basis, eval_prod]
  refine prod_congr rfl fun j _ ↦ ?_
  rw [basisDivisor, eval_mul, eval_C, eval_sub, eval_X, eval_C, div_eq_inv_mul]

/-- For nodes `v` that are distinct on `s`, the Lagrange weights at a point `x` reproduce
every polynomial `P` of degree less than `#s`:
`∑ i ∈ s, (basis s v i).eval x * P.eval (v i) = P.eval x`. -/
theorem sum_eval_basis_mul_eval (hvs : Set.InjOn v s) {P : F[X]} (hP : P.degree < #s) (x : F) :
    ∑ i ∈ s, (Lagrange.basis s v i).eval x * P.eval (v i) = P.eval x := by
  conv_rhs => rw [eq_interpolate hvs hP, interpolate_apply, eval_finsetSum]
  simp only [eval_mul, eval_C, mul_comm]

/-- For nodes `v` that are distinct on `s` and `n < #s`, the Lagrange weights at a point `x`
reproduce the power `x ^ n`: `∑ i ∈ s, (basis s v i).eval x * v i ^ n = x ^ n`. -/
theorem sum_eval_basis_mul_pow (hvs : Set.InjOn v s) {n : ℕ} (hn : n < #s) (x : F) :
    ∑ i ∈ s, (Lagrange.basis s v i).eval x * v i ^ n = x ^ n := by
  have hdeg : (X ^ n : F[X]).degree < #s :=
    (degree_X_pow_le n).trans_lt (by exact_mod_cast hn)
  simpa only [eval_pow, eval_X] using sum_eval_basis_mul_eval hvs hdeg x

end Lagrange

end
