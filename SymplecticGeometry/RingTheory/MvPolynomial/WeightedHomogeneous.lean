/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# Partial derivatives of weighted homogeneous polynomials at their zeros

Let `f` be weighted homogeneous for the weights `w`, and let `p` be a zero of `f` with `p i ≠ 0`
and `(w i : R) ≠ 0`. If every partial derivative `∂ₖ f` with `k ≠ i` and `w k ≠ 0` vanishes at
`p`, then so does `∂ᵢ f`
(`MvPolynomial.IsWeightedHomogeneous.eval_pderiv_eq_zero_of_eval_eq_zero`). This follows from
Euler's identity, Mathlib's `MvPolynomial.IsWeightedHomogeneous.sum_weight_X_mul_pderiv`.

For a polynomial in several blocks of homogeneous coordinates, weighting one block by `1` and the
others by `0` shows that, in the affine chart where `p i ≠ 0`, the derivative in the variable `i`
is not needed to decide whether the gradient vanishes at a zero. This is the multi-block analogue
of the single-block statement in Tau Ceti's `forall_eval_pderiv_eq_zero_iff_dehomogenize`.
-/

public section

namespace MvPolynomial

variable {σ R : Type*} [Finite σ] [CommSemiring R] [NoZeroDivisors R]

/-- At a zero `p` of a weighted homogeneous polynomial `f` with `p i ≠ 0` and `(w i : R) ≠ 0`,
the partial derivative `∂ᵢ f` vanishes as soon as every `∂ₖ f` with `k ≠ i` and `w k ≠ 0`
vanishes at `p`. -/
theorem IsWeightedHomogeneous.eval_pderiv_eq_zero_of_eval_eq_zero {w : σ → ℕ} {d : ℕ}
    {f : MvPolynomial σ R} (hf : f.IsWeightedHomogeneous w d) {p : σ → R} (hp : eval p f = 0)
    {i : σ} (hi : p i ≠ 0) (hwi : (w i : R) ≠ 0)
    (h : ∀ k ≠ i, w k ≠ 0 → eval p (pderiv k f) = 0) :
    eval p (pderiv i f) = 0 := by
  have := Fintype.ofFinite σ
  have e := congrArg (eval p) hf.sum_weight_X_mul_pderiv
  simp only [map_sum, map_mul, eval_X, hp, nsmul_eq_mul] at e
  rw [Fintype.sum_eq_single i fun k hk ↦ by
    rcases eq_or_ne (w k) 0 with hwk | hwk
    · simp [hwk]
    · simp [h k hk hwk]] at e
  simpa [hwi, hi] using e

end MvPolynomial

end
