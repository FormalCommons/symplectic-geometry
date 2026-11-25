/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import TauCeti.RingTheory.MvPolynomial.Jacobian.Basic
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Weighted homogeneous polynomials in blocks of variables

Let `f` be weighted homogeneous for the weights `w`, and let `p` be a zero of `f` with `p i ≠ 0`
and `(w i : R) ≠ 0`. If every partial derivative `∂ₖ f` with `k ≠ i` and `w k ≠ 0` vanishes at
`p`, then so does `∂ᵢ f`
(`MvPolynomial.IsWeightedHomogeneous.eval_pderiv_eq_zero_of_eval_eq_zero`). This follows from
Euler's identity, Mathlib's `MvPolynomial.IsWeightedHomogeneous.sum_weight_X_mul_pderiv`.

For a polynomial in several blocks of homogeneous coordinates, weighting one block by `1` and the
others by `0` shows that, in the affine chart where `p i ≠ 0`, the derivative in the variable `i`
is not needed to decide whether the gradient vanishes at a zero. This is the multi-block analogue
of the single-block statement in Tau Ceti's `forall_eval_pderiv_eq_zero_iff_dehomogenize`.

For a polynomial `f` in two blocks of variables `σ ⊕ τ` that is weighted homogeneous of weight `a`
for the weights `Sum.elim 1 0`, scaling the first block by `c` multiplies the value of `f` by
`c ^ a` (`MvPolynomial.IsWeightedHomogeneous.eval_sumElim_smul_left`); the weights `Sum.elim 0 1`
give the same for the second block (`MvPolynomial.IsWeightedHomogeneous.eval_sumElim_smul_right`).
Both are cases of Tau Ceti's `MvPolynomial.IsWeightedHomogeneous.aeval_pow_mul`.

Two evaluated forms of Euler's identity are also recorded here. The weighted sum
`∑ₖ w k * p k * (∂ₖ f)(p)` is `d * f(p)`
(`MvPolynomial.IsWeightedHomogeneous.sum_weight_mul_eval_pderiv`), and scaling each coordinate
`x k` by `c ^ w k` multiplies `c ^ w i * (∂ᵢ f)` by `c ^ d`
(`MvPolynomial.IsWeightedHomogeneous.aeval_pow_mul_pderiv`), the derivative form of Tau Ceti's
`MvPolynomial.IsWeightedHomogeneous.aeval_pow_mul`. For a family of weighted homogeneous
polynomials, the first says that the Jacobian matrix `TauCeti.jacobiMatrixAt` sends
`fun x ↦ w x * v x` to the values `d k * (p k)(v)` at a point `v`, and so to `0` at a common zero
(`TauCeti.jacobiMatrixAt_mulVec_weight_mul`, `TauCeti.jacobiMatrixAt_mulVec_weight_mul_eq_zero`);
these are the weighted versions of Tau Ceti's `TauCeti.jacobiMatrixAt_mulVec_self` and
`TauCeti.jacobiMatrixAt_mulVec_self_eq_zero`, and follow their proofs.
-/

public section

namespace MvPolynomial

section Euler

variable {σ R : Type*} [CommSemiring R]

/-- **Euler's identity, evaluated.** For `f` weighted homogeneous of degree `d` for the weights
`w`, the sum of `w k * p k * (∂ₖ f)(p)` over the variables is `d * f(p)`. -/
theorem IsWeightedHomogeneous.sum_weight_mul_eval_pderiv [Fintype σ] {w : σ → ℕ} {d : ℕ}
    {f : MvPolynomial σ R} (hf : f.IsWeightedHomogeneous w d) (p : σ → R) :
    ∑ k, (w k : R) * p k * eval p (pderiv k f) = d * eval p f := by
  have e := congrArg (eval p) hf.sum_weight_X_mul_pderiv
  simpa [map_sum, nsmul_eq_mul, mul_assoc] using e

/-- **Scaling a partial derivative of a weighted homogeneous polynomial.** If `f` is weighted
homogeneous of degree `d` for the weights `w`, then multiplying each coordinate `x k` by
`c ^ w k` multiplies the value of `∂ᵢ f`, weighted by `c ^ w i`, by `c ^ d`. -/
theorem IsWeightedHomogeneous.aeval_pow_mul_pderiv {A : Type*} [CommSemiring A] [Algebra R A]
    {w : σ → ℕ} {d : ℕ} {f : MvPolynomial σ R} (hf : f.IsWeightedHomogeneous w d) (c : A)
    (x : σ → A) (i : σ) :
    c ^ w i * aeval (fun k ↦ c ^ w k * x k) (pderiv i f) = c ^ d * aeval x (pderiv i f) := by
  induction hf using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q _ _ ihp ihq => rw [map_add, map_add, map_add, mul_add, mul_add, ihp, ihq]
  | monomial e r he =>
    rw [pderiv_monomial]
    by_cases hi : e i = 0
    · simp [hi]
    · rw [(isWeightedHomogeneous_monomial _ _ _ rfl).aeval_pow_mul, ← mul_assoc, ← pow_add,
        add_comm, Finsupp.weight_sub_single_add hi, he]

end Euler

section PDeriv

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

end PDeriv

section SumElim

variable {σ τ R : Type*} [CommSemiring R] {f : MvPolynomial (σ ⊕ τ) R} {a : ℕ}

/-- If `f` is weighted homogeneous of weight `a` for the weights `Sum.elim 1 0`, that is
homogeneous of degree `a` in the first block of variables, then scaling the first block by `c`
multiplies the value of `f` by `c ^ a`. -/
theorem IsWeightedHomogeneous.eval_sumElim_smul_left
    (hf : f.IsWeightedHomogeneous (Sum.elim 1 0) a) (c : R) (v : σ → R) (w : τ → R) :
    eval (Sum.elim (c • v) w) f = c ^ a * eval (Sum.elim v w) f := by
  have h := hf.aeval_pow_mul (A := R) c (Sum.elim v w)
  rw [aeval_eq_eval, aeval_eq_eval] at h
  convert h using 3
  ext (i | i) <;> simp

/-- If `f` is weighted homogeneous of weight `a` for the weights `Sum.elim 0 1`, that is
homogeneous of degree `a` in the second block of variables, then scaling the second block by `c`
multiplies the value of `f` by `c ^ a`. -/
theorem IsWeightedHomogeneous.eval_sumElim_smul_right
    (hf : f.IsWeightedHomogeneous (Sum.elim 0 1) a) (c : R) (v : σ → R) (w : τ → R) :
    eval (Sum.elim v (c • w)) f = c ^ a * eval (Sum.elim v w) f := by
  have h := hf.aeval_pow_mul (A := R) c (Sum.elim v w)
  rw [aeval_eq_eval, aeval_eq_eval] at h
  convert h using 3
  ext (i | i) <;> simp

end SumElim

end MvPolynomial

namespace TauCeti

open MvPolynomial Matrix

variable {σ ι R : Type*} [CommSemiring R] [Fintype σ]

/-- **Euler's identity for a weighted homogeneous family.** If each `p k` is weighted
homogeneous of degree `d k` for the weights `w`, the Jacobian matrix at `v` sends the vector
`fun x ↦ w x * v x` to the values `d k * p k (v)`. -/
theorem jacobiMatrixAt_mulVec_weight_mul {p : ι → MvPolynomial σ R} {w : σ → ℕ} {d : ι → ℕ}
    (hp : ∀ k, (p k).IsWeightedHomogeneous w (d k)) (v : σ → R) :
    jacobiMatrixAt p v *ᵥ (fun x ↦ (w x : R) * v x) = fun k ↦ (d k : R) * eval v (p k) := by
  ext k
  rw [← (hp k).sum_weight_mul_eval_pderiv v]
  simp only [mulVec, dotProduct, jacobiMatrixAt_apply]
  exact Finset.sum_congr rfl fun x _ ↦ by ring

/-- At a common zero of a weighted homogeneous family, the vector `fun x ↦ w x * v x` lies in
the kernel of the Jacobian matrix. -/
theorem jacobiMatrixAt_mulVec_weight_mul_eq_zero {p : ι → MvPolynomial σ R} {w : σ → ℕ}
    {d : ι → ℕ} (hp : ∀ k, (p k).IsWeightedHomogeneous w (d k)) {v : σ → R}
    (hv : ∀ k, eval v (p k) = 0) :
    jacobiMatrixAt p v *ᵥ (fun x ↦ (w x : R) * v x) = 0 := by
  rw [jacobiMatrixAt_mulVec_weight_mul hp]
  ext k
  simp [hv]

end TauCeti

end
