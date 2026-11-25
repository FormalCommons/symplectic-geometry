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
import SymplecticGeometry.Data.Matrix.Mul

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

The second says how the Jacobian matrix changes when each coordinate `v x` of the point is
multiplied by `c ^ w x`: its rows and columns are scaled by powers of `c`
(`TauCeti.jacobiMatrixAt_weight_smul_mul`), so for `c ≠ 0` it stays surjective
(`TauCeti.mulVec_surjective_jacobiMatrixAt_weight_smul_iff`, by
`Matrix.mulVec_surjective_iff_of_mul_eq_mul`). For a family in two blocks of
variables, homogeneous in each block, applying these once for each block scales the two blocks
separately (`TauCeti.jacobiMatrixAt_sumElim_smul_mul`,
`TauCeti.mulVec_surjective_jacobiMatrixAt_sumElim_smul_iff`), so surjectivity depends only on
the pair of projective points (`TauCeti.mulVec_surjective_jacobiMatrixAt_sumElim_iff_of_mk_eq_mk`).
These follow the proof of Tau Ceti's `TauCeti.mulVec_surjective_jacobiMatrixAt_iff_of_mk_eq_mk`.
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
  have e := hf.sum_weight_mul_eval_pderiv p
  rw [hp, mul_zero] at e
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

namespace TauCeti

open MvPolynomial Matrix

section Scaling

variable {σ τ ι R : Type*} [CommSemiring R]

/-- How the Jacobian matrix of a weighted homogeneous family changes when each coordinate `v x`
of the point is multiplied by `c ^ w x`: the entry in row `k` and column `x`, multiplied by
`c ^ w x`, is `c ^ d k` times the entry at the unscaled point. -/
theorem jacobiMatrixAt_weight_smul_mul {p : ι → MvPolynomial σ R} {w : σ → ℕ} {d : ι → ℕ}
    (hp : ∀ k, (p k).IsWeightedHomogeneous w (d k)) (c : R) (v : σ → R) (k : ι) (x : σ) :
    c ^ w x * jacobiMatrixAt p (fun y ↦ c ^ w y * v y) k x = c ^ d k * jacobiMatrixAt p v k x := by
  simpa [aeval_eq_eval] using (hp k).aeval_pow_mul_pderiv c v x

/-- How the Jacobian matrix of a family in two blocks of variables, of degree `d₁ k` in the first
block and `d₂ k` in the second, changes when the two blocks of the point are scaled by `s` and
`t`: the entry in row `k` and column `x`, multiplied by `s` if `x` lies in the first block and by
`t` if it lies in the second, is `s ^ d₁ k * t ^ d₂ k` times the entry at the unscaled point. -/
theorem jacobiMatrixAt_sumElim_smul_mul {p : ι → MvPolynomial (σ ⊕ τ) R} {d₁ d₂ : ι → ℕ}
    (hp₁ : ∀ k, (p k).IsWeightedHomogeneous (Sum.elim 1 0) (d₁ k))
    (hp₂ : ∀ k, (p k).IsWeightedHomogeneous (Sum.elim 0 1) (d₂ k)) (s t : R)
    (v : σ → R) (w : τ → R) (k : ι) (x : σ ⊕ τ) :
    s ^ (Sum.elim 1 0 x : ℕ) * t ^ (Sum.elim 0 1 x : ℕ) *
        jacobiMatrixAt p (Sum.elim (s • v) (t • w)) k x =
      s ^ d₁ k * t ^ d₂ k * jacobiMatrixAt p (Sum.elim v w) k x := by
  have hz : Sum.elim (s • v) (t • w) = fun y ↦
      s ^ (Sum.elim 1 0 y : ℕ) * (t ^ (Sum.elim 0 1 y : ℕ) * Sum.elim v w y) := by
    ext (c | c) <;> simp
  rw [hz, mul_comm (s ^ _), mul_assoc, jacobiMatrixAt_weight_smul_mul hp₁, mul_left_comm,
    jacobiMatrixAt_weight_smul_mul hp₂]
  ring

end Scaling

section Field

variable {σ τ ι K : Type*} [Field K] [Fintype σ]

/-- Multiplying each coordinate `v x` of the point by `c ^ w x`, for a nonzero `c`, does not
change whether the Jacobian matrix of a weighted homogeneous family is surjective. -/
theorem mulVec_surjective_jacobiMatrixAt_weight_smul_iff {p : ι → MvPolynomial σ K}
    {w : σ → ℕ} {d : ι → ℕ} (hp : ∀ k, (p k).IsWeightedHomogeneous w (d k)) {c : K} (hc : c ≠ 0)
    (v : σ → K) :
    (jacobiMatrixAt p (fun y ↦ c ^ w y * v y)).mulVec.Surjective ↔
      (jacobiMatrixAt p v).mulVec.Surjective := by
  -- Scaling the point scales row `k` by `c ^ d k` and column `x` by `c ^ w x`, all nonzero.
  have hc := isUnit_iff_ne_zero.mpr hc
  exact mulVec_surjective_iff_of_mul_eq_mul (Pi.isUnit_iff.mpr fun _ ↦ hc.pow _)
    (Pi.isUnit_iff.mpr fun _ ↦ hc.pow _) fun k x ↦ by
    rw [mul_comm]
    exact jacobiMatrixAt_weight_smul_mul hp c v k x

variable [Fintype τ]

/-- Scaling the two blocks of the point by nonzero scalars does not change whether the Jacobian
matrix of a family in two blocks of variables, homogeneous in each block, is surjective. -/
theorem mulVec_surjective_jacobiMatrixAt_sumElim_smul_iff {p : ι → MvPolynomial (σ ⊕ τ) K}
    {d₁ d₂ : ι → ℕ} (hp₁ : ∀ k, (p k).IsWeightedHomogeneous (Sum.elim 1 0) (d₁ k))
    (hp₂ : ∀ k, (p k).IsWeightedHomogeneous (Sum.elim 0 1) (d₂ k)) {s t : K} (hs : s ≠ 0)
    (ht : t ≠ 0) (v : σ → K) (w : τ → K) :
    (jacobiMatrixAt p (Sum.elim (s • v) (t • w))).mulVec.Surjective ↔
      (jacobiMatrixAt p (Sum.elim v w)).mulVec.Surjective := by
  have hz : Sum.elim (s • v) (t • w) = fun y ↦
      s ^ (Sum.elim 1 0 y : ℕ) * (fun y ↦ t ^ (Sum.elim 0 1 y : ℕ) * Sum.elim v w y) y := by
    ext (c | c) <;> simp
  rw [hz, mulVec_surjective_jacobiMatrixAt_weight_smul_iff hp₁ hs,
    mulVec_surjective_jacobiMatrixAt_weight_smul_iff hp₂ ht]

/-- Whether the Jacobian matrix of a family in two blocks of variables, homogeneous in each
block, is surjective at a pair of nonzero vectors depends only on the pair of projective points
they represent. -/
theorem mulVec_surjective_jacobiMatrixAt_sumElim_iff_of_mk_eq_mk
    {p : ι → MvPolynomial (σ ⊕ τ) K} {d₁ d₂ : ι → ℕ}
    (hp₁ : ∀ k, (p k).IsWeightedHomogeneous (Sum.elim 1 0) (d₁ k))
    (hp₂ : ∀ k, (p k).IsWeightedHomogeneous (Sum.elim 0 1) (d₂ k))
    {v v' : σ → K} {w w' : τ → K} (hv : v ≠ 0) (hv' : v' ≠ 0) (hw : w ≠ 0) (hw' : w' ≠ 0)
    (h₁ : Projectivization.mk K v hv = Projectivization.mk K v' hv')
    (h₂ : Projectivization.mk K w hw = Projectivization.mk K w' hw') :
    (jacobiMatrixAt p (Sum.elim v w)).mulVec.Surjective ↔
      (jacobiMatrixAt p (Sum.elim v' w')).mulVec.Surjective := by
  obtain ⟨s, rfl⟩ := (Projectivization.mk_eq_mk_iff' K v v' hv hv').mp h₁
  obtain ⟨t, rfl⟩ := (Projectivization.mk_eq_mk_iff' K w w' hw hw').mp h₂
  exact mulVec_surjective_jacobiMatrixAt_sumElim_smul_iff hp₁ hp₂ (left_ne_zero_of_smul hv)
    (left_ne_zero_of_smul hw) v' w'

end Field

end TauCeti

end
