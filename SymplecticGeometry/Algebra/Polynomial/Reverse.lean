/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Algebra.CharP.Basic
import TauCeti.Algebra.Polynomial.Reverse

/-!
# Roots `±1` of self-reciprocal polynomials

A polynomial `p` with `natDegree p ≤ N` is self-reciprocal at `N` when `p.reflect N = p`, that
is, `X ^ N p (1 / X) = p (X)`. Its roots then come in pairs `a`, `a⁻¹` with equal multiplicity
(Tau Ceti's `Polynomial.rootMultiplicity_reflect_eq_inv`). This file treats the two roots that
are their own inverses, `c` with `c * c = 1`:

* `Polynomial.neg_one_pow_rootMultiplicity_mul_pow_eq_one`: over a domain, if `p ≠ 0` and `m` is
  the multiplicity of such a `c`, then `(-1) ^ m c ^ N = 1`;

and so, over a domain whose characteristic is not `2`,

* `Polynomial.even_rootMultiplicity_one_of_reflect_eq`: the multiplicity of `1` is even;
* `Polynomial.even_rootMultiplicity_neg_one_of_reflect_eq`: the multiplicity of `-1` is even
  when `N` is even.

Writing `p = (X - c) ^ m q` with `q (c) ≠ 0` and `c ^ 2 = 1`, reflection turns `(X - c) ^ m` into
`(-c) ^ m (X - c) ^ m`, so `q = (-c) ^ m q.reflect (N - m)`, and evaluating at `c` gives
`(-1) ^ m c ^ N = 1`.

The parity at `±1` of the root multiplicities of a self-reciprocal polynomial is the polynomial
fact behind the parity of the multiplicities of the eigenvalues `±1` of a symplectic matrix
(McDuff–Salamon, Lemma 2.2.2).

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017]
-/

public section

namespace Polynomial

variable {R : Type*} [CommRing R] [IsDomain R]

/-- For a nonzero polynomial `p` with `p.reflect N = p` and a square root `c` of `1`,
`(-1) ^ m c ^ N = 1`, where `m` is the multiplicity of `c` as a root of `p`. -/
theorem neg_one_pow_rootMultiplicity_mul_pow_eq_one {p : R[X]} {N : ℕ} (hp : p ≠ 0)
    (hN : p.natDegree ≤ N) (h : p.reflect N = p) {c : R} (hc : c * c = 1) :
    (-1) ^ p.rootMultiplicity c * c ^ N = 1 := by
  let : Invertible c := ⟨c, hc, hc⟩
  obtain ⟨q, heq, hqroot⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp c
  set m := p.rootMultiplicity c
  have hq : q ≠ 0 := right_ne_zero_of_mul (heq ▸ hp)
  have hdeg : p.natDegree = m + q.natDegree := by
    rw [heq, ((monic_X_sub_C c).pow m).natDegree_mul' hq, (monic_X_sub_C c).natDegree_pow,
      natDegree_X_sub_C, mul_one]
  have hqN : q.natDegree ≤ N - m := by omega
  have hlinear : (X - C c).reflect 1 = C (-c) * (X - C c) := by
    rw [reflect_sub, reflect_one_X, reflect_C, mul_sub, ← C_mul, neg_mul, hc]
    simp only [pow_one, C_neg, C_1]
    ring
  have hpow : ((X - C c) ^ m).reflect m = (C (-c) * (X - C c)) ^ m := by
    rw [← hlinear, ← reflect_pow _ (N := 1) (by simp), Nat.mul_one]
  have hfactor : p.reflect N = (X - C c) ^ m * (C ((-c) ^ m) * q.reflect (N - m)) := by
    conv_lhs => rw [heq, ← Nat.add_sub_of_le (show m ≤ N by omega)]
    rw [reflect_mul _ _ (by simp [(monic_X_sub_C c).natDegree_pow]) hqN, hpow, mul_pow, ← C_pow]
    ring
  -- Cancelling `(X - c) ^ m` from `p.reflect N = p` gives `q = (-c) ^ m q.reflect (N - m)`.
  have hqq : q = C ((-c) ^ m) * q.reflect (N - m) := by
    have := h.symm.trans hfactor
    rw [heq] at this
    exact mul_left_cancel₀ (pow_ne_zero _ (X_sub_C_ne_zero c)) this
  have hqc : q.eval c ≠ 0 := by simpa only [dvd_iff_isRoot, IsRoot.def] using hqroot
  have hrefl : (q.reflect (N - m)).eval c * c ^ (N - m) = q.eval c := by
    simpa only [invOf_eq_right_inv hc, eval₂_id] using
      eval₂_reflect_mul_pow (RingHom.id R) c (N - m) q hqN
  have hcpow : c ^ (N - m) * c ^ (N - m) = 1 := by rw [← mul_pow, hc, one_pow]
  have hkey : q.eval c * ((-1) ^ m * c ^ N) = q.eval c * 1 := by
    have h1 : q.eval c = (-c) ^ m * (q.reflect (N - m)).eval c := by
      conv_lhs => rw [hqq]
      rw [eval_mul, eval_C]
    have h2 : (q.reflect (N - m)).eval c = q.eval c * c ^ (N - m) := by
      rw [← hrefl, mul_assoc, hcpow, mul_one]
    have hN' : c ^ N = c ^ m * c ^ (N - m) := by rw [← pow_add]; congr 1; omega
    calc q.eval c * ((-1) ^ m * c ^ N)
        = (-c) ^ m * (q.eval c * c ^ (N - m)) := by rw [hN', neg_pow]; ring
      _ = q.eval c * 1 := by rw [← h2, ← h1, mul_one]
  exact mul_left_cancel₀ hqc hkey

/-- If `p.reflect N = p` for some `N ≥ natDegree p`, then `1` is a root of `p` of even
multiplicity, over a domain whose characteristic is not `2`. -/
theorem even_rootMultiplicity_one_of_reflect_eq (hR : ringChar R ≠ 2) {p : R[X]} {N : ℕ}
    (hN : p.natDegree ≤ N) (h : p.reflect N = p) : Even (p.rootMultiplicity 1) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  have := neg_one_pow_rootMultiplicity_mul_pow_eq_one hp hN h (mul_one 1)
  rw [one_pow, mul_one] at this
  exact (neg_one_pow_eq_one_iff_even (Ring.neg_one_ne_one_of_char_ne_two hR)).1 this

/-- If `p.reflect N = p` for some even `N ≥ natDegree p`, then `-1` is a root of `p` of even
multiplicity, over a domain whose characteristic is not `2`. -/
theorem even_rootMultiplicity_neg_one_of_reflect_eq (hR : ringChar R ≠ 2) {p : R[X]} {N : ℕ}
    (hN : p.natDegree ≤ N) (hNe : Even N) (h : p.reflect N = p) :
    Even (p.rootMultiplicity (-1)) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  have := neg_one_pow_rootMultiplicity_mul_pow_eq_one hp hN h (by rw [neg_mul_neg, mul_one])
  rw [hNe.neg_one_pow, mul_one] at this
  exact (neg_one_pow_eq_one_iff_even (Ring.neg_one_ne_one_of_char_ne_two hR)).1 this

end Polynomial

end
