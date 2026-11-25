/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.Algebra.MvPolynomial.Degrees
import TauCeti.RingTheory.MvPolynomial.Finrank

/-!
# Images of polynomial maps lie on hypersurfaces

Let `P = (P₀, …, Pₙ)` be `n + 1` polynomials of total degree at most `d ≥ 1` in `n` variables
over a field `K`. Then there is a nonzero polynomial `Q` in `n + 1` variables, of total degree at
most `(n + 1)! * d ^ n`, with `Q(P₀, …, Pₙ) = 0`
(`SymplecticGeometry.exists_mvPolynomial_ne_zero_aeval_eq_zero`). In particular `Q` vanishes on
the image of the polynomial map `Kⁿ → Kⁿ⁺¹` given by `P`
(`SymplecticGeometry.exists_mvPolynomial_ne_zero_eval_eq_zero`).

The proof is a dimension count. Substitution `Q ↦ Q(P)` maps the polynomials of total degree at
most `D` in `n + 1` variables linearly to those of total degree at most `D * d` in `n` variables
(Tau Ceti's `MvPolynomial.totalDegree_aeval_le`). By Tau Ceti's
`TauCeti.finrank_restrictTotalDegree` these spaces have dimensions `(D + n + 1).choose (n + 1)`
and `(D * d + n).choose n`, and for `D = (n + 1)! * d ^ n` the first is the larger
(Mathlib's `Nat.choose_add_le_add_one_pow` and `Nat.pow_succ_le_ascFactorial`), so the map has
a nonzero kernel. The hypothesis `1 ≤ d` is needed: for `n ≥ 1` and constant `P` the bound
would be `0`, but a nonzero constant `Q` does not vanish at `P`.

This is the algebraic step of Auroux's avoidance estimate [Auroux2000], Proposition 2; the
degree bound is the one that the dimension count gives.

## References

* [D. Auroux, *Symplectic 4-manifolds as branched coverings of ℂℙ²*][Auroux2000]
-/

public section

namespace SymplecticGeometry

open MvPolynomial

variable {K σ ι : Type*} [Field K] [Fintype σ] [Fintype ι]

/-- **Images of polynomial maps lie on hypersurfaces.** Let `P` be a family of `n + 1`
polynomials, indexed by `ι`, of total degree at most `d ≥ 1` in `n` variables, indexed by `σ`,
over a field `K`. Then some nonzero polynomial `Q` in the variables `ι`, of total degree at most
`(n + 1)! * d ^ n`, satisfies `Q(P) = 0`. -/
theorem exists_mvPolynomial_ne_zero_aeval_eq_zero
    (hι : Fintype.card ι = Fintype.card σ + 1) {d : ℕ} (hd : 1 ≤ d)
    (P : ι → MvPolynomial σ K) (hP : ∀ i, (P i).totalDegree ≤ d) :
    ∃ Q : MvPolynomial ι K, Q ≠ 0 ∧
      Q.totalDegree ≤ (Fintype.card σ + 1).factorial * d ^ Fintype.card σ ∧ aeval P Q = 0 := by
  set n := Fintype.card σ
  set D := (n + 1).factorial * d ^ n
  -- The dimension count: `(n + 1)! * (D * d + n).choose n` is at most
  -- `(n + 1)! * ((D + 1) * d) ^ n = D * (D + 1) ^ n`, which is less than
  -- `(D + 1) ^ (n + 1) ≤ (n + 1)! * (D + (n + 1)).choose (n + 1)`.
  have hlt : (D * d + n).choose n < (D + (n + 1)).choose (n + 1) := by
    refine Nat.lt_of_mul_lt_mul_left (a := (n + 1).factorial) ?_
    calc (n + 1).factorial * (D * d + n).choose n
        ≤ (n + 1).factorial * (d ^ n * (D + 1) ^ n) := by
          refine Nat.mul_le_mul_left _ ((Nat.choose_add_le_add_one_pow _ _).trans ?_)
          rw [← mul_pow]
          exact Nat.pow_le_pow_left (by nlinarith) n
      _ = D * (D + 1) ^ n := by ring
      _ < (D + 1) ^ (n + 1) := by
          rw [pow_succ']
          exact Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self D) (by positivity)
      _ ≤ (n + 1).factorial * (D + (n + 1)).choose (n + 1) := by
          rw [← Nat.ascFactorial_eq_factorial_mul_choose]
          exact Nat.pow_succ_le_ascFactorial (D + 1) (n + 1)
  let φ : restrictTotalDegree ι K D →ₗ[K] restrictTotalDegree σ K (D * d) :=
    (aeval P).toLinearMap.restrict fun Q hQ ↦ by
      rw [mem_restrictTotalDegree] at hQ ⊢
      exact (totalDegree_aeval_le Q fun i _ ↦ hP i).trans (Nat.mul_le_mul_right d hQ)
  have hφ : LinearMap.ker φ ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt <| by
    rwa [TauCeti.finrank_restrictTotalDegree, TauCeti.finrank_restrictTotalDegree, hι]
  obtain ⟨⟨Q, hQD⟩, hQ, hQ0⟩ := (Submodule.ne_bot_iff _).1 hφ
  refine ⟨Q, fun h ↦ hQ0 (by simp [h]), (mem_restrictTotalDegree _ _ _).1 hQD, ?_⟩
  simpa [φ, Subtype.ext_iff] using hQ

/-- **Images of polynomial maps lie on hypersurfaces**, pointwise. Let `P` be a family of
`n + 1` polynomials, indexed by `ι`, of total degree at most `d ≥ 1` in `n` variables, indexed by
`σ`, over a field `K`. Then some nonzero polynomial `Q` in the variables `ι`, of total degree at
most `(n + 1)! * d ^ n`, vanishes at `(P i (x))ᵢ` for every point `x : σ → K`, that is, on the
image of the polynomial map `Kⁿ → Kⁿ⁺¹` given by `P`. -/
theorem exists_mvPolynomial_ne_zero_eval_eq_zero
    (hι : Fintype.card ι = Fintype.card σ + 1) {d : ℕ} (hd : 1 ≤ d)
    (P : ι → MvPolynomial σ K) (hP : ∀ i, (P i).totalDegree ≤ d) :
    ∃ Q : MvPolynomial ι K, Q ≠ 0 ∧
      Q.totalDegree ≤ (Fintype.card σ + 1).factorial * d ^ Fintype.card σ ∧
      ∀ x : σ → K, eval (fun i ↦ eval x (P i)) Q = 0 := by
  obtain ⟨Q, hQ0, hQd, hQ⟩ := exists_mvPolynomial_ne_zero_aeval_eq_zero hι hd P hP
  refine ⟨Q, hQ0, hQd, fun x ↦ ?_⟩
  have h : (eval x).comp (algebraMap K (MvPolynomial σ K)) = RingHom.id K := by ext; simp
  simpa [-algebraMap_eq, map_aeval, h] using congrArg (eval x) hQ

end SymplecticGeometry

end
