/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Trunc

/-!
# Truncation of multivariate power series to a total degree

Two facts about Mathlib's `MvPowerSeries.truncTotal`, the truncation of a power series in
finitely many variables to its terms of total degree less than `n`.

* `MvPowerSeries.truncTotal_zero`: the truncation to the terms of total degree less than `0`
  is `0`.
* `MvPowerSeries.truncTotal_eq_sum_monomial`: for a `Fintype` of variables, the truncation is
  the sum of the monomials `p.coeff α • X^α` over the total degrees `k < n` and the exponents
  `α ∈ univ.piAntidiag k` of total degree `k`, written as functions `σ → ℕ`.
-/

public section

open Finset

namespace MvPowerSeries

variable {σ R : Type*} [CommSemiring R]

/-- The truncation of `p` to the terms of total degree less than `0` is `0`. -/
@[simp]
theorem truncTotal_zero [Finite σ] (p : MvPowerSeries σ R) : p.truncTotal 0 = 0 := by
  ext s
  simp [coeff_truncTotal_eq_ite]

/-- The truncation of `p` to the terms of total degree less than `n`, as the sum over `k < n`
of the monomials of `p` whose exponent `α : σ → ℕ` has total degree `k`. -/
theorem truncTotal_eq_sum_monomial [Fintype σ] [DecidableEq σ] (p : MvPowerSeries σ R)
    (n : ℕ) : p.truncTotal n = ∑ k ∈ range n, ∑ α ∈ univ.piAntidiag k,
      MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm α)
        (p.coeff (Finsupp.equivFunOnFinite.symm α)) := by
  ext s
  obtain ⟨a, rfl⟩ := Finsupp.equivFunOnFinite.symm.surjective s
  simp only [coeff_truncTotal_eq_ite, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
    Equiv.apply_eq_iff_eq, Finset.sum_ite_eq', mem_piAntidiag, mem_univ, implies_true, and_true,
    Finsupp.degree_eq_sum, Finsupp.coe_equivFunOnFinite_symm, eq_comm (a := ∑ i, a i), mem_range]

end MvPowerSeries

end
