/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.LinearAlgebra.Projectivization.Veronese

/-!
# The linear form of a homogeneous polynomial in the Veronese monomials

Tau Ceti's `TauCeti.veroneseLinearForm d p` writes a polynomial `p` of degree `d` as a
linear form in the monomials of degree `d`, with the coefficients of `p` at the exponent vectors
`veroneseExponent N d k`. This file shows that this vector of coefficients is nonzero when `p` is
a nonzero homogeneous polynomial of degree `d`:
`MvPolynomial.IsHomogeneous.veroneseLinearForm_coeff_ne_zero`.
-/

public section

open TauCeti

namespace MvPolynomial.IsHomogeneous

variable {N d : ℕ} {R : Type*} [CommSemiring R] {p : MvPolynomial (Fin N) R}

/-- The coefficients of a nonzero homogeneous polynomial `p` of degree `d` at the exponent
vectors of degree `d`, the coefficients of its linear form `veroneseLinearForm d p`, are not all
zero. -/
theorem veroneseLinearForm_coeff_ne_zero (hp : p.IsHomogeneous d) (h0 : p ≠ 0) :
    (fun k ↦ p.coeff (Finsupp.equivFunOnFinite.symm (veroneseExponent N d k))) ≠ 0 := by
  intro h
  obtain ⟨m, hm⟩ := ne_zero_iff.1 h0
  have hdeg : ∑ i, m i = d := by
    rw [← hp hm, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  apply hm
  simpa using congrFun h ((veroneseExponentEquiv N d).symm ⟨m, hdeg⟩)

end MvPolynomial.IsHomogeneous

end
