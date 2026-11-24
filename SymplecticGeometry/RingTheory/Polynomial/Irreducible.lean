/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Polynomial.Div

/-!
# Irreducible polynomials with zero constant coefficient

An irreducible polynomial `p` over a nontrivial commutative semiring is associated to `X` exactly
when its constant coefficient vanishes (`Polynomial.associated_X_iff_coeff_zero_eq_zero`): if
`p.coeff 0 = 0` then `X ∣ p`, and since `X` is not a unit, `p` is `X` times a unit.
-/

public section

namespace Polynomial

variable {R : Type*} [CommSemiring R] [Nontrivial R] {p : R[X]}

/-- An irreducible polynomial is associated to `X` if and only if its constant coefficient is
zero. -/
theorem associated_X_iff_coeff_zero_eq_zero (hp : Irreducible p) :
    Associated X p ↔ p.coeff 0 = 0 :=
  ⟨fun h ↦ X_dvd_iff.1 h.dvd,
    fun h ↦ ((hp.dvd_iff.1 (X_dvd_iff.2 h)).resolve_left not_isUnit_X).symm⟩

end Polynomial

end
