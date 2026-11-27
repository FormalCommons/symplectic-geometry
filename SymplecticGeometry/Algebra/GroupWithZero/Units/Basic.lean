/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Ring.Defs
import SymplecticGeometry.Algebra.Ring.Units

/-!
# The inverse of a square root of `-1`

In a monoid with zero and a distributive negation, an element `a` with `a * a = -1` is a unit
(`isUnit_of_mul_self_eq_neg_one`), so `Ring.inverse a` is its inverse, which is `-a`.

## Main results

* `Ring.inverse_eq_neg_of_mul_self_eq_neg_one`: the inverse `Ring.inverse a` of an element of
  square `-1` is `-a`.
-/

public section

open Ring

variable {M : Type*}

/-- In a monoid with zero and a distributive negation, the inverse of an element of square `-1`
is its negative. -/
theorem Ring.inverse_eq_neg_of_mul_self_eq_neg_one [MonoidWithZero M] [HasDistribNeg M] {a : M}
    (ha : a * a = -1) : a⁻¹ʳ = -a :=
  left_inv_eq_right_inv (inverse_mul_cancel a (SymplecticGeometry.isUnit_of_mul_self_eq_neg_one ha))
    (by rw [mul_neg, ha, neg_neg])

end
