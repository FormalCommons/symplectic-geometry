/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Ring.Defs

/-!
# Square roots of `-1` are units

In a monoid with a distributive negation, an element `a` with `a * a = -1` is a unit whose
inverse is `-a`, because `a * -a = -(a * a) = 1`, and likewise `-a * a = 1`.

## Main results

* `isUnit_of_mul_self_eq_neg_one`: an element of square `-1` is a unit.
* `Ring.inverse_eq_neg_of_mul_self_eq_neg_one`: its inverse `Ring.inverse a` is `-a`.
-/

public section

open Ring

variable {M : Type*}

/-- In a monoid with a distributive negation, an element of square `-1` is a unit. -/
theorem isUnit_of_mul_self_eq_neg_one [Monoid M] [HasDistribNeg M] {a : M} (ha : a * a = -1) :
    IsUnit a :=
  isUnit_iff_exists.2 ⟨-a, by rw [mul_neg, ha, neg_neg], by rw [neg_mul, ha, neg_neg]⟩

/-- In a monoid with zero and a distributive negation, the inverse of an element of square `-1`
is its negative. -/
theorem Ring.inverse_eq_neg_of_mul_self_eq_neg_one [MonoidWithZero M] [HasDistribNeg M] {a : M}
    (ha : a * a = -1) : a⁻¹ʳ = -a :=
  left_inv_eq_right_inv (inverse_mul_cancel a (isUnit_of_mul_self_eq_neg_one ha))
    (by rw [mul_neg, ha, neg_neg])

end
