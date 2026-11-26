/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Star.Basic
import SymplecticGeometry.Algebra.GroupWithZero.Units.Basic
import SymplecticGeometry.Algebra.Ring.Units

/-!
# Star rings: elements of square `-1`

In a star ring, an element `a` with `a * a = -1` is a unit with inverse `-a`, and so is its star.
It follows that `a⋆ a` and `a a⋆` are inverse to each other.

## Main results

* `star_mul_self_eq_inverse_of_mul_self_eq_neg_one`: if `a * a = -1`, then
  `a⋆ a = (a a⋆)⁻¹`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Section 2.5.
-/

public section

namespace SymplecticGeometry

open Ring

variable {A : Type*} [Ring A] [StarRing A]

/-- In a star ring, if `a * a = -1`, then `a⋆ a` is the inverse of `a a⋆`. -/
theorem star_mul_self_eq_inverse_of_mul_self_eq_neg_one {a : A} (ha : a * a = -1) :
    star a * a = (a * star a)⁻¹ʳ := by
  rw [inverse_mul (.inl (isUnit_of_mul_self_eq_neg_one ha)), inverse_star,
    inverse_eq_neg_of_mul_self_eq_neg_one ha, star_neg, neg_mul_neg]

end SymplecticGeometry

end
