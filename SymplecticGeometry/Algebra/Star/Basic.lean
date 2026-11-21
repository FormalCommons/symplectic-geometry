/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Star.Basic

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

open Ring

variable {A : Type*} [Ring A] [StarRing A]

/-- In a star ring, if `a * a = -1`, then `a⋆ a` is the inverse of `a a⋆`. -/
theorem star_mul_self_eq_inverse_of_mul_self_eq_neg_one {a : A} (ha : a * a = -1) :
    star a * a = (a * star a)⁻¹ʳ := by
  let u : Aˣ := ⟨a, -a, by rw [mul_neg, ha, neg_neg], by rw [neg_mul, ha, neg_neg]⟩
  have hinv : a⁻¹ʳ = -a := inverse_unit u
  rw [inverse_mul (.inl u.isUnit), inverse_star, hinv, star_neg, neg_mul_neg]

end
