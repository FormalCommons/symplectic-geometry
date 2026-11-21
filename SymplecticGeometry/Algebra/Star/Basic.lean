/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Tactic.NoncommRing

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
  have hu : IsUnit a := ⟨⟨a, -a, by rw [mul_neg, ha, neg_neg], by rw [neg_mul, ha, neg_neg]⟩, rfl⟩
  have hmul : a * star a * (star a * a) = 1 := by
    have hs : star a * star a = -1 := by rw [← star_mul, ha, star_neg, star_one]
    calc a * star a * (star a * a) = a * (star a * star a) * a := by noncomm_ring
      _ = 1 := by rw [hs, mul_neg_one, neg_mul, ha, neg_neg]
  simpa using ((inverse_mul_eq_iff_eq_mul _ 1 _ (hu.mul hu.star)).2 hmul.symm).symm

end
