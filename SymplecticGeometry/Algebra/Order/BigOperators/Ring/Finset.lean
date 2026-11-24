/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The sign of a finite product

In a linearly ordered commutative ring, a finite product is its absolute value times `-1` raised to
the number of negative factors.

## Main results

* `Finset.prod_eq_neg_one_pow_mul_abs_prod`:
  `∏ i ∈ s, f i = (-1) ^ #{i ∈ s | f i < 0} * |∏ i ∈ s, f i|`.
* `Finset.prod_eq_prod_of_abs_eq`: two finite products with the same absolute value and the same
  number of negative factors are equal.
-/

public section

namespace Finset

variable {ι κ R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- A finite product is `-1` raised to the number of negative factors, times its absolute value. -/
theorem prod_eq_neg_one_pow_mul_abs_prod (s : Finset ι) (f : ι → R) :
    ∏ i ∈ s, f i = (-1) ^ #{i ∈ s | f i < 0} * |∏ i ∈ s, f i| := by
  have h (i : ι) : f i = (if f i < 0 then -1 else 1) * |f i| := by
    split_ifs with hi
    · rw [abs_of_neg hi, neg_one_mul, neg_neg]
    · rw [abs_of_nonneg (not_lt.1 hi), one_mul]
  conv_lhs => rw [prod_congr rfl fun i _ ↦ h i]
  rw [prod_mul_distrib, prod_ite, prod_const_one, mul_one, prod_const, abs_prod]

/-- Two finite products with the same absolute value and the same number of negative factors are
equal. -/
theorem prod_eq_prod_of_abs_eq {s : Finset ι} {t : Finset κ} {f : ι → R} {g : κ → R}
    (habs : |∏ i ∈ s, f i| = |∏ i ∈ t, g i|) (hneg : #{i ∈ s | f i < 0} = #{i ∈ t | g i < 0}) :
    ∏ i ∈ s, f i = ∏ i ∈ t, g i := by
  rw [prod_eq_neg_one_pow_mul_abs_prod, prod_eq_neg_one_pow_mul_abs_prod t, habs, hneg]

end Finset

end
