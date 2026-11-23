/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Data.Nat.Cast.Defs

/-!
# Counting even numbers in a range by a sum

The indicator of the even numbers, summed over `0, 1, …, 2m`, is `m + 1`:
`Finset.sum_range_two_mul_add_one_ite_even`. This counts the even degrees of a space whose
homology is that of `ℂℙᵐ`, as in Euler characteristic computations.

The proof, by induction on `m`, is that of the local step `hEven` in Tau Ceti's
`ComplexProjectiveSpace.cwEulerChar_cwComplex`, over any additive commutative monoid with one
rather than `ℤ`.
-/

public section

namespace Finset

/-- The number of even `i` with `0 ≤ i ≤ 2m`, written as a sum of indicators, is `m + 1`. -/
theorem sum_range_two_mul_add_one_ite_even {R : Type*} [AddCommMonoidWithOne R] (m : ℕ) :
    ∑ i ∈ range (2 * m + 1), (if Even i then 1 else 0 : R) = m + 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 by omega, sum_range_succ, sum_range_succ, ih]
    simp [parity_simps, add_assoc]

end Finset

end
