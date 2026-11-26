/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Double sums over ordered pairs

Over a linearly ordered index set, a double sum `∑ i ∈ s, ∑ j ∈ s, h i j` whose terms vanish on
the diagonal is the sum over the pairs `i < j` of `h i j + h j i`. This is how a sum over all
pairs of indices of an antisymmetric expression, such as the coordinate expansion of a two-form,
becomes a sum over the increasing pairs.

## Main results

* `Finset.sum_sum_eq_sum_sum_lt_add_swap`: the double sum of `h` is the sum over the pairs
  `i < j` of `h i j + h j i`, when `h i i = 0` for every `i`.
-/

public section

namespace Finset

variable {ι M : Type*} [LinearOrder ι] [AddCommMonoid M]

/-- A double sum whose terms vanish on the diagonal is the sum over the increasing pairs `i < j`
of `h i j + h j i`. -/
theorem sum_sum_eq_sum_sum_lt_add_swap (s : Finset ι) (h : ι → ι → M) (hh : ∀ i, h i i = 0) :
    ∑ i ∈ s, ∑ j ∈ s, h i j = ∑ i ∈ s, ∑ j ∈ s with i < j, (h i j + h j i) := by
  have hsplit : ∀ i j, h i j = (if i < j then h i j else 0) + (if j < i then h i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · simp [hij, hij.not_gt]
    · simp [hh]
    · simp [hij, hij.not_gt]
  calc ∑ i ∈ s, ∑ j ∈ s, h i j
      = ∑ i ∈ s, ∑ j ∈ s, ((if i < j then h i j else 0) + (if j < i then h i j else 0)) :=
        sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ hsplit i j
    _ = ∑ i ∈ s, ∑ j ∈ s, ((if i < j then h i j else 0) + (if i < j then h j i else 0)) := by
        simp_rw [sum_add_distrib]
        rw [sum_comm (f := fun i j ↦ if j < i then h i j else 0)]
    _ = ∑ i ∈ s, ∑ j ∈ s with i < j, (h i j + h j i) := by
        simp_rw [sum_filter]
        refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
        split_ifs <;> simp

end Finset

end
