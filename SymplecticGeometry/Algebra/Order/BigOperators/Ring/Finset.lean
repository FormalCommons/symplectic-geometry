/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Defs

/-!
# Zero sums of products of nonnegative terms

A supplement to `Mathlib.Algebra.Order.BigOperators.Ring.Finset`, in an ordered semiring without
zero divisors:

* `Finset.sum_mul_eq_zero_iff_of_nonneg`: a sum `∑ i ∈ s, f i * g i` with `f i, g i ≥ 0`
  vanishes exactly when `f i = 0` or `g i = 0` for each `i ∈ s`.
* `Finset.sum_mul_eq_zero_iff_of_forall_ne_zero`: if moreover some `f i` is nonzero, and each
  `g i` with `f i ≠ 0` vanishes exactly when a proposition `p` holds, then the sum vanishes
  exactly when `p` holds. This is how a function glued from local functions by a partition of
  unity, or by bump functions, vanishes exactly where the local functions do.
-/

public section

namespace Finset

variable {ι R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R]
  {s : Finset ι} {f g : ι → R}

/-- If `f i, g i ≥ 0` for `i ∈ s`, then `∑ i ∈ s, f i * g i = 0` if and only if `f i = 0` or
`g i = 0` for every `i ∈ s`. -/
theorem sum_mul_eq_zero_iff_of_nonneg (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i) :
    ∑ i ∈ s, f i * g i = 0 ↔ ∀ i ∈ s, f i = 0 ∨ g i = 0 := by
  simp [sum_eq_zero_iff_of_nonneg fun i hi ↦ mul_nonneg (hf i hi) (hg i hi)]

/-- Let `f i, g i ≥ 0` for `i ∈ s`, with some `f i ≠ 0`, and let `g i = 0 ↔ p` whenever
`f i ≠ 0`. Then `∑ i ∈ s, f i * g i = 0 ↔ p`. -/
theorem sum_mul_eq_zero_iff_of_forall_ne_zero {p : Prop} (hf : ∀ i ∈ s, 0 ≤ f i)
    (hg : ∀ i ∈ s, 0 ≤ g i) (hfg : ∀ i ∈ s, f i ≠ 0 → (g i = 0 ↔ p))
    (hs : ∃ i ∈ s, f i ≠ 0) : ∑ i ∈ s, f i * g i = 0 ↔ p := by
  rw [sum_mul_eq_zero_iff_of_nonneg hf hg]
  obtain ⟨j, hj, hfj⟩ := hs
  refine ⟨fun h ↦ (hfg j hj hfj).1 ((h j hj).resolve_left hfj), fun hp i hi ↦ ?_⟩
  exact or_iff_not_imp_left.2 fun hfi ↦ (hfg i hi hfi).2 hp

end Finset

end
