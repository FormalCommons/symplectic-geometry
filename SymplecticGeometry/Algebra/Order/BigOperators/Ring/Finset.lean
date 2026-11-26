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

A supplement to `Mathlib.Algebra.Order.BigOperators.Ring.Finset`. A sum `∑ i ∈ s, f i * g i` of
nonnegative terms, in an ordered semiring without zero divisors, vanishes exactly when every
`g i` with `f i ≠ 0` does (`Finset.sum_mul_eq_zero_iff_of_nonneg`). It is stated for a
proposition `p` that each such `g i` detects, and some `f i` nonzero: this is how a function
glued from local functions by a partition of unity, or by bump functions, vanishes exactly where
the local functions do.
-/

public section

namespace Finset

/-- Let `f i, g i ≥ 0` for `i ∈ s`, with some `f i ≠ 0`, and let `g i = 0 ↔ p` whenever
`f i ≠ 0`. Then `∑ i ∈ s, f i * g i = 0 ↔ p`. -/
theorem sum_mul_eq_zero_iff_of_nonneg {ι R : Type*} [Semiring R] [PartialOrder R]
    [IsOrderedRing R] [NoZeroDivisors R] {s : Finset ι} {f g : ι → R} {p : Prop}
    (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i) (hfg : ∀ i ∈ s, f i ≠ 0 → (g i = 0 ↔ p))
    (hs : ∃ i ∈ s, f i ≠ 0) : ∑ i ∈ s, f i * g i = 0 ↔ p := by
  rw [sum_eq_zero_iff_of_nonneg fun i hi ↦ mul_nonneg (hf i hi) (hg i hi)]
  obtain ⟨j, hj, hfj⟩ := hs
  refine ⟨fun h ↦ (hfg j hj hfj).1 ((mul_eq_zero.1 (h j hj)).resolve_left hfj), fun hp i hi ↦ ?_⟩
  by_cases hfi : f i = 0
  · rw [hfi, zero_mul]
  · rw [(hfg i hi hfi).2 hp, mul_zero]

end Finset

end
