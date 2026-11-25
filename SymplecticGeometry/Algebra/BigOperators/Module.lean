/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Module.Defs
import Mathlib.Tactic.Abel

/-!
# Chains of differences weighted by scalars

For vectors `v 0, …, v n` in a module and scalars `t 0, …, t (n - 1)`, this file evaluates the
sum `v 0 + ∑ l ∈ range n, t l • (v (l + 1) - v l)`, which passes from `v l` to `v (l + 1)` as
`t l` goes from `0` to `1`. Where the weights before the `i`-th are `1` and those after it are
`0`, the sum is the two-term interpolation `v i + t i • (v (i + 1) - v i)`; where all weights are
`0` it is `v 0`, and where all are `1` it telescopes to `v n`. Such sums glue sections by cutoffs
in the proof of holonomic approximation, [EliashbergMishachev2002], Chapter 3.

## Main results

* `Finset.add_sum_range_smul_sub_eq_of_lt`: where `t l = 1` for `l < i` and `t l = 0` for
  `i < l < n`, the sum equals `v i + t i • (v (i + 1) - v i)`.
* `Finset.add_sum_range_smul_sub_eq_left`, `Finset.add_sum_range_smul_sub_eq_right`: where all
  `t l` are `0` the sum is `v 0`, and where all are `1` it is `v n`.

## References

* [Y. Eliashberg and N. Mishachev, *Introduction to the h-Principle*][EliashbergMishachev2002]
-/

public section

namespace Finset

variable {R M : Type*} [Semiring R] [AddCommGroup M] [Module R M] {n i : ℕ} {v : ℕ → M}
  {t : ℕ → R}

/-- Where `t l = 1` for every `l < i` and `t l = 0` for every `i < l < n`, with `i < n`, the
sum `v 0 + ∑ l < n, t l • (v (l + 1) - v l)` equals `v i + t i • (v (i + 1) - v i)`. -/
theorem add_sum_range_smul_sub_eq_of_lt (hi : i < n) (h₁ : ∀ l < i, t l = 1)
    (h₀ : ∀ l, i < l → l < n → t l = 0) :
    v 0 + ∑ l ∈ range n, t l • (v (l + 1) - v l) = v i + t i • (v (i + 1) - v i) := by
  rw [← sum_range_add_sum_Ico _ hi.le, sum_congr rfl fun l hl ↦ by
      rw [h₁ l (mem_range.1 hl), one_smul], sum_range_sub,
    sum_eq_single_of_mem i (by simpa using hi) fun l hl hne ↦ by
      rw [h₀ l (lt_of_le_of_ne (mem_Ico.1 hl).1 (Ne.symm hne)) (mem_Ico.1 hl).2, zero_smul]]
  abel

/-- Where `t l = 0` for every `l < n`, the sum `v 0 + ∑ l < n, t l • (v (l + 1) - v l)` equals
`v 0`. -/
theorem add_sum_range_smul_sub_eq_left (h₀ : ∀ l < n, t l = 0) :
    v 0 + ∑ l ∈ range n, t l • (v (l + 1) - v l) = v 0 := by
  rw [sum_eq_zero fun l hl ↦ by rw [h₀ l (mem_range.1 hl), zero_smul], add_zero]

/-- Where `t l = 1` for every `l < n`, the sum `v 0 + ∑ l < n, t l • (v (l + 1) - v l)` equals
`v n`. -/
theorem add_sum_range_smul_sub_eq_right (h₁ : ∀ l < n, t l = 1) :
    v 0 + ∑ l ∈ range n, t l • (v (l + 1) - v l) = v n := by
  rw [sum_congr rfl fun l hl ↦ by rw [h₁ l (mem_range.1 hl), one_smul], sum_range_sub,
    add_sub_cancel]

end Finset

end
