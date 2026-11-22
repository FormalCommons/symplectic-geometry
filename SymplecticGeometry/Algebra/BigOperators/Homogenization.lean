/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Products of homogenized sums

For an element `x` of a commutative semiring and coefficients `aᵢ`, the sum
`∑_{i ≤ m} aᵢ x^{m-i}` is the value at `Y = 1`, `Z = x` of the homogenization `∑ aᵢ Yⁱ Z^{m-i}` in
degree `m` of the polynomial `∑ aᵢ Yⁱ`. Homogenization is multiplicative: if `a` vanishes above `m`
and `b` above `n`, the product of the sums of `a` in degree `m` and of `b` in degree `n` is the
sum, in degree `m + n`, of the Cauchy product `k ↦ ∑_{i ≤ k} aᵢ b_{k-i}`
(`Finset.sum_mul_pow_sub_mul_sum_mul_pow_sub`). For `x = 1` this writes the product of two finite
sums as the sum of their Cauchy product.
-/

public section

namespace Finset

variable {R : Type*} [CommSemiring R]

/-- **Products of homogenized sums.** If `aᵢ = 0` for `i > m` and `bⱼ = 0` for `j > n`, then
`(∑_{i ≤ m} aᵢ x^{m-i}) (∑_{j ≤ n} bⱼ x^{n-j}) = ∑_{k ≤ m+n} (∑_{i ≤ k} aᵢ b_{k-i}) x^{m+n-k}`. -/
theorem sum_mul_pow_sub_mul_sum_mul_pow_sub (x : R) {a b : ℕ → R} {m n : ℕ}
    (ha : ∀ i, m < i → a i = 0) (hb : ∀ j, n < j → b j = 0) :
    (∑ i ∈ range (m + 1), a i * x ^ (m - i)) * (∑ j ∈ range (n + 1), b j * x ^ (n - j)) =
      ∑ k ∈ range (m + n + 1), (∑ i ∈ range (k + 1), a i * b (k - i)) * x ^ (m + n - k) := by
  set g : ℕ → ℕ → R := fun i j ↦ a i * b j * x ^ (m + n - (i + j))
  have hR : ∑ k ∈ range (m + n + 1), (∑ i ∈ range (k + 1), a i * b (k - i)) * x ^ (m + n - k) =
      ∑ i ∈ range (m + n + 1), ∑ j ∈ range (m + n + 1 - i), g i j := by
    rw [← sum_range_diag_flip]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [sum_mul]
    refine sum_congr rfl fun i hi ↦ ?_
    rw [mem_range] at hi
    simp only [g, Nat.add_sub_cancel' (Nat.le_of_lt_succ hi)]
  rw [hR, sum_mul_sum]
  symm
  rw [← sum_subset (range_subset_range.2 (by omega : m + 1 ≤ m + n + 1)) fun i _ hi ↦
    sum_eq_zero fun j _ ↦ by simp [g, ha i (by simpa using hi)]]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [mem_range] at hi
  rw [← sum_subset (range_subset_range.2 (by omega : n + 1 ≤ m + n + 1 - i)) fun j _ hj ↦
    by simp [g, hb j (by simpa using hj)]]
  refine sum_congr rfl fun j hj ↦ ?_
  rw [mem_range] at hj
  have : m + n - (i + j) = m - i + (n - j) := by omega
  simp only [g, this, pow_add]
  ring

end Finset

end
