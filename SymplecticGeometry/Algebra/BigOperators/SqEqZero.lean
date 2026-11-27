/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Ring

/-!
# Powers of a sum of elements of square zero

In a commutative semiring, if `y i ^ 2 = 0` for every `i ∈ s`, the multinomial expansion of
`(∑ i ∈ s, y i) ^ k` keeps only the squarefree monomials, each `k !` times:
`(∑ i ∈ s, y i) ^ k = k ! • ∑ t ∈ s.powersetCard k, ∏ i ∈ t, y i`
(`Finset.sum_pow_of_sq_eq_zero`). In particular the `card s`-th power is `(card s) ! • ∏ i ∈ s, y i`
and every higher power vanishes.
-/

public section

open Nat

namespace Finset

variable {ι R : Type*} [CommSemiring R]

/-- **The power of a sum of elements of square zero.** If `y i ^ 2 = 0` for `i ∈ s`, then
`(∑ i ∈ s, y i) ^ k` is `k !` times the sum of the products `∏ i ∈ t, y i` over the subsets `t` of
`s` with `k` elements. -/
theorem sum_pow_of_sq_eq_zero {s : Finset ι} {y : ι → R} (hy : ∀ i ∈ s, y i ^ 2 = 0) (k : ℕ) :
    (∑ i ∈ s, y i) ^ k = k ! • ∑ t ∈ s.powersetCard k, ∏ i ∈ t, y i := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty =>
    cases k with
    | zero => simp
    | succ k => rw [powersetCard_eq_empty.2 (by simp)]; simp
  | insert a s ha ih =>
    have hs := ih fun i hi ↦ hy i (mem_insert_of_mem hi)
    have ha2 := hy a (mem_insert_self a s)
    have has {j t} (ht : t ∈ s.powersetCard j) : a ∉ t := fun h ↦ ha ((mem_powersetCard.1 ht).1 h)
    rw [sum_insert ha]
    cases k with
    | zero => simp
    | succ k =>
      -- In `(y a + σ) ^ (k + 1)` only the terms of degree at most one in `y a` survive.
      have hexp : (y a + ∑ i ∈ s, y i) ^ (k + 1) =
          (∑ i ∈ s, y i) ^ (k + 1) + (k + 1) * y a * (∑ i ∈ s, y i) ^ k := by
        rw [add_pow, sum_range_succ', sum_range_succ',
          sum_eq_zero fun j _ ↦ by rw [pow_eq_zero_of_le (by omega) ha2, zero_mul, zero_mul]]
        simp; ring
      -- The subsets of `insert a s` with `k + 1` elements either avoid `a`, or are `insert a t`.
      rw [hexp, hs, hs, powersetCard_succ_insert ha, sum_union, sum_image, nsmul_add]
      · congr 1
        rw [nsmul_eq_mul, nsmul_eq_mul, mul_sum, mul_sum, mul_sum]
        refine sum_congr rfl fun t ht ↦ ?_
        rw [prod_insert (has ht), factorial_succ]
        push_cast; ring
      · intro t ht t' ht' h
        rw [← erase_insert (has ht), h, erase_insert (has ht')]
      · rw [disjoint_left]
        intro t ht ht'
        obtain ⟨u, -, rfl⟩ := mem_image.1 ht'
        exact has ht (mem_insert_self a u)

end Finset

end
