/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

import Mathlib.Data.Nat.Choose.Sum

/-!
# Bounds on the iterated derivatives of a product, and blends of increasing functions

* `norm_iteratedDeriv_mul_le_of_forall_norm_le`: if the first `n` derivatives of `f` at `x` are
  bounded by `B` and those of `g` by `τ`, then the `n`-th derivative of `f * g` at `x` is
  bounded by `2 ^ n * B * τ`. It follows from Mathlib's Leibniz rule `iteratedDeriv_mul` and
  `Nat.sum_range_choose`. With `f` a fixed cutoff and `g` a small difference, it says that the
  cutoff times the difference is small with it.
* `deriv_mul_add_one_sub_mul_pos`: a combination `c * f + (1 - c) * g` with `c ∈ [0, 1]` of two
  functions with positive derivative at `x` has positive derivative at `x`.
-/

public section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕜 𝔸]
  {n : ℕ} {x : 𝕜} {f g : 𝕜 → 𝔸}

/-- **Leibniz bound.** If `f` and `g` are `Cⁿ` at `x`, the iterated derivatives of `f` of order
at most `n` at `x` have norm at most `B`, and those of `g` have norm at most `τ`, then the `n`-th
iterated derivative of `f * g` at `x` has norm at most `2 ^ n * B * τ`. -/
theorem norm_iteratedDeriv_mul_le_of_forall_norm_le (hf : ContDiffAt 𝕜 n f x)
    (hg : ContDiffAt 𝕜 n g x) {B τ : ℝ} (hB : ∀ i ≤ n, ‖iteratedDeriv i f x‖ ≤ B)
    (hτ : ∀ i ≤ n, ‖iteratedDeriv i g x‖ ≤ τ) :
    ‖iteratedDeriv n (f * g) x‖ ≤ 2 ^ n * B * τ := by
  have h2 : (2 : ℝ) ^ n = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) := by
    exact_mod_cast (Nat.sum_range_choose n).symm
  rw [iteratedDeriv_mul hf hg, h2, Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi ↦ ?_)
  have hi : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  rw [mul_assoc, ← nsmul_eq_mul, mul_assoc]
  refine norm_nsmul_le.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  exact (norm_mul_le _ _).trans
    (mul_le_mul (hB i hi) (hτ _ (n.sub_le i)) (norm_nonneg _) ((norm_nonneg _).trans (hB i hi)))

/-- A combination `c * f + (1 - c) * g`, with `0 ≤ c ≤ 1`, of two real functions that are
differentiable at `x` with positive derivatives there has positive derivative at `x`. -/
theorem deriv_mul_add_one_sub_mul_pos {f g : ℝ → ℝ} {x c : ℝ} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (hf' : 0 < deriv f x) (hg' : 0 < deriv g x) (hc₀ : 0 ≤ c)
    (hc₁ : c ≤ 1) : 0 < deriv (fun y ↦ c * f y + (1 - c) * g y) x := by
  rw [deriv_fun_add (hf.const_mul c) (hg.const_mul (1 - c)), deriv_const_mul _ hf,
    deriv_const_mul _ hg]
  rcases hc₀.eq_or_lt with rfl | hc₀
  · simpa using hg'
  · nlinarith

end
