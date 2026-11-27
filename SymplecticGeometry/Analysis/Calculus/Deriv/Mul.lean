/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Convex combinations of functions

* `deriv_mul_add_one_sub_mul_pos`: a combination `c * f + (1 - c) * g` with `c ∈ [0, 1]` of two
  real functions with positive derivative at `x` has positive derivative at `x`. The derivative
  is computed by Mathlib's `deriv_const_mul`; the differentiability of `f` and `g` at `x` follows
  from their derivatives being nonzero (`differentiableAt_of_deriv_ne_zero`).
* `iteratedDeriv_mul_add_one_sub_mul_sub_iteratedDeriv`: the `n`-th derivative of a blend
  `ρ * f + (1 - ρ) * g` differs from that of `g` by `∑ i ≤ n, (n choose i) ρ⁽ⁱ⁾ (f - g)⁽ⁿ⁻ⁱ⁾`,
  since the blend is `g + ρ * (f - g)`; this is Mathlib's Leibniz rule `iteratedDeriv_mul`.
-/

public section

/-- A combination `c * f + (1 - c) * g`, with `0 ≤ c ≤ 1`, of two real functions with positive
derivatives at `x` has positive derivative at `x`. -/
theorem deriv_mul_add_one_sub_mul_pos {f g : ℝ → ℝ} {x c : ℝ} (hf : 0 < deriv f x)
    (hg : 0 < deriv g x) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) :
    0 < deriv (fun y ↦ c * f y + (1 - c) * g y) x := by
  have hfd := differentiableAt_of_deriv_ne_zero hf.ne'
  have hgd := differentiableAt_of_deriv_ne_zero hg.ne'
  rw [deriv_fun_add (hfd.const_mul c) (hgd.const_mul (1 - c)), deriv_const_mul _ hfd,
    deriv_const_mul _ hgd]
  rcases hc₀.eq_or_lt with rfl | hc₀
  · simpa using hg
  · nlinarith

/-- The `n`-th derivative of the blend `ρ * f + (1 - ρ) * g` of `f` and `g` by `ρ`, minus that of
`g`, is `∑ i ≤ n, (n choose i) ρ⁽ⁱ⁾ (f⁽ⁿ⁻ⁱ⁾ - g⁽ⁿ⁻ⁱ⁾)`, for `ρ`, `f` and `g` that are `Cⁿ` at
`x`. -/
theorem iteratedDeriv_mul_add_one_sub_mul_sub_iteratedDeriv {𝕜 𝔸 : Type*}
    [NontriviallyNormedField 𝕜] [NormedRing 𝔸] [NormedAlgebra 𝕜 𝔸] {n : ℕ} {ρ f g : 𝕜 → 𝔸}
    {x : 𝕜} (hρ : ContDiffAt 𝕜 n ρ x) (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) :
    iteratedDeriv n (fun y ↦ ρ y * f y + (1 - ρ y) * g y) x - iteratedDeriv n g x =
      ∑ i ∈ Finset.range (n + 1), n.choose i * iteratedDeriv i ρ x *
        (iteratedDeriv (n - i) f x - iteratedDeriv (n - i) g x) := by
  have hblend : (fun y ↦ ρ y * f y + (1 - ρ y) * g y) = g + ρ * (f - g) := by
    ext y
    simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, sub_mul, one_mul, mul_sub]
    abel
  have hfg : ContDiffAt 𝕜 n (f - g) x := hf.sub hg
  have hm : ContDiffAt 𝕜 n (ρ * (f - g)) x := hρ.mul hfg
  rw [hblend, iteratedDeriv_add hg hm, add_sub_cancel_left, iteratedDeriv_mul hρ hfg]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hi : ((n - i : ℕ) : WithTop ℕ∞) ≤ n := by exact_mod_cast Nat.sub_le n i
  rw [iteratedDeriv_sub (hf.of_le hi) (hg.of_le hi)]

end
