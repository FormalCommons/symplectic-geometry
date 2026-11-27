/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Comparing powers of large natural numbers

* `Real.eventually_mul_rpow_one_sixth_lt_mul_sqrt`: for every constant `C` and every `ε > 0`,
  `C * k ^ (1 / 6) < ε * √k` for all large natural numbers `k`. It turns a support radius of
  order `k ^ (1 / 6)`, the radius of the cut-off of Donaldson's peak sections, into the radius
  `ε * √k` that bounds on rescaled charts take.
* `Real.eventually_mul_rpow_neg_half_lt`: for every constant `C` and every `ε > 0`,
  `C * k ^ (-1 / 2) < ε` for all large natural numbers `k`, so that an error of order
  `k ^ (-1 / 2)`, such as a bound on rescaled charts, is eventually below any given `ε`.

## References

* [S. K. Donaldson, *Symplectic submanifolds and almost-complex geometry*][Donaldson1996].
-/

public section

namespace Real

/-- For every `C` and every `ε > 0`, `C * k ^ (1 / 6) < ε * √k` for all large natural numbers
`k`. -/
theorem eventually_mul_rpow_one_sixth_lt_mul_sqrt (C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in Filter.atTop, C * (k : ℝ) ^ (1 / 6 : ℝ) < ε * √k := by
  have ht := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
    tendsto_natCast_atTop_atTop).eventually_gt_atTop (C / ε)
  filter_upwards [ht, Filter.eventually_ge_atTop 1] with k hk hk1
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  -- `√k = k ^ (1 / 6) * k ^ (1 / 3)`.
  have hsq : √(k : ℝ) = (k : ℝ) ^ (1 / 6 : ℝ) * (k : ℝ) ^ (1 / 3 : ℝ) := by
    rw [sqrt_eq_rpow, ← rpow_add hk0]
    norm_num
  rw [Function.comp_apply, div_lt_iff₀ hε] at hk
  rw [hsq]
  have h6 : 0 < (k : ℝ) ^ (1 / 6 : ℝ) := rpow_pos_of_pos hk0 _
  nlinarith

/-- For every `C` and every `ε > 0`, `C * k ^ (-1 / 2) < ε` for all large natural numbers `k`. -/
theorem eventually_mul_rpow_neg_half_lt (C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in Filter.atTop, C * (k : ℝ) ^ (-1 / 2 : ℝ) < ε := by
  have h := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
    tendsto_natCast_atTop_atTop).const_mul C
  rw [mul_zero] at h
  have h' : Filter.Tendsto (fun k : ℕ ↦ C * (k : ℝ) ^ (-1 / 2 : ℝ)) Filter.atTop (nhds 0) := by
    convert h using 4
    norm_num
  exact h'.eventually (gt_mem_nhds hε)

end Real

end
