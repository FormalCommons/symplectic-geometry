/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Comparing powers of large natural numbers

* `Real.eventually_mul_rpow_one_sixth_lt_mul_sqrt`: for every constant `C` and every `ε > 0`,
  `C * k ^ (1 / 6) < ε * √k` for all large natural numbers `k`. It turns a support radius of
  order `k ^ (1 / 6)`, the radius of the cut-off of Donaldson's peak sections, into the radius
  `ε * √k` that bounds on rescaled charts take.

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

end Real

end
