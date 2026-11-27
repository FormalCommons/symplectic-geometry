/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Real.Sqrt

/-!
# A lower bound for the logarithm near `1`

For `0 < u`, the bound `log (u ^ 2) ≥ 1 - 1 / u ^ 2` (`Real.one_sub_inv_le_log_of_pos`) gives
`log u ≥ (u ^ 2 - 1) / (2 * u ^ 2)` (`Real.sq_sub_one_div_le_log`), and so, for `1 < u`,
`1 / √(log u) ≤ √2 * u / √(u ^ 2 - 1)` (`Real.one_div_sqrt_log_le`). The right side is the
derivative of `√2 * √(u ^ 2 - 1)`, which makes integrals of `1 / √(log u)` from `1` easy to
bound; such integrals define Struwe's shapes.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  §4.6.
-/

public section

namespace Real

/-- For `0 < u`, `log u` is at least `(u ^ 2 - 1) / (2 * u ^ 2)`. -/
theorem sq_sub_one_div_le_log {u : ℝ} (hu : 0 < u) :
    (u ^ 2 - 1) / (2 * u ^ 2) ≤ log u := by
  have hu₂ : 0 < u ^ 2 := pow_pos hu 2
  have h := one_sub_inv_le_log_of_pos hu₂
  rw [log_pow, Nat.cast_ofNat, ← one_div, one_sub_div hu₂.ne', div_le_iff₀ hu₂] at h
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- For `1 < u`, `1 / √(log u) ≤ √2 * u / √(u ^ 2 - 1)`. -/
theorem one_div_sqrt_log_le {u : ℝ} (hu : 1 < u) :
    1 / √(log u) ≤ √2 * u / √(u ^ 2 - 1) := by
  have hu₀ : 0 < u := zero_lt_one.trans hu
  have hL : 0 < log u := log_pos hu
  have h : u ^ 2 - 1 ≤ 2 * u ^ 2 * log u :=
    (div_le_iff₀' (by positivity)).1 (sq_sub_one_div_le_log hu₀)
  have hw : √(u ^ 2 - 1) ≤ √2 * u * √(log u) := by
    calc √(u ^ 2 - 1) ≤ √(2 * u ^ 2 * log u) := sqrt_le_sqrt h
      _ = √2 * u * √(log u) := by
        rw [sqrt_mul (by positivity), sqrt_mul (by positivity), sqrt_sq hu₀.le]
  rw [div_le_div_iff₀ (sqrt_pos.2 hL) (sqrt_pos.2 (by nlinarith))]
  linarith

end Real

end
