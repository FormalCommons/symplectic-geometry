/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Gaussian bounds under a change of variable

* `Real.one_add_pow_mul_exp_neg_mul_sq_le_of_le_mul`: a bound of the form
  `(1 + t) ^ N * exp (-c * t ^ 2)` gives one of the same form in any `d ≥ 0` comparable to `t`,
  with a smaller exponent `c / b ^ 2` and a constant factor. This is how a Gaussian decay in
  the coordinates of a chart becomes one in a distance comparable to them, as in the decay of
  Donaldson's peak sections.
* `Real.one_add_pow_mul_exp_neg_mul_sq_le_of_le`: for `t ≥ 0`, the weight
  `(1 + t) ^ N * exp (-c * t ^ 2)` grows with `N` and decreases as `c` grows.

## References

* [S. K. Donaldson, *Symplectic submanifolds and almost-complex geometry*][Donaldson1996].
-/

public section

namespace Real

/-- A Gaussian bound in `t` is one in any `d ≥ 0` comparable to `t`: if `t ≤ a * d` and
`d ≤ b * t` with `b > 0`, then for `c ≥ 0`,
`(1 + t) ^ N * exp (-c * t ^ 2) ≤ max a 1 ^ N * (1 + d) ^ N * exp (-(c / b ^ 2) * d ^ 2)`. -/
theorem one_add_pow_mul_exp_neg_mul_sq_le_of_le_mul {t d a b c : ℝ} (N : ℕ) (hd : 0 ≤ d)
    (hb : 0 < b) (hc : 0 ≤ c) (htd : t ≤ a * d) (hdt : d ≤ b * t) :
    (1 + t) ^ N * exp (-c * t ^ 2) ≤
      max a 1 ^ N * (1 + d) ^ N * exp (-(c / b ^ 2) * d ^ 2) := by
  have ht : 0 ≤ t := by nlinarith
  have hpoly : (1 + t) ^ N ≤ (max a 1 * (1 + d)) ^ N :=
    pow_le_pow_left₀ (by linarith)
      (by nlinarith [mul_le_mul_of_nonneg_right (le_max_left a 1) hd, le_max_right a 1]) N
  have hexp : exp (-c * t ^ 2) ≤ exp (-(c / b ^ 2) * d ^ 2) := by
    have h : c / b ^ 2 * d ^ 2 ≤ c * t ^ 2 :=
      calc c / b ^ 2 * d ^ 2 ≤ c / b ^ 2 * (b * t) ^ 2 := by gcongr
        _ = c * t ^ 2 := by field_simp
    exact exp_le_exp.2 (by linarith)
  calc (1 + t) ^ N * exp (-c * t ^ 2) ≤ (max a 1 * (1 + d)) ^ N * exp (-(c / b ^ 2) * d ^ 2) :=
        mul_le_mul hpoly hexp (exp_pos _).le (by positivity)
    _ = max a 1 ^ N * (1 + d) ^ N * exp (-(c / b ^ 2) * d ^ 2) := by rw [mul_pow]

/-- For `t ≥ 0`, the weight `(1 + t) ^ N * exp (-c * t ^ 2)` is monotone in `N` and antitone
in `c`: if `N ≤ N'` and `c' ≤ c`, then
`(1 + t) ^ N * exp (-c * t ^ 2) ≤ (1 + t) ^ N' * exp (-c' * t ^ 2)`. -/
theorem one_add_pow_mul_exp_neg_mul_sq_le_of_le {t c c' : ℝ} {N N' : ℕ} (ht : 0 ≤ t)
    (hN : N ≤ N') (hc : c' ≤ c) :
    (1 + t) ^ N * exp (-c * t ^ 2) ≤ (1 + t) ^ N' * exp (-c' * t ^ 2) := by
  gcongr
  linarith

end Real

end
