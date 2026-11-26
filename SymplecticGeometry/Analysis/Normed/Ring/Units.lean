/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Units of a complete normed algebra on a segment

In a complete normed algebra `R` over a normed field `𝕜`, let `a` be a unit and `b` an element
with `‖a⁻¹ b - 1‖ < 1`. Then every point `(1 - s) a + s b` of the segment from `a` to `b`, for a
scalar `‖s‖ ≤ 1`, is a unit (`Units.isUnit_one_sub_smul_add_smul_of_norm_lt_one`): it is
`a (1 - s (1 - a⁻¹ b))`, and the second factor is a unit by the Neumann series, Mathlib's
`isUnit_one_sub_of_norm_lt_one`.

## References

* [A. Hatcher, *Vector Bundles and K-Theory*][Hatcher2017], §2.1 (nearby clutching functions are
  homotopic).
-/

public section

namespace Units

variable {𝕜 R : Type*} [NormedField 𝕜] [NormedRing R] [NormedAlgebra 𝕜 R] [CompleteSpace R]

/-- If `a` is a unit of a complete normed algebra and `‖a⁻¹ b - 1‖ < 1`, then `(1 - s) a + s b`
is a unit for every scalar `s` with `‖s‖ ≤ 1`. -/
theorem isUnit_one_sub_smul_add_smul_of_norm_lt_one (a : Rˣ) {b : R}
    (h : ‖(↑a⁻¹ : R) * b - 1‖ < 1) {s : 𝕜} (hs : ‖s‖ ≤ 1) :
    IsUnit ((1 - s) • (a : R) + s • b) := by
  have hu : ‖s • (1 - (↑a⁻¹ : R) * b)‖ < 1 :=
    calc ‖s • (1 - (↑a⁻¹ : R) * b)‖ ≤ ‖s‖ * ‖(↑a⁻¹ : R) * b - 1‖ := by
          rw [← norm_sub_rev]; exact norm_smul_le _ _
      _ ≤ 1 * ‖(↑a⁻¹ : R) * b - 1‖ := mul_le_mul_of_nonneg_right hs (norm_nonneg _)
      _ < 1 := by rwa [one_mul]
  have hfac : (1 - s) • (a : R) + s • b = a * (1 - s • (1 - (↑a⁻¹ : R) * b)) := by
    simp [mul_sub, sub_smul, smul_sub]
    abel
  rw [hfac]
  exact a.isUnit.mul (isUnit_one_sub_of_norm_lt_one hu)

end Units

end
