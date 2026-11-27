/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.SpecialShape

import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Families of special `i`-convex shapes

The families of `i`-convex shapes (`SymplecticGeometry.IsConvexShapeAt`) of Cieliebak and
Eliashberg's §4.6, which sweep out the neighbourhood of the corner of the surrounding shape.

* `SymplecticGeometry.sub_le_struweShape_two`: Struwe's shape with value `c` at `2 δ` takes at
  `δ` a value at least `c - 3 δ`. This is the bound
  `SymplecticGeometry.integral_one_div_sqrt_log_div_le` with `d = 3` and `K = 2`, for which
  `exp (4 / 9) ≤ 2`.
* `SymplecticGeometry.isConvexShapeAt_struweShape_two`: for `0 < δ` and `4 ≤ d`, Struwe's
  shape with value `2 d δ` at `2 δ` is an `i`-convex shape at every point of `(δ, 2 δ]`. By
  the bound above it is at least `5 δ` there, while `L = log (r / δ) ≤ log 2 < 1`, so that both
  `r √L` and `2 r √L³` are at most `4 δ`, and `SymplecticGeometry.isConvexShapeAt_struweShape_of_lt`
  applies.

Its slope at `2 δ` is `1 / √(log 2)` (`SymplecticGeometry.deriv_struweShape_mul`), and its slope
tends to `+∞` at `δ` (`SymplecticGeometry.tendsto_deriv_struweShape`).

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  §4.6: Lemma 4.23.
-/

public section

namespace SymplecticGeometry

open Real Set

variable {δ : ℝ}

/-- Struwe's shape with value `c` at `2 δ` takes at `δ` a value at least `c - 3 δ`. -/
theorem sub_le_struweShape_two (hδ : 0 < δ) (c : ℝ) : c - 3 * δ ≤ struweShape δ 2 c δ := by
  have hexp : exp (4 / 3 ^ 2) ≤ 2 := by
    rw [← le_log_iff_exp_le two_pos]
    linarith [log_two_gt_d9]
  have h := integral_one_div_sqrt_log_div_le (by norm_num : (0 : ℝ) < 3) hδ hexp
  rw [struweShape_def, intervalIntegral.integral_symm]
  linarith

/-- **Struwe's shape on `(δ, 2 δ]`** (Cieliebak–Eliashberg, Lemma 4.23). For `0 < δ` and
`4 ≤ d`, Struwe's shape with value `2 d δ` at `2 δ` is an `i`-convex shape at every point of
`(δ, 2 δ]`. -/
theorem isConvexShapeAt_struweShape_two {d r : ℝ} (hδ : 0 < δ) (hd : 4 ≤ d)
    (hr : r ∈ Ioc δ (2 * δ)) : IsConvexShapeAt (struweShape δ 2 (2 * d * δ)) r := by
  have hr₀ : 0 < r := hδ.trans hr.1
  have hχ : 5 * δ < struweShape δ 2 (2 * d * δ) r := by
    have := sub_le_struweShape_two hδ (2 * d * δ)
    have := strictMonoOn_struweShape hδ one_le_two (2 * d * δ) (mem_Ici.2 le_rfl)
      (mem_Ici.2 hr.1.le) hr.1
    nlinarith
  have ht₀ : 0 ≤ √(log (r / δ)) := sqrt_nonneg _
  have ht : √(log (r / δ)) ≤ 1 := by
    refine sqrt_le_one.2 ((log_le_log (div_pos hr₀ hδ) ((div_le_iff₀ hδ).2 hr.2)).trans ?_)
    linarith [log_two_lt_d9]
  refine isConvexShapeAt_struweShape_of_lt hδ one_le_two hr.1 ?_ ?_
  · nlinarith [mul_le_mul hr.2 ht ht₀ (by positivity)]
  · nlinarith [mul_le_mul hr.2 (pow_le_one₀ (n := 3) ht₀ ht) (by positivity) (by positivity)]

end SymplecticGeometry

end
