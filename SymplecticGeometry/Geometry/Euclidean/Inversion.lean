/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.Geometry.Euclidean.Inversion.Basic

/-!
# Inversion of a circle about its centre

Inversion in the circle of centre `c` and radius `R` maps the circle `circleMap c r` of the same
centre to the circle `circleMap c (R ^ 2 / r)`, point by point at the same angle
(`EuclideanGeometry.inversion_circleMap`). The radius `r` may be zero or negative: a circle of
negative radius is traversed from the antipodal point, and so is its image.
-/

public section

namespace EuclideanGeometry

/-- Inversion in the circle of centre `c` and radius `R` maps the point of angle `θ` on the circle
of centre `c` and radius `r` to the point of angle `θ` on the circle of radius `R ^ 2 / r`. -/
theorem inversion_circleMap (c : ℂ) (R r θ : ℝ) :
    inversion c R (circleMap c r θ) = circleMap c (R ^ 2 / r) θ := by
  rcases eq_or_ne r 0 with rfl | -
  · simp
  simp only [inversion, circleMap, dist_eq_norm, vsub_eq_sub, vadd_eq_add, add_sub_cancel_left,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.real_smul, div_pow, sq_abs]
  push_cast
  field_simp
  ring

end EuclideanGeometry

end
