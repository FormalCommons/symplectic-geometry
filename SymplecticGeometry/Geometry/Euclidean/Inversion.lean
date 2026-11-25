/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.Geometry.Euclidean.Inversion.Basic
public import TauCeti.Geometry.Euclidean.Inversion

/-!
# Inversion of a circle about its centre, and the regions it exchanges

Inversion in the circle of centre `c` and radius `R` maps the circle `circleMap c r` of the same
centre to the circle `circleMap c (R ^ 2 / r)`, point by point at the same angle
(`EuclideanGeometry.inversion_circleMap`). The radius `r` may be zero or negative: a circle of
negative radius is traversed from the antipodal point, and so is its image.

In a real inner product space, inversion about the origin in the sphere of radius `R` exchanges
the regions `R ^ 2 / r < ‖x‖` and `‖x‖ < r` of the punctured space, for every `r > 0`
(`EuclideanGeometry.norm_inversion_zero_lt_iff`, `EuclideanGeometry.lt_norm_inversion_zero_iff`).
These extend Tau Ceti's `EuclideanGeometry.norm_inversion_lt_inv_iff` and
`EuclideanGeometry.inv_lt_norm_inversion_iff` from the unit sphere to any radius.
Inversion about the origin also commutes with scaling, once the radius is scaled as well
(`EuclideanGeometry.inversion_zero_smul`).
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

section Norm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Inversion about the origin commutes with scaling by `a`, when the radius is scaled by `a` too:
`inversion 0 (a * R) (a • x) = a • inversion 0 R x`. -/
theorem inversion_zero_smul (a R : ℝ) (x : V) :
    inversion (0 : V) (a * R) (a • x) = a • inversion 0 R x := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  simp only [inversion, dist_zero_right, vsub_eq_sub, sub_zero, vadd_eq_add, add_zero, norm_smul,
    Real.norm_eq_abs]
  rw [smul_comm]
  congr 1
  rw [div_pow, div_pow, mul_pow, mul_pow, sq_abs]
  field_simp

/-- For `r > 0`, inversion about the origin in the sphere of radius `R` maps a point `x ≠ 0` into
the region `‖w‖ < r` exactly when `R ^ 2 / r < ‖x‖`. -/
theorem norm_inversion_zero_lt_iff (R : ℝ) {r : ℝ} (hr : 0 < r) {x : V} (hx : x ≠ 0) :
    ‖inversion (0 : V) R x‖ < r ↔ R ^ 2 / r < ‖x‖ := by
  rw [norm_inversion_zero, div_lt_iff₀ (norm_pos_iff.2 hx), div_lt_iff₀ hr, mul_comm]

/-- For `r > 0`, inversion about the origin in the sphere of radius `R` maps a point `x ≠ 0` into
the region `r < ‖w‖` exactly when `‖x‖ < R ^ 2 / r`. -/
theorem lt_norm_inversion_zero_iff (R : ℝ) {r : ℝ} (hr : 0 < r) {x : V} (hx : x ≠ 0) :
    r < ‖inversion (0 : V) R x‖ ↔ ‖x‖ < R ^ 2 / r := by
  rw [norm_inversion_zero, lt_div_iff₀ (norm_pos_iff.2 hx), lt_div_iff₀ hr, mul_comm]

end Norm

end EuclideanGeometry

end
