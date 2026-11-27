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
Inversion about a point commutes with the homotheties of the same centre, once the radius is
scaled as well (`EuclideanGeometry.inversion_mul_homothety`).

In `ℂ`, inversion about `0` in the circle of radius `R` is `z ↦ R ^ 2 / conj z`
(`EuclideanGeometry.inversion_zero_eq_sq_div_conj`, from Tau Ceti's
`TauCeti.inversion_eq_conj_reciprocal`). So it maps real points to real points, its real and
imaginary parts are those of `z` scaled by `R ^ 2 / |z| ^ 2`, it keeps the open lower half-plane,
and its distance to a real point is that of `R ^ 2 / z`.
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

/-- Inversion about `c` commutes with the homothety of centre `c` and ratio `a`, when the radius
is scaled by `a` too: `inversion c (a * R) (homothety c a x) = homothety c a (inversion c R x)`. -/
theorem inversion_mul_homothety {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (c : P) (a R : ℝ) (x : P) :
    inversion c (a * R) (AffineMap.homothety c a x) =
      AffineMap.homothety c a (inversion c R x) := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rcases eq_or_ne x c with rfl | hx
  · simp
  have : dist x c ≠ 0 := dist_ne_zero.2 hx
  simp only [inversion, AffineMap.homothety_apply, vadd_vsub, dist_vadd_left, norm_smul,
    Real.norm_eq_abs, ← dist_eq_norm_vsub, smul_smul]
  congr 2
  rw [div_pow, div_pow, mul_pow, mul_pow, sq_abs]
  field_simp

section Norm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

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

section Complex

open ComplexConjugate

/-- In `ℂ`, inversion about `0` in the circle of radius `R` is `z ↦ R ^ 2 / conj z`. -/
theorem inversion_zero_eq_sq_div_conj (R : ℝ) (z : ℂ) :
    inversion (0 : ℂ) R z = (R : ℂ) ^ 2 / conj z := by
  rw [TauCeti.inversion_eq_conj_reciprocal]
  simp

/-- In `ℂ`, inversion about `0` in the circle of radius `R` maps the real point `x` to the real
point `R ^ 2 / x`. -/
@[simp]
theorem inversion_zero_ofReal (R x : ℝ) : inversion (0 : ℂ) R (x : ℂ) = (R : ℂ) ^ 2 / x := by
  rw [inversion_zero_eq_sq_div_conj, Complex.conj_ofReal]

/-- The real part of the image of `z` under inversion about `0` in the circle of radius `R` is
`R ^ 2 * re z / |z| ^ 2`. -/
theorem inversion_zero_re (R : ℝ) (z : ℂ) :
    (inversion (0 : ℂ) R z).re = R ^ 2 * z.re / Complex.normSq z := by
  rw [inversion_zero_eq_sq_div_conj, div_eq_mul_inv, ← Complex.ofReal_pow, Complex.re_ofReal_mul,
    Complex.inv_re, Complex.conj_re, Complex.normSq_conj, mul_div_assoc]

/-- The imaginary part of the image of `z` under inversion about `0` in the circle of radius `R` is
`R ^ 2 * im z / |z| ^ 2`. -/
theorem inversion_zero_im (R : ℝ) (z : ℂ) :
    (inversion (0 : ℂ) R z).im = R ^ 2 * z.im / Complex.normSq z := by
  rw [inversion_zero_eq_sq_div_conj, div_eq_mul_inv, ← Complex.ofReal_pow, Complex.im_ofReal_mul,
    Complex.inv_im, Complex.conj_im, Complex.normSq_conj, neg_neg, mul_div_assoc]

/-- Inversion about `0` in a circle of nonzero radius maps the open lower half-plane to itself. -/
theorem inversion_zero_im_neg {R : ℝ} (hR : R ≠ 0) {z : ℂ} (hz : z.im < 0) :
    (inversion (0 : ℂ) R z).im < 0 := by
  rw [inversion_zero_im]
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by positivity) hz)
    (Complex.normSq_pos.2 (by rintro rfl; simp at hz))

/-- The distance from the image of `z` under inversion about `0` in the circle of radius `R` to a
real point `x` is that from `R ^ 2 / z` to `x`, since the two are mirror images in the real
axis. -/
theorem norm_inversion_zero_sub_ofReal (R : ℝ) (z : ℂ) (x : ℝ) :
    ‖inversion (0 : ℂ) R z - x‖ = ‖(R : ℂ) ^ 2 / z - x‖ := by
  rw [inversion_zero_eq_sq_div_conj, ← Complex.norm_conj]
  simp

end Complex

end EuclideanGeometry

end
