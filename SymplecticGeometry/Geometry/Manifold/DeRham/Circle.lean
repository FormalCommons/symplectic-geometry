/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Circle

/-!
# Rotation invariance of the angular form on the circle

The angular form `dθ` on the unit circle (`TauCeti.circleAngularForm`), the restriction of
`x dy - y dx`, is invariant under the rotations of the circle: for every `a : Circle`, the
pull-back of `dθ` along `w ↦ a * w`, and along `w ↦ w * a`, is `dθ`. In the plane this is the
invariance of `x dy - y dx = Im (conj z dz)` under multiplication by a complex number of modulus
one.

## Main results

* `TauCeti.mpullback_mul_planeAngularForm`: multiplication by a complex number of modulus one
  preserves `x dy - y dx`.
* `TauCeti.mpullback_mul_left_circleAngularForm`, `TauCeti.mpullback_mul_right_circleAngularForm`:
  the rotations of the circle preserve `dθ`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 11 (the angle form on the
  circle).
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace TauCeti

attribute [local instance] finrank_real_complex_fact'

/-- Multiplication by a complex number `a` of modulus one preserves the `1`-form `x dy - y dx` on
the plane. -/
theorem mpullback_mul_planeAngularForm {a : ℂ} (ha : ‖a‖ = 1) :
    mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun z : ℂ ↦ a * z) planeAngularForm = planeAngularForm := by
  have hd (z u : ℂ) : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun z : ℂ ↦ a * z) z u = a * u := by
    rw [mfderiv_eq_fderiv]
    -- `NormedSpace.fromTangentSpace` is the identity of `ℂ` and has no simp lemmas.
    change fderiv ℝ (fun z : ℂ ↦ a * z) z u = a * u
    rw [show (fun z : ℂ ↦ a * z) = fun y ↦ a * id y from rfl,
      ((hasFDerivAt_id z).const_mul a).fderiv]
    simp
  have hnorm : a.re * a.re + a.im * a.im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, ha, one_pow]
  have key (z u : ℂ) :
      (a * z).re * (a * u).im - (a * z).im * (a * u).re = z.re * u.im - z.im * u.re := by
    simp only [Complex.mul_re, Complex.mul_im]
    linear_combination (z.re * u.im - z.im * u.re) * hnorm
  funext z
  ext v
  -- The tangent vectors of `ℂ` are elements of `ℂ` only up to unfolding `TangentSpace`.
  erw [mpullback_apply, planeAngularForm_apply, planeAngularForm_apply, hd]
  exact key z (v 0)

/-- The rotations `w ↦ a * w` of the circle preserve its angular form. -/
theorem mpullback_mul_left_circleAngularForm (a : Circle) :
    mpullback (𝓡 1) (𝓡 1) (fun w : Circle ↦ a * w) circleAngularForm = circleAngularForm := by
  have hcoe : MDifferentiable (𝓡 1) 𝓘(ℝ, ℂ) (fun z : Circle ↦ (z : ℂ)) :=
    (contMDiff_coe_sphere (m := 1)).mdifferentiable one_ne_zero
  have hmul : MDifferentiable (𝓡 1) (𝓡 1) (fun w : Circle ↦ a * w) :=
    (contMDiff_mul_left (n := 1)).mdifferentiable one_ne_zero
  have hmulℂ : MDifferentiable 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun z : ℂ ↦ (a : ℂ) * z) :=
    (contDiff_const.mul contDiff_id).contMDiff.mdifferentiable (n := 1) (by simp)
  have hcomp : (fun z : Circle ↦ (z : ℂ)) ∘ (fun w : Circle ↦ a * w) =
      (fun z : ℂ ↦ (a : ℂ) * z) ∘ fun z : Circle ↦ (z : ℂ) := by
    funext w
    simp
  rw [circleAngularForm_def, ← mpullback_comp hmul hcoe, hcomp, mpullback_comp hcoe hmulℂ,
    mpullback_mul_planeAngularForm (by simp)]

/-- The rotations `w ↦ w * a` of the circle preserve its angular form. -/
theorem mpullback_mul_right_circleAngularForm (a : Circle) :
    mpullback (𝓡 1) (𝓡 1) (fun w : Circle ↦ w * a) circleAngularForm = circleAngularForm := by
  simp_rw [mul_comm _ a]
  exact mpullback_mul_left_circleAngularForm a

end TauCeti
