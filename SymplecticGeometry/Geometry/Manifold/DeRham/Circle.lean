/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Lie.Exponential.Circle
public import TauCeti.Geometry.Manifold.DeRham.Circle
import SymplecticGeometry.Analysis.Complex.RadialProjection

/-!
# The angular forms of the circle and of the plane

The angular form `dθ` on the unit circle (`TauCeti.circleAngularForm`), the restriction of
`x dy - y dx`, is invariant under the rotations of the circle (Tau Ceti's
`TauCeti.mpullback_mul_left_circleAngularForm`). In the plane, `x dy - y dx = Im (conj z dz)`
is invariant under multiplication by a complex number of modulus one. The form also takes the
value `1` on the velocity of `Circle.exp` at `0`, the generator of the Lie algebra of the circle.

The plane form also transforms simply under the maps that read the angle off a point of the
plane: at a point of the unit circle its pull-back along `z ↦ z ^ k` is `k (x dy - y dx)`, and
away from `0` its pull-back along the radial projection `z ↦ z / ‖z‖` is the angular form
`‖z‖⁻² (x dy - y dx)` of the punctured plane. Read in `ℂ`, a map `u` into the circle has
derivative `du = u · i u^* dθ`.

## Main results

* `TauCeti.mpullback_mul_planeAngularForm`: multiplication by a complex number of modulus one
  preserves `x dy - y dx`.
* `SymplecticGeometry.circleAngularForm_one_circleLieGenerator`: `dθ` takes the value `1` on the
  generator `SymplecticGeometry.circleLieGenerator` of the Lie algebra of the circle.
* `TauCeti.mpullback_zpow_planeAngularForm_apply`,
  `TauCeti.mpullback_div_norm_planeAngularForm_apply`,
  `TauCeti.mpullback_div_norm_zpow_planeAngularForm_apply`: the pull-backs of `x dy - y dx` along
  `z ↦ z ^ k` on the unit circle, along `z ↦ z / ‖z‖`, and along `z ↦ (z / ‖z‖) ^ k`.
* `TauCeti.mvfderiv_coe_circle_apply`: `du = u · i u^* dθ` for a map `u` into the circle.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 11 (the angle form on the
  circle).
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace TauCeti

attribute [local instance] finrank_real_complex_fact'

/-- The plane angular form `x dy - y dx` at `z` is `Im (conj z · v)`. -/
theorem planeAngularForm_apply_eq_im (z : ℂ) (v : Fin 1 → ℂ) :
    planeAngularForm z v = ((starRingEnd ℂ) z * v 0).im := by
  rw [planeAngularForm_apply, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- Let `f` be a map of the plane with real derivative `f'` at `z`. If
`Im (conj (f z) · f' v) = c · Im (conj z · v)` for every `v`, then at `z` the pull-back of
`x dy - y dx` along `f` is `c (x dy - y dx)`. -/
theorem mpullback_planeAngularForm_eq_smul_of_hasFDerivAt {f : ℂ → ℂ} {f' : ℂ →L[ℝ] ℂ} {z : ℂ}
    (hf : HasFDerivAt f f' z) {c : ℝ}
    (h : ∀ v : ℂ, ((starRingEnd ℂ) (f z) * f' v).im = c * ((starRingEnd ℂ) z * v).im) :
    mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f planeAngularForm z = c • planeAngularForm z := by
  ext v
  -- The tangent vectors of `ℂ` are elements of `ℂ` only up to unfolding `TangentSpace`.
  erw [mpullback_apply, mfderiv_eq_fderiv, hf.fderiv, planeAngularForm_apply_eq_im,
    ContinuousAlternatingMap.smul_apply, planeAngularForm_apply_eq_im]
  exact h (v 0)

/-- Multiplication by a complex number `a` of modulus one preserves the `1`-form `x dy - y dx` on
the plane. -/
theorem mpullback_mul_planeAngularForm {a : ℂ} (ha : ‖a‖ = 1) :
    mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun z : ℂ ↦ a * z) planeAngularForm = planeAngularForm := by
  funext z
  rw [← one_smul ℝ (planeAngularForm z)]
  refine mpullback_planeAngularForm_eq_smul_of_hasFDerivAt
    ((hasFDerivAt_id z).const_mul a) fun v ↦ ?_
  simp only [smul_apply, ContinuousLinearMap.id_apply, id, smul_eq_mul,
    map_mul, one_mul]
  rw [show (starRingEnd ℂ) a * (starRingEnd ℂ) z * (a * v) =
      ((starRingEnd ℂ) a * a) * ((starRingEnd ℂ) z * v) by ring, Complex.conj_mul', ha]
  simp

/-! ### The plane angular form under powers and radial projection -/

/-- At a point `u` of the unit circle, the pull-back of `x dy - y dx` along `z ↦ z ^ k` is
`k (x dy - y dx)`. -/
theorem mpullback_zpow_planeAngularForm_apply {u : ℂ} (hu : ‖u‖ = 1) (k : ℤ) :
    mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun z : ℂ ↦ z ^ k) planeAngularForm u =
      (k : ℝ) • planeAngularForm u := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  have hconj : (starRingEnd ℂ) u = u⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hu]
    simp
  refine mpullback_planeAngularForm_eq_smul_of_hasFDerivAt
    ((hasStrictDerivAt_zpow k u (Or.inl hu0)).hasDerivAt.hasFDerivAt.restrictScalars ℝ)
    fun v ↦ ?_
  have h1 : u ^ (-k) * u ^ k = 1 := by
    rw [← zpow_add₀ hu0]
    simp
  have h : (starRingEnd ℂ) (u ^ k) * (v * ((k : ℂ) * u ^ (k - 1))) =
      (k : ℝ) * ((starRingEnd ℂ) u * v) := by
    rw [map_zpow₀, hconj, zpow_sub₀ hu0, zpow_one, inv_zpow', Complex.ofReal_intCast]
    field_simp
    linear_combination (v * k) * h1
  simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul]
  rw [h, Complex.im_ofReal_mul]

/-- Away from `0`, the pull-back of `x dy - y dx` along the radial projection `z ↦ z / ‖z‖` onto
the unit circle is the angular form `‖z‖⁻² (x dy - y dx)`. -/
theorem mpullback_div_norm_planeAngularForm_apply {w : ℂ} (hw : w ≠ 0) :
    mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun z : ℂ ↦ z / ‖z‖) planeAngularForm w =
      (‖w‖ ^ 2)⁻¹ • planeAngularForm w := by
  have hn : DifferentiableAt ℝ (fun z : ℂ ↦ ‖z‖⁻¹) w :=
    ((contDiffAt_norm ℝ hw (n := 1)).differentiableAt one_ne_zero).inv (norm_ne_zero_iff.2 hw)
  have hd := hn.hasFDerivAt.smul (hasFDerivAt_id (𝕜 := ℝ) w)
  have heq : ((fun z : ℂ ↦ ‖z‖⁻¹) • id) = fun z : ℂ ↦ z / ‖z‖ := by
    funext z
    simp [div_eq_inv_mul, Complex.real_smul]
  rw [heq] at hd
  refine mpullback_planeAngularForm_eq_smul_of_hasFDerivAt hd fun v ↦ ?_
  simp only [add_apply, FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, id, Complex.real_smul, map_div₀, Complex.conj_ofReal]
  have h1 : ((starRingEnd ℂ) w * w).im = 0 := by
    rw [Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  have h2 : (‖w‖ : ℂ) ≠ 0 := by simpa using hw
  -- The derivative of `z / ‖z‖` is `v / ‖w‖` plus a real multiple of `w`.
  set t := fderiv ℝ (fun z : ℂ ↦ ‖z‖⁻¹) w v
  rw [show (starRingEnd ℂ) w / ‖w‖ * (((‖w‖⁻¹ : ℝ) : ℂ) * v + (t : ℂ) * w) =
      (((‖w‖ ^ 2)⁻¹ : ℝ) : ℂ) * ((starRingEnd ℂ) w * v) +
        ((t / ‖w‖ : ℝ) : ℂ) * ((starRingEnd ℂ) w * w) by
    push_cast
    field_simp,
    Complex.add_im, Complex.im_ofReal_mul, Complex.im_ofReal_mul, h1, mul_zero, add_zero]

/-- Away from `0`, the pull-back of `x dy - y dx` along `z ↦ (z / ‖z‖) ^ k` is
`k ‖z‖⁻² (x dy - y dx)`, `k` times the angular form. -/
theorem mpullback_div_norm_zpow_planeAngularForm_apply {w : ℂ} (hw : w ≠ 0) (k : ℤ) :
    mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun z : ℂ ↦ (z / ‖z‖) ^ k) planeAngularForm w =
      ((k : ℝ) * (‖w‖ ^ 2)⁻¹) • planeAngularForm w := by
  have hn := Complex.norm_div_norm hw
  have hdiv : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun z : ℂ ↦ z / ‖z‖) w :=
    (Complex.differentiableAt_div_norm hw).mdifferentiableAt
  have hpow : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun z : ℂ ↦ z ^ k) (w / ‖w‖) :=
    ((differentiableAt_zpow.2 (Or.inl (by rintro h; simp [h] at hn))).restrictScalars
      ℝ).mdifferentiableAt
  have hcomp : (fun z : ℂ ↦ (z / ‖z‖) ^ k) = (fun z : ℂ ↦ z ^ k) ∘ fun z : ℂ ↦ z / ‖z‖ := rfl
  have h : mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun z : ℂ ↦ z / ‖z‖)
      (mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun z : ℂ ↦ z ^ k) planeAngularForm) w =
      mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun z : ℂ ↦ z / ‖z‖) ((k : ℝ) • planeAngularForm) w :=
    mpullback_apply_congr (mpullback_zpow_planeAngularForm_apply hn k)
  rw [hcomp, mpullback_comp_at hdiv hpow, h, mpullback_smul, Pi.smul_apply,
    mpullback_div_norm_planeAngularForm_apply hw, mul_smul]

/-! ### The derivative of a circle-valued map -/

section CircleValued

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- For a map `u : M → Circle` differentiable at `x`, the derivative of `u` read in `ℂ` is
`du = u · i u^* dθ` at `x`. -/
theorem mvfderiv_coe_circle_apply {u : M → Circle} {x : M}
    (hu : MDifferentiableAt I (𝓡 1) u x) (v : TangentSpace I x) :
    mvfderiv I (fun y ↦ (u y : ℂ)) x v =
      (u x : ℂ) * (Complex.I * (mpullback I (𝓡 1) u circleAngularForm x ![v] : ℝ)) := by
  have huc : MDifferentiableAt I 𝓘(ℝ, ℂ) (fun y ↦ (u y : ℂ)) x :=
    ((contMDiff_coe_sphere (m := 1)).mdifferentiableAt one_ne_zero).comp x hu
  -- The logarithmic derivative of a map of modulus one is imaginary, with imaginary part `u^* dθ`.
  have hre := re_mlogDeriv_apply_eq_zero huc (.of_forall fun y ↦ Circle.norm_coe (u y)) ![v]
  have hlog : mlogDeriv I (fun y ↦ (u y : ℂ)) x ![v] =
      Complex.I * (mpullback I (𝓡 1) u circleAngularForm x ![v] : ℝ) := by
    apply Complex.ext
    · rw [hre]; simp
    · rw [mpullback_circleAngularForm_apply_eq_im_mlogDeriv hu]; simp
  rw [← hlog, mlogDeriv_apply, Matrix.cons_val_zero, ← mul_assoc,
    mul_inv_cancel₀ (Circle.coe_ne_zero _), one_mul]

end CircleValued

end TauCeti

namespace SymplecticGeometry

open TauCeti

/-- The angular form of the circle takes the value `1` on the generator of its Lie algebra. -/
@[simp]
theorem circleAngularForm_one_circleLieGenerator :
    circleAngularForm 1 ![circleLieGenerator] = 1 := by
  have h := circleAngularForm_apply_curveVelocity_circleExp 0
  rw [Manifold.curveVelocity_apply, Circle.exp_zero] at h
  convert h using 2
  funext i
  fin_cases i
  exact circleLieGenerator_def

end SymplecticGeometry
