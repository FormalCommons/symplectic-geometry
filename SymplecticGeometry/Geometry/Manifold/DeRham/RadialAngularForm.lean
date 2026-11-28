/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Orientation.Complex
public import TauCeti.Geometry.Manifold.DeRham.Circle
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
public import Mathlib.LinearAlgebra.Complex.Orientation
import SymplecticGeometry.Analysis.Calculus.Deriv.EventuallyConst
import TauCeti.Analysis.InnerProductSpace.NormPow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.MeasureTheory.Integral.PolarCoord
import TauCeti.MeasureTheory.Measure.Haar.OfBasis
import TauCeti.Topology.Algebra.Support
import Mathlib.Data.Fin.Tuple.Reflection

/-!
# The angular form cut off near the origin

For a function `β : ℝ → ℝ`, the `1`-form `β(‖z‖) dθ` on the plane `ℂ`, where
`dθ = ‖z‖⁻² (x dy - y dx)` is the angular form of the punctured plane, is
`SymplecticGeometry.radialAngularForm β`. If `β` is `C^n` and vanishes on `(-∞, a]` for some
`a > 0`, the form is `C^n` on all of `ℂ`. Its exterior derivative is
`β'(r) dr ∧ dθ = β'(‖z‖) / ‖z‖ · dx ∧ dy`. If moreover `β = 1` on `[b, ∞)`, this `2`-form is
supported in the closed annulus `a ≤ ‖z‖ ≤ b`, and its integral over `ℂ`, for the standard
orientation in which `(1, i)` is positive, is `2π ∫ β' = 2π`.

These forms are the local models of the curvature of a connection on a circle bundle that is flat
outside a disc: in polar coordinates `β(r) dθ` interpolates between the zero form near the centre
and the angular form near the boundary circle.

The integral is computed in polar form through Tau Ceti's `TauCeti.integral_fun_norm_complex`:
on `ℂ`, the integral of `f(‖z‖)` is `2π ∫₀^∞ f(r) r dr`.

The standard orientation is `TauCeti.Manifold.Orientation.complex`, the constant orientation
given by `Complex.orientation`. It is the orientation of `ℂ` as a complex manifold, but Tau
Ceti's `TauCeti.complexManifoldOrientation` is indexed by `Fin (2 * finrank ℂ ℂ)`, which is not
`Fin 2` by definition, so it does not integrate `2`-forms directly.

## Main declarations

* `SymplecticGeometry.radialAngularForm β`: the `1`-form `β(‖z‖) dθ` on `ℂ`.
* `SymplecticGeometry.isSmoothForm_radialAngularForm`: it is `C^n` when `β` is and vanishes near
  `0`.
* `SymplecticGeometry.mextDeriv_radialAngularForm_apply_of_ne_zero`: away from the origin,
  `d(β(‖z‖) dθ) = β'(‖z‖)/‖z‖ dx ∧ dy` for any `β` differentiable at `‖z‖`.
* `SymplecticGeometry.mextDeriv_radialAngularForm_apply`: the same on all of `ℂ` when `β` vanishes
  near `0`.
* `SymplecticGeometry.tsupport_mextDeriv_radialAngularForm_subset`: its exterior derivative is
  supported in the annulus `a ≤ ‖z‖ ≤ b`.
* `SymplecticGeometry.integralTopForm_mextDeriv_radialAngularForm`: `∫_ℂ d(β(‖z‖) dθ) = 2π`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §2.7 (the first Chern number as the integral of a curvature form).
* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §6 (the angular
  form and the global angular form of a circle bundle).
-/

public section

noncomputable section

open Set Filter MeasureTheory TauCeti
open scoped Manifold ContDiff Topology Real

namespace SymplecticGeometry

/-- The `1`-form `β(‖z‖) dθ` on the plane `ℂ`, where `dθ = ‖z‖⁻² (x dy - y dx)` is the angular
form of the punctured plane: at `z` it is `β ‖z‖ / ‖z‖ ^ 2` times `TauCeti.planeAngularForm`.
At `z = 0` it is zero. -/
def radialAngularForm (β : ℝ → ℝ) : RoughForm 𝓘(ℝ, ℂ) ℂ ℝ 1 :=
  fun z ↦ (β ‖z‖ / ‖z‖ ^ 2) • planeAngularForm z

theorem radialAngularForm_def (β : ℝ → ℝ) :
    radialAngularForm β = fun z ↦ (β ‖z‖ / ‖z‖ ^ 2) • planeAngularForm z :=
  (rfl)

/-- Evaluation of `β(‖z‖) dθ`: `β ‖z‖ / ‖z‖ ^ 2 * (x v_y - y v_x)` at `z = x + y i`. -/
@[simp]
theorem radialAngularForm_apply (β : ℝ → ℝ) (z : ℂ) (v : Fin 1 → ℂ) :
    radialAngularForm β z v = β ‖z‖ / ‖z‖ ^ 2 * (z.re * (v 0).im - z.im * (v 0).re) := by
  rw [radialAngularForm_def]
  -- The form takes vectors of the tangent spaces of `ℂ`, which are `ℂ` only after unfolding
  -- `TangentSpace`, so these rewrites need `erw`.
  erw [ContinuousAlternatingMap.smul_apply, planeAngularForm_apply]
  rfl

variable {β : ℝ → ℝ} {a b : ℝ}

/-- If `β` vanishes on `(-∞, a]` with `a > 0`, then `β(‖z‖) dθ` vanishes near the origin. -/
theorem radialAngularForm_eventuallyEq_zero (ha : 0 < a) (hβa : ∀ t ≤ a, β t = 0) :
    Filter.EventuallyEq (β := ℂ [⋀^Fin 1]→L[ℝ] ℝ) (𝓝 (0 : ℂ)) (radialAngularForm β) 0 := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) ha] with z hz
  rw [radialAngularForm_def]
  simp only [hβa _ (mem_ball_zero_iff.1 hz).le, zero_div, zero_smul]
  -- The two zeros are alternating maps on `TangentSpace 𝓘(ℝ, ℂ) z` and on `ℂ`.
  rfl

/-- The plane angular form `x dy - y dx`, as a smooth map into alternating maps. -/
private theorem contDiff_planeAngularForm :
    ContDiff ℝ (E := ℂ) (F := ℂ [⋀^Fin 1]→L[ℝ] ℝ) ∞ planeAngularForm :=
  isSmoothForm_modelSpace_iff.1 isSmoothForm_planeAngularForm

/-- **Smoothness of `β(‖z‖) dθ`.** If `β` is `C^n` and vanishes on `(-∞, a]` with `a > 0`, the
form `β(‖z‖) dθ` is `C^n` on all of `ℂ`. -/
theorem isSmoothForm_radialAngularForm {n : WithTop ℕ∞} (hn : n ≤ ∞) (hβ : ContDiff ℝ n β)
    (ha : 0 < a) (hβa : ∀ t ≤ a, β t = 0) : IsSmoothForm 𝓘(ℝ, ℂ) n (radialAngularForm β) := by
  rw [isSmoothForm_modelSpace_iff]
  refine contDiff_iff_contDiffAt.2 fun z ↦ ?_
  rcases eq_or_ne z 0 with rfl | hz
  · exact contDiffAt_const.congr_of_eventuallyEq (radialAngularForm_eventuallyEq_zero ha hβa)
  · rw [radialAngularForm_def]
    exact ((hβ.contDiffAt.comp z ((contDiffAt_norm ℝ hz).of_le hn)).div
      (((contDiffAt_norm ℝ hz).of_le hn).pow 2) (by positivity)).smul
      (contDiff_planeAngularForm.of_le hn).contDiffAt

/-- The derivative at `z ≠ 0` of the coefficient `y ↦ β ‖y‖ / ‖y‖ ^ 2` of `β(‖y‖) dθ`, for `β`
differentiable at `‖z‖`. -/
private theorem hasFDerivAt_radialCoeff {z : ℂ} (hz : z ≠ 0) (hβ : DifferentiableAt ℝ β ‖z‖) :
    HasFDerivAt (fun y : ℂ ↦ β ‖y‖ / ‖y‖ ^ 2)
      (((deriv β ‖z‖ * ‖z‖ ^ 2 - β ‖z‖ * (2 * ‖z‖)) / (‖z‖ ^ 2) ^ 2) • ‖z‖⁻¹ • innerSL ℝ z)
      z := by
  have h := (hβ.hasDerivAt.div (hasDerivAt_pow 2 ‖z‖)
    (pow_ne_zero 2 (norm_ne_zero_iff.2 hz))).comp_hasFDerivAt z (hasFDerivAt_norm_of_ne hz)
  exact h.congr_fderiv (by simp)

/-- The derivative at `z ≠ 0` of the coefficient `y ↦ β(‖y‖) dθ_y(w)` of `β(‖y‖) dθ` on a fixed
vector `w`, for `β` differentiable at `‖z‖`. -/
private theorem hasFDerivAt_radialAngularForm_apply {z : ℂ} (hz : z ≠ 0)
    (hβ : DifferentiableAt ℝ β ‖z‖) (w : ℂ) :
    HasFDerivAt (fun y : ℂ ↦ radialAngularForm β y ![w])
      ((β ‖z‖ / ‖z‖ ^ 2) • (w.im • Complex.reCLM - w.re • Complex.imCLM) +
        (z.re * w.im - z.im * w.re) •
          ((deriv β ‖z‖ * ‖z‖ ^ 2 - β ‖z‖ * (2 * ‖z‖)) / (‖z‖ ^ 2) ^ 2) •
            ‖z‖⁻¹ • innerSL ℝ z) z := by
  have hl : HasFDerivAt (fun y : ℂ ↦ y.re * w.im - y.im * w.re)
      (w.im • Complex.reCLM - w.re • Complex.imCLM) z := by
    convert (Complex.reCLM.hasFDerivAt (x := z) |>.mul_const w.im).sub
      (Complex.imCLM.hasFDerivAt.mul_const w.re) using 1
    ext
    simp [mul_comm]
  have he : (fun y : ℂ ↦ radialAngularForm β y ![w]) =
      fun y ↦ β ‖y‖ / ‖y‖ ^ 2 * (y.re * w.im - y.im * w.re) :=
    funext fun y ↦ radialAngularForm_apply β y ![w]
  rw [he]
  exact (hasFDerivAt_radialCoeff hz hβ).mul hl

/-- **The exterior derivative of `β(‖z‖) dθ` away from the origin.** At a point `z ≠ 0` where
`β` is differentiable at `‖z‖`, the exterior derivative of `β(‖z‖) dθ` is
`β'(‖z‖) / ‖z‖ dx ∧ dy`. -/
theorem mextDeriv_radialAngularForm_apply_of_ne_zero {z : ℂ} (hz : z ≠ 0)
    (hβ : DifferentiableAt ℝ β ‖z‖) (v : Fin 2 → ℂ) :
    mextDeriv (radialAngularForm β) z v =
      deriv β ‖z‖ / ‖z‖ * ((v 0).re * (v 1).im - (v 0).im * (v 1).re) := by
  have hd : DifferentiableAt ℝ (E := ℂ) (F := ℂ [⋀^Fin 1]→L[ℝ] ℝ) (radialAngularForm β) z := by
    rw [radialAngularForm_def]
    exact (hasFDerivAt_radialCoeff hz hβ).differentiableAt.smul
      (contDiff_planeAngularForm.differentiable (by simp) z)
  have e0 : Fin.removeNth 0 v = ![v 1] := (FinVec.etaExpand_eq _).symm
  have e1 : Fin.removeNth 1 v = ![v 0] := (FinVec.etaExpand_eq _).symm
  rw [mextDeriv_eq_extDeriv]
  refine (extDeriv_apply hd v).trans ?_
  rw [Fin.sum_univ_two, e0, e1]
  -- The coefficient functions are stated on `ℂ`, the form on the tangent spaces of `ℂ`.
  erw [(hasFDerivAt_radialAngularForm_apply hz hβ (v 1)).fderiv,
    (hasFDerivAt_radialAngularForm_apply hz hβ (v 0)).fderiv]
  have hr : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz
  have hn2 : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq]
  simp [Complex.inner]
  field_simp
  linear_combination (2 * β ‖z‖ - ‖z‖ * deriv β ‖z‖) *
    ((v 1).im * (v 0).re - (v 1).re * (v 0).im) * hn2

/-- **The exterior derivative of `β(‖z‖) dθ`** is `β'(r) dr ∧ dθ = β'(‖z‖) / ‖z‖ dx ∧ dy`, for
`β` differentiable and vanishing on `(-∞, a]` with `a > 0`. At `z = 0` both sides vanish. -/
theorem mextDeriv_radialAngularForm_apply (hβ : Differentiable ℝ β) (ha : 0 < a)
    (hβa : ∀ t ≤ a, β t = 0) (z : ℂ) (v : Fin 2 → ℂ) :
    mextDeriv (radialAngularForm β) z v =
      deriv β ‖z‖ / ‖z‖ * ((v 0).re * (v 1).im - (v 0).im * (v 1).re) := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [mextDeriv_congr_of_eventuallyEq (η := (0 : RoughForm 𝓘(ℝ, ℂ) ℂ ℝ 1))
        (radialAngularForm_eventuallyEq_zero ha hβa),
      mextDeriv_zero]
    simp only [norm_zero, div_zero, zero_mul]
    -- The zero alternating map, applied to vectors of the tangent space of `ℂ` at `0`.
    rfl
  · exact mextDeriv_radialAngularForm_apply_of_ne_zero hz (hβ _) v

/-- **Support of `d(β(‖z‖) dθ)`.** If `β` is differentiable, `0` on `(-∞, a]` and `1` on
`[b, ∞)`, with `a > 0`, the exterior derivative of `β(‖z‖) dθ` is supported in the closed
annulus `a ≤ ‖z‖ ≤ b`. -/
theorem tsupport_mextDeriv_radialAngularForm_subset (hβ : Differentiable ℝ β) (ha : 0 < a)
    (hβa : ∀ t ≤ a, β t = 0) (hβb : ∀ t ≥ b, β t = 1) :
    _root_.tsupport (α := ℂ [⋀^Fin 2]→L[ℝ] ℝ) (mextDeriv (radialAngularForm β)) ⊆
      {z : ℂ | ‖z‖ ∈ Icc a b} := by
  refine TauCeti.tsupport_subset_of_forall_notMem_eq_zero (fun z h ↦ ?_)
    (isClosed_Icc.preimage continuous_norm)
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  refine (mextDeriv_radialAngularForm_apply hβ ha hβa z v).trans ?_
  rw [deriv_eq_zero_of_notMem_Icc hβa hβb h, zero_div, zero_mul]
  -- The zero alternating map, applied to vectors of the tangent space of `ℂ` at `z`.
  rfl

/-- The exterior derivative of `β(‖z‖) dθ` on the positive basis `(1, i)` is `β'(‖z‖) / ‖z‖`. -/
private theorem mextDeriv_radialAngularForm_basisOneI (hβ : Differentiable ℝ β) (ha : 0 < a)
    (hβa : ∀ t ≤ a, β t = 0) (z : ℂ) :
    mextDeriv (radialAngularForm β) z Complex.basisOneI = deriv β ‖z‖ / ‖z‖ := by
  rw [mextDeriv_radialAngularForm_apply hβ ha hβa]
  simp

/-- **The integral of `d(β(‖z‖) dθ)`.** If `β` is `C¹`, `0` on `(-∞, a]` and `1` on `[b, ∞)`,
with `0 < a`, then the integral of `d(β(‖z‖) dθ)` over `ℂ`, for the standard orientation in which
`(1, i)` is positive, is `2π`. -/
theorem integralTopForm_mextDeriv_radialAngularForm (hβ : ContDiff ℝ 1 β) (ha : 0 < a)
    (hβa : ∀ t ≤ a, β t = 0) (hβb : ∀ t ≥ b, β t = 1) :
    integralTopForm Manifold.Orientation.complex
      (mextDeriv (radialAngularForm β)) = 2 * π := by
  have hβd : Differentiable ℝ β := hβ.differentiable (by simp)
  have hab : a ≤ b := by
    by_contra h
    have := hβa b (not_le.1 h).le
    rw [hβb b le_rfl] at this
    exact one_ne_zero this
  -- The form is smooth with compact support, hence integrable.
  have hint : IntegrableTopForm (mextDeriv (radialAngularForm β)) :=
    (isSmoothForm_mextDeriv (isSmoothForm_radialAngularForm (by simp) hβ ha hβa) (n := 0)
      (by simp)).integrableTopForm
      ((isCompact_closedBall (0 : ℂ) b).of_isClosed_subset (isClosed_tsupport _)
        ((tsupport_mextDeriv_radialAngularForm_subset hβd ha hβa hβb).trans
          fun z hz ↦ mem_closedBall_zero_iff.2 hz.2)) Complex.basisOneI
  -- `Complex.orientation` is by definition the orientation of `Complex.basisOneI`.
  rw [Manifold.Orientation.complex_def,
    integralTopForm_model_eq_integral_of_integrableTopForm Complex.orientation _ hint
      Complex.basisOneI rfl,
    Complex.addHaar_basisOneI]
  simp only [mextDeriv_radialAngularForm_basisOneI hβd ha hβa]
  rw [TauCeti.integral_fun_norm_complex (fun t ↦ deriv β t / t)]
  -- Polar form: `∫_ℂ f(‖z‖) = 2 π ∫₀^∞ f(r) r dr`, and here `f(r) r = β'(r)`.
  have hpolar : ∫ t in Ioi (0 : ℝ), t • (deriv β t / t) =
      ∫ t in Ioi (0 : ℝ), deriv β t := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) ↦ ?_
    rw [smul_eq_mul]
    field_simp
  have hderiv : ∫ t in Ioi (0 : ℝ), deriv β t = 1 := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      Ioc_subset_Ioi_self fun t ht ↦ deriv_eq_zero_of_notMem_Icc hβa hβb
        fun h ↦ ht.2 ⟨ht.1, h.2⟩,
      ← intervalIntegral.integral_of_le (ha.le.trans hab),
      intervalIntegral.integral_deriv_eq_sub (fun t _ ↦ hβd t)
        ((hβ.continuous_deriv (by simp)).intervalIntegrable _ _),
      hβb b le_rfl, hβa 0 ha.le, sub_zero]
  rw [hpolar, hderiv, smul_eq_mul, mul_one]

end SymplecticGeometry

end

end
