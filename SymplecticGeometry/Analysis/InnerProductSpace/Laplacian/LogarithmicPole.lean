/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.PDE.FundamentalSolution.Planar.DistributionalLaplacian
public import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian

/-!
# The Laplacian of a cut-off logarithmic pole

Let `a : ℂ` and let `χ : ℂ → ℝ` be a compactly supported `C²` function that is equal to `1` on a
neighbourhood of `a`. The function `ψ t = χ t * log ‖t - a‖²` has a logarithmic pole at `a`, but
its Laplacian is a continuous compactly supported function (smooth when `χ` is), and

`∫ Δψ = -4π`.

This is the distributional identity `Δ log ‖· - a‖² = 4π δₐ` seen through the cutoff `χ`.

## Main results

* `SymplecticGeometry.laplacian_log_norm_sub_sq`: `log ‖· - a‖²` has pointwise Laplacian `0`
  everywhere, the value at the pole being the junk value.
* `SymplecticGeometry.laplacian_fun_mul_log_norm_sub_sq`: `Δψ = -Δ((1 - χ) log ‖· - a‖²)`, a
  Laplacian of a function that is `C²` on all of `ℂ`.
* `SymplecticGeometry.contDiff_laplacian_fun_mul_log_norm_sub_sq` and
  `SymplecticGeometry.hasCompactSupport_laplacian_fun_mul_log_norm_sub_sq`: `Δψ` is `C^m` when `χ`
  is `C^(m + 2)`, and has compact support; so it is integrable
  (`SymplecticGeometry.integrable_laplacian_fun_mul_log_norm_sub_sq`).
* `SymplecticGeometry.integral_laplacian_fun_mul_log_norm_sub_sq`: `∫ Δψ = -4π`.

## Implementation notes

The integral is computed with a bump function `φ` that is `1` on a neighbourhood of the support of
`χ`. Green's second identity against `φ` (Tau Ceti's
`ContDiffOn.integral_laplacian_smul_eq_integral_smul_laplacian`) moves the Laplacian of the
`C²` function `(1 - χ) log ‖· - a‖²` onto `φ`; since `Δφ` vanishes where `χ ≠ 0`, what remains is
`∫ Δφ · log ‖· - a‖²`, which Tau Ceti's `integral_laplacian_mul_planarNewtonianKernel_sub`
evaluates, as `log ‖t - a‖² = -4π G(t - a)` for the planar Newtonian kernel `G`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  proof of Proposition 7.1.13.
-/

public section

namespace SymplecticGeometry

open InnerProductSpace MeasureTheory Filter Topology Metric TauCeti
open scoped Laplacian ContDiff Distributions

/-- The function `log ‖t - a‖²` is `-4π` times the planar Newtonian kernel with pole `a`. -/
theorem log_norm_sub_sq_eq_planarNewtonianKernel (t a : ℂ) :
    Real.log (‖t - a‖ ^ 2) = -(4 * Real.pi) * planarNewtonianKernel (t - a) := by
  rw [planarNewtonianKernel_def, Real.log_pow]
  field_simp
  push_cast
  ring

/-- Away from `a`, the function `log ‖· - a‖²` is `C^n` for every `n`. -/
theorem contDiffAt_log_norm_sub_sq {n : WithTop ℕ∞} {z a : ℂ} (hz : z ≠ a) :
    ContDiffAt ℝ n (fun t : ℂ ↦ Real.log (‖t - a‖ ^ 2)) z :=
  ((contDiffAt_id.sub contDiffAt_const).norm_sq ℝ).log
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz)))

/-- The function `log ‖· - a‖²` solves the Laplace equation pointwise on all of `ℂ`: away from
`a` it is harmonic, and at the pole the value `0` is the junk value of the Laplacian of a function
not differentiable there. -/
theorem laplacian_log_norm_sub_sq (a z : ℂ) :
    Δ (fun t : ℂ ↦ Real.log (‖t - a‖ ^ 2)) z = 0 := by
  let l : ℝ ≃L[ℝ] ℝ :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 (-(4 * Real.pi)) (neg_ne_zero.mpr (by positivity)))
  have hl : (fun t : ℂ ↦ Real.log (‖t - a‖ ^ 2)) = l ∘ fun t ↦ planarNewtonianKernel (t - a) := by
    funext t
    rw [Function.comp_apply, ContinuousLinearEquiv.smulLeft_apply_apply, Units.smul_mk0,
      smul_eq_mul, log_norm_sub_sq_eq_planarNewtonianKernel]
  rw [hl, laplacian_CLE_comp_left]
  simp

/-- If `χ` is `C^n` and equal to `1` near `a`, then `(1 - χ) log ‖· - a‖²` is `C^n` on all
of `ℂ`: the cutoff removes the pole. -/
theorem contDiff_one_sub_mul_log_norm_sub_sq {n : WithTop ℕ∞} {a : ℂ} {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ n χ) (hχa : χ =ᶠ[𝓝 a] 1) :
    ContDiff ℝ n fun t ↦ (1 - χ t) * Real.log (‖t - a‖ ^ 2) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  rcases eq_or_ne z a with rfl | hz
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hχa] with t ht
    simp [ht]
  · exact (contDiffAt_const.sub hχ.contDiffAt).mul (contDiffAt_log_norm_sub_sq hz)

/-- If `χ` is `C²` and equal to `1` near `a`, then the Laplacian of `χ log ‖· - a‖²` is minus
that of the `C²` function `(1 - χ) log ‖· - a‖²`, at every point, the pole included. -/
theorem laplacian_fun_mul_log_norm_sub_sq {a : ℂ} {χ : ℂ → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hχa : χ =ᶠ[𝓝 a] 1) (z : ℂ) :
    Δ (fun t ↦ χ t * Real.log (‖t - a‖ ^ 2)) z =
      -Δ (fun t ↦ (1 - χ t) * Real.log (‖t - a‖ ^ 2)) z := by
  rcases eq_or_ne z a with rfl | hz
  · have h₁ : (fun t ↦ χ t * Real.log (‖t - z‖ ^ 2)) =ᶠ[𝓝 z]
        fun t ↦ Real.log (‖t - z‖ ^ 2) := by
      filter_upwards [hχa] with t ht
      simp [ht]
    have h₂ : (fun t ↦ (1 - χ t) * Real.log (‖t - z‖ ^ 2)) =ᶠ[𝓝 z] fun _ ↦ (0 : ℝ) := by
      filter_upwards [hχa] with t ht
      simp [ht]
    rw [(laplacian_congr_nhds h₁).self_of_nhds, (laplacian_congr_nhds h₂).self_of_nhds,
      laplacian_log_norm_sub_sq, laplacian_const, Pi.zero_apply, neg_zero]
  · have hL : ContDiffAt ℝ 2 (fun t : ℂ ↦ Real.log (‖t - a‖ ^ 2)) z :=
      contDiffAt_log_norm_sub_sq hz
    have hsum := (hχ.contDiffAt.mul hL).laplacian_add
      (((contDiffAt_const (c := (1 : ℝ))).sub hχ.contDiffAt).mul hL)
    have hfun : ((fun t ↦ χ t * Real.log (‖t - a‖ ^ 2)) +
        fun t ↦ (1 - χ t) * Real.log (‖t - a‖ ^ 2)) = fun t ↦ Real.log (‖t - a‖ ^ 2) := by
      funext t
      simp only [Pi.add_apply]
      ring
    rw [hfun, laplacian_log_norm_sub_sq] at hsum
    linarith

/-- If `χ` is `C^n` and equal to `1` near `a`, then the Laplacian of `χ log ‖· - a‖²` is `C^m`
for every `m` with `m + 2 ≤ n`; in particular it is smooth when `χ` is. -/
theorem contDiff_laplacian_fun_mul_log_norm_sub_sq {n m : WithTop ℕ∞} {a : ℂ} {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ n χ) (hm : m + 2 ≤ n) (hχa : χ =ᶠ[𝓝 a] 1) :
    ContDiff ℝ m (Δ fun t ↦ χ t * Real.log (‖t - a‖ ^ 2)) := by
  have h₂ : ContDiff ℝ 2 χ := hχ.of_le (le_add_self.trans hm)
  rw [funext (laplacian_fun_mul_log_norm_sub_sq h₂ hχa)]
  exact ((contDiff_one_sub_mul_log_norm_sub_sq hχ hχa).laplacian hm).neg

/-- If `χ` is `C²` and equal to `1` near `a`, then the Laplacian of `χ log ‖· - a‖²` is
continuous. -/
theorem continuous_laplacian_fun_mul_log_norm_sub_sq {a : ℂ} {χ : ℂ → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hχa : χ =ᶠ[𝓝 a] 1) : Continuous (Δ fun t ↦ χ t * Real.log (‖t - a‖ ^ 2)) :=
  (contDiff_laplacian_fun_mul_log_norm_sub_sq (m := 0) hχ (by simp) hχa).continuous

/-- If `χ` has compact support, so has the Laplacian of `χ log ‖· - a‖²`. -/
theorem hasCompactSupport_laplacian_fun_mul_log_norm_sub_sq {a : ℂ} {χ : ℂ → ℝ}
    (hχc : HasCompactSupport χ) :
    HasCompactSupport (Δ fun t ↦ χ t * Real.log (‖t - a‖ ^ 2)) :=
  (hχc.mul_right (f' := fun t ↦ Real.log (‖t - a‖ ^ 2))).laplacian

/-- If `χ` is `C²`, compactly supported and equal to `1` near `a`, then the Laplacian of
`χ log ‖· - a‖²` is integrable. -/
theorem integrable_laplacian_fun_mul_log_norm_sub_sq {a : ℂ} {χ : ℂ → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hχc : HasCompactSupport χ) (hχa : χ =ᶠ[𝓝 a] 1) :
    Integrable (Δ fun t ↦ χ t * Real.log (‖t - a‖ ^ 2)) :=
  (continuous_laplacian_fun_mul_log_norm_sub_sq hχ hχa).integrable_of_hasCompactSupport
    (hasCompactSupport_laplacian_fun_mul_log_norm_sub_sq hχc)

/-- **The integral of the Laplacian of a cut-off logarithmic pole.** If `χ` is `C²`, compactly
supported and equal to `1` near `a`, then `∫ Δ (χ log ‖· - a‖²) = -4π`. -/
theorem integral_laplacian_fun_mul_log_norm_sub_sq {a : ℂ} {χ : ℂ → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hχc : HasCompactSupport χ) (hχa : χ =ᶠ[𝓝 a] 1) :
    ∫ t, Δ (fun t ↦ χ t * Real.log (‖t - a‖ ^ 2)) t = -(4 * Real.pi) := by
  obtain ⟨R, hR⟩ := hχc.isCompact.isBounded.subset_ball a
  set r := max R 1
  have hK : tsupport χ ⊆ ball a r := hR.trans (ball_subset_ball (le_max_left _ _))
  -- A bump function `φ` equal to `1` on the ball `ball a r` around the support of `χ`.
  let φ : ContDiffBump a := ⟨r, r + 1, by positivity, by linarith⟩
  have hφ₁ {t : ℂ} (ht : t ∈ ball a r) : φ t = 1 :=
    φ.one_of_mem_closedBall (ball_subset_closedBall ht)
  have hΔφ {t : ℂ} (ht : t ∈ ball a r) : Δ (φ : ℂ → ℝ) t = 0 := by
    have h : (φ : ℂ → ℝ) =ᶠ[𝓝 t] fun _ ↦ (1 : ℝ) :=
      eventually_of_mem (isOpen_ball.mem_nhds ht) fun _ hs ↦ hφ₁ hs
    rw [(laplacian_congr_nhds h).self_of_nhds, laplacian_const, Pi.zero_apply]
  let ϕ : 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℝ) :=
    ⟨φ, φ.contDiff, φ.hasCompactSupport, Set.subset_univ _⟩
  have hgreen := (contDiff_one_sub_mul_log_norm_sub_sq hχ hχa).contDiffOn
    (s := (⊤ : TopologicalSpace.Opens ℂ)).integral_laplacian_smul_eq_integral_smul_laplacian
    (μ := volume) ϕ
  rw [TestFunction.coe_mk] at hgreen
  -- `Δψ = -φ • Δ((1 - χ) log ‖· - a‖²)`, as `Δψ` vanishes off the support of `χ`.
  have hcut (t : ℂ) : Δ (fun t ↦ χ t * Real.log (‖t - a‖ ^ 2)) t =
      -((φ : ℂ → ℝ) t • Δ (fun t ↦ (1 - χ t) * Real.log (‖t - a‖ ^ 2)) t) := by
    have h := laplacian_fun_mul_log_norm_sub_sq hχ hχa t
    by_cases ht : t ∈ ball a r
    · rw [h, hφ₁ ht, one_smul]
    · rw [laplacian_of_notMem_tsupport fun h ↦ ht (hK (tsupport_mul_subset_left h))] at h ⊢
      rw [neg_eq_zero.mp h.symm, smul_zero, neg_zero]
  -- `Δφ • (1 - χ) log ‖· - a‖² = -4π Δφ · G(· - a)`, as `Δφ` vanishes on the support of `χ`.
  have hpole (t : ℂ) : Δ (φ : ℂ → ℝ) t • ((1 - χ t) * Real.log (‖t - a‖ ^ 2)) =
      -(4 * Real.pi) * (Δ (φ : ℂ → ℝ) t * planarNewtonianKernel (t - a)) := by
    by_cases ht : t ∈ ball a r
    · rw [hΔφ ht, zero_smul, zero_mul, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport fun h ↦ ht (hK h), sub_zero, one_mul, smul_eq_mul,
        log_norm_sub_sq_eq_planarNewtonianKernel]
      ring
  simp_rw [hcut, integral_neg, ← hgreen, hpole]
  rw [integral_const_mul,
    integral_laplacian_mul_planarNewtonianKernel_sub φ.contDiff φ.hasCompactSupport a,
    φ.one_of_mem_closedBall (mem_closedBall_self (by positivity))]
  ring

end SymplecticGeometry

end
