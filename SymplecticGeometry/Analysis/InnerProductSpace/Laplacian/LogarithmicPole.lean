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
import TauCeti.Analysis.InnerProductSpace.Laplacian.Integral
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian

/-!
# Laplacians of functions with logarithmic poles

Let `a : ℂ` and let `χ : ℂ → ℝ` be a compactly supported `C²` function that is equal to `1` on a
neighbourhood of `a`. The function `ψ t = χ t * log ‖t - a‖²` has a logarithmic pole at `a`, but
its Laplacian is a continuous compactly supported function (smooth when `χ` is), and

`∫ Δψ = -4π`.

This is the distributional identity `Δ log ‖· - a‖² = 4π δₐ` seen through the cutoff `χ`.

On a bounded open set `Ω ⊆ ℂ` this gives a Green-type identity for a function `h` with finitely
many logarithmic poles: if `h` is `C²` on `Ω` off a finite set `S ⊆ Ω`, constant near
`frontier Ω`, and near each `s ∈ S` equal to `c s * log ‖t - s‖²` plus a function `C²` at `s`,
then `Δh` is integrable on `Ω` and

`∫ t in Ω, Δh t = -4π ∑ s ∈ S, c s`.

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
* `SymplecticGeometry.integrableOn_laplacian_of_log_poles` and
  `SymplecticGeometry.setIntegral_laplacian_eq_of_log_poles`: the identity on `Ω`.

## Implementation notes

The integral is computed with a bump function `φ` that is `1` on a neighbourhood of the support of
`χ`. Green's second identity against `φ` (Tau Ceti's
`ContDiffOn.integral_laplacian_smul_eq_integral_smul_laplacian`) moves the Laplacian of the
`C²` function `(1 - χ) log ‖· - a‖²` onto `φ`; since `Δφ` vanishes where `χ ≠ 0`, what remains is
`∫ Δφ · log ‖· - a‖²`, which Tau Ceti's `integral_laplacian_mul_planarNewtonianKernel_sub`
evaluates, as `log ‖t - a‖² = -4π G(t - a)` for the planar Newtonian kernel `G`.

For the identity on `Ω`, each pole `s` is cut off by a bump function `χ s` supported in `Ω`. What
remains, `g = h - C - ∑ s, c s * χ s * log ‖· - s‖²` on `Ω` (with `C` the value of `h` near
`frontier Ω`), extended by `0`, is `C²` with compact support
(`SymplecticGeometry.exists_laplacian_ae_eq_add_sum_of_log_poles`), so Tau Ceti's
`integral_laplacian_eq_zero_of_hasCompactSupport` gives `∫ Δg = 0`, and the one-pole identity
gives the rest.

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

/-- If `χ` is equal to `1` near `a` and `C²` at `z`, then at `z` the Laplacian of
`χ log ‖· - a‖²` is minus that of `(1 - χ) log ‖· - a‖²`; `z` may be the pole `a`. -/
theorem laplacian_fun_mul_log_norm_sub_sq {a z : ℂ} {χ : ℂ → ℝ} (hχ : ContDiffAt ℝ 2 χ z)
    (hχa : χ =ᶠ[𝓝 a] 1) :
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
    have hsum := (hχ.mul hL).laplacian_add
      (((contDiffAt_const (c := (1 : ℝ))).sub hχ).mul hL)
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
  have h (z : ℂ) := laplacian_fun_mul_log_norm_sub_sq (z := z) h₂.contDiffAt hχa
  rw [funext h]
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
    have h := laplacian_fun_mul_log_norm_sub_sq (z := t) hχ.contDiffAt hχa
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

/-! ### Planar domains -/

section Domain

variable {Ω : Set ℂ} {S : Finset ℂ} {h c : ℂ → ℝ} {C : ℝ}

/-- Removing cut-off poles: if `χ s` is `C²` and equal to `1` near `s` for each `s ∈ S`, and `h` is
`C²` at `z ∉ S` and has a logarithmic pole with coefficient `c s` at each `s ∈ S`, then
`h - ∑ s ∈ S, c s * χ s · log ‖· - s‖²` is `C²` at `z`. -/
private theorem contDiffAt_sub_sum_mul_log_of_log_poles {z : ℂ} {χ : ℂ → ℂ → ℝ}
    (hχ : ∀ s ∈ S, ContDiff ℝ 2 (χ s)) (hχ₁ : ∀ s ∈ S, χ s =ᶠ[𝓝 s] 1)
    (hh : z ∉ S → ContDiffAt ℝ 2 h z)
    (hpole : ∀ s ∈ S, ∃ k : ℂ → ℝ, ContDiffAt ℝ 2 k s ∧
      ∀ᶠ t in 𝓝 s, h t = c s * Real.log (‖t - s‖ ^ 2) + k t) :
    ContDiffAt ℝ 2
      (fun t ↦ h t - ∑ s ∈ S, c s * (χ s t * Real.log (‖t - s‖ ^ 2))) z := by
  have hψ {s : ℂ} (hs : s ∈ S) (hz : z ≠ s) :
      ContDiffAt ℝ 2 (fun t ↦ c s * (χ s t * Real.log (‖t - s‖ ^ 2))) z :=
    contDiffAt_const.mul ((hχ s hs).contDiffAt.mul (contDiffAt_log_norm_sub_sq hz))
  by_cases hzS : z ∈ S
  · obtain ⟨k, hk, hkh⟩ := hpole z hzS
    have hsplit : (fun t ↦ h t - ∑ s ∈ S, c s * (χ s t * Real.log (‖t - s‖ ^ 2))) =
        fun t ↦ (h t - c z * (χ z t * Real.log (‖t - z‖ ^ 2))) -
          ∑ s ∈ S.erase z, c s * (χ s t * Real.log (‖t - s‖ ^ 2)) := by
      funext t
      rw [← Finset.add_sum_erase S _ hzS]
      ring
    have hloc : (fun t ↦ h t - c z * (χ z t * Real.log (‖t - z‖ ^ 2))) =ᶠ[𝓝 z]
        fun t ↦ k t + c z * ((1 - χ z t) * Real.log (‖t - z‖ ^ 2)) := by
      filter_upwards [hkh] with t ht
      rw [ht]
      ring
    rw [hsplit]
    exact ((hk.add (contDiffAt_const.mul (contDiff_one_sub_mul_log_norm_sub_sq (hχ z hzS)
      (hχ₁ z hzS)).contDiffAt)).congr_of_eventuallyEq hloc).sub (ContDiffAt.sum fun s hs ↦
        hψ (Finset.mem_of_mem_erase hs) (Finset.ne_of_mem_erase hs).symm)
  · exact (hh hzS).sub (ContDiffAt.sum fun s hs ↦ hψ hs fun h ↦ hzS (h ▸ hs))

/-- Under the hypotheses of `setIntegral_laplacian_eq_of_log_poles`, almost everywhere on `Ω`,
`Δh = Δg + ∑ s ∈ S, c s * Δ(χ s · log ‖· - s‖²)`, where `g` is `C²` with compact support and
`Δg` vanishes off `Ω`, and each `χ s` is `C²`, compactly supported in `Ω` and equal to `1` near
`s`. -/
theorem exists_laplacian_ae_eq_add_sum_of_log_poles (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hS : ↑S ⊆ Ω) (hh : ∀ z ∈ Ω \ ↑S, ContDiffAt ℝ 2 h z)
    (hC : ∀ᶠ t in 𝓝ˢ (frontier Ω), h t = C)
    (hpole : ∀ s ∈ S, ∃ k : ℂ → ℝ, ContDiffAt ℝ 2 k s ∧
      ∀ᶠ t in 𝓝 s, h t = c s * Real.log (‖t - s‖ ^ 2) + k t) :
    ∃ (g : ℂ → ℝ) (χ : ℂ → ℂ → ℝ), ContDiff ℝ 2 g ∧ HasCompactSupport g ∧
      (∀ t ∉ Ω, Δ g t = 0) ∧
      (∀ s ∈ S, ContDiff ℝ 2 (χ s) ∧ HasCompactSupport (χ s) ∧ χ s =ᶠ[𝓝 s] 1 ∧
        tsupport (χ s) ⊆ Ω) ∧
      Δ h =ᵐ[volume.restrict Ω]
        fun t ↦ Δ g t + ∑ s ∈ S, c s * Δ (fun t ↦ χ s t * Real.log (‖t - s‖ ^ 2)) t := by
  -- A bump function about each pole, supported in `Ω`.
  have hφ (s : ℂ) : ∃ φ : ContDiffBump s, s ∈ Ω → closedBall s φ.rOut ⊆ Ω := by
    by_cases hs : s ∈ Ω
    · obtain ⟨r, hr, hrΩ⟩ := nhds_basis_closedBall.mem_iff.mp (hΩ.mem_nhds hs)
      exact ⟨⟨r / 2, r, by positivity, by linarith⟩, fun _ ↦ hrΩ⟩
    · exact ⟨⟨1, 2, one_pos, one_lt_two⟩, fun h ↦ (hs h).elim⟩
  choose φ hφΩ using hφ
  set ψ : ℂ → ℂ → ℝ := fun s t ↦ φ s t * Real.log (‖t - s‖ ^ 2) with hψ
  have hψcd {s z : ℂ} (hz : z ≠ s) : ContDiffAt ℝ 2 (ψ s) z :=
    (φ s).contDiffAt.mul (contDiffAt_log_norm_sub_sq hz)
  have hψ0 {s t : ℂ} (ht : t ∉ closedBall s (φ s).rOut) : ψ s t = 0 := by
    simp only [hψ]
    rw [(φ s).zero_of_le_dist (not_le.mp ht).le, zero_mul]
  -- `G = h - C - ∑ c s ψ s`; it vanishes near `frontier Ω` and is `C²` on `Ω`.
  set G : ℂ → ℝ := fun t ↦ h t - C - ∑ s ∈ S, c s * ψ s t with hG
  have hGfront : ∀ᶠ t in 𝓝ˢ (frontier Ω), G t = 0 := by
    have hK : ∀ᶠ t in 𝓝ˢ (frontier Ω), ∀ s ∈ S, t ∉ closedBall s (φ s).rOut := by
      refine (eventually_all_finset S).mpr fun s hs ↦ ?_
      refine isClosed_closedBall.isOpen_compl.mem_nhdsSet.mpr fun t ht htB ↦ ?_
      rw [hΩ.frontier_eq] at ht
      exact ht.2 (hφΩ s (hS hs) htB)
    filter_upwards [hC, hK] with t ht htK
    simp only [hG]
    rw [ht, sub_self, zero_sub, neg_eq_zero]
    exact Finset.sum_eq_zero fun s hs ↦ by rw [hψ0 (htK s hs), mul_zero]
  have hGcd {z : ℂ} (hz : z ∈ Ω) : ContDiffAt ℝ 2 G z :=
    (contDiffAt_sub_sum_mul_log_of_log_poles (fun s _ ↦ (φ s).contDiff)
      (fun s _ ↦ (φ s).eventuallyEq_one) (fun hzS ↦ hh z ⟨hz, hzS⟩) hpole).sub
      contDiffAt_const |>.congr_of_eventuallyEq (Eventually.of_forall fun t ↦ by
        simp only [hG, hψ]
        ring)
  -- `g` is `G` on `Ω`, extended by `0`.
  set g : ℂ → ℝ := Ω.indicator G with hg
  have hgΩ {z : ℂ} (hz : z ∈ Ω) : g =ᶠ[𝓝 z] G := by
    filter_upwards [hΩ.mem_nhds hz] with t ht
    exact Set.indicator_of_mem ht G
  have hg0 {z : ℂ} (hz : z ∉ Ω) : g =ᶠ[𝓝 z] fun _ ↦ (0 : ℝ) := by
    by_cases hzc : z ∈ closure Ω
    · have hzf : z ∈ frontier Ω := by
        rw [hΩ.frontier_eq]
        exact ⟨hzc, hz⟩
      filter_upwards [hGfront.filter_mono (nhds_le_nhdsSet hzf)] with t ht
      by_cases htΩ : t ∈ Ω
      · rw [hg, Set.indicator_of_mem htΩ, ht]
      · exact Set.indicator_of_notMem htΩ G
    · filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hzc] with t ht
      exact Set.indicator_of_notMem (fun h ↦ ht (subset_closure h)) G
  have hgcd : ContDiff ℝ 2 g := by
    refine contDiff_iff_contDiffAt.mpr fun z ↦ ?_
    by_cases hz : z ∈ Ω
    · exact (hGcd hz).congr_of_eventuallyEq (hgΩ hz)
    · exact contDiffAt_const.congr_of_eventuallyEq (hg0 hz)
  refine ⟨g, fun s ↦ φ s, hgcd, ?_, fun t ht ↦ ?_, fun s hs ↦ ?_, ?_⟩
  · exact HasCompactSupport.intro hb.isCompact_closure fun t ht ↦
      Set.indicator_of_notMem (fun h ↦ ht (subset_closure h)) G
  · rw [(laplacian_congr_nhds (hg0 ht)).self_of_nhds, laplacian_const, Pi.zero_apply]
  · refine ⟨(φ s).contDiff, (φ s).hasCompactSupport, (φ s).eventuallyEq_one, ?_⟩
    rw [(φ s).tsupport_eq]
    exact hφΩ s (hS hs)
  · have hS0 : volume (S : Set ℂ) = 0 := S.finite_toSet.measure_zero _
    filter_upwards [ae_restrict_mem hΩ.measurableSet,
      ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp hS0)] with t ht₁ ht₂
    have ht : t ∈ Ω \ ↑S := ⟨ht₁, ht₂⟩
    -- On `Ω`, `h = g + C + ∑ c s ψ s`, and every term is `C²` at `t ∉ S`.
    have hloc : h =ᶠ[𝓝 t] (g + fun _ ↦ C) + ∑ s ∈ S, c s • ψ s := by
      filter_upwards [hgΩ ht.1] with t' ht'
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ht', hG]
      ring
    have hne : ∀ s ∈ S, t ≠ s := fun s hs hts ↦ ht.2 (Finset.mem_coe.mpr (hts ▸ hs))
    have hψt : ∀ s ∈ S, ContDiffAt ℝ 2 (c s • ψ s) t := fun s hs ↦ by
      rw [Pi.smul_def]
      exact (hψcd (hne s hs)).const_smul (c s)
    have h₁ : ContDiffAt ℝ 2 (g + fun _ ↦ C) t := by
      rw [Pi.add_def]
      exact hgcd.contDiffAt.add contDiffAt_const
    have h₂ : ContDiffAt ℝ 2 (∑ s ∈ S, c s • ψ s) t := by
      rw [Finset.sum_fn]
      exact ContDiffAt.sum hψt
    rw [(laplacian_congr_nhds hloc).self_of_nhds, h₁.laplacian_add h₂,
      hgcd.contDiffAt.laplacian_add contDiffAt_const, laplacian_const, Pi.zero_apply, add_zero,
      laplacian_sum hψt]
    refine congrArg _ (Finset.sum_congr rfl fun s hs ↦ ?_)
    rw [laplacian_smul _ (hψcd (hne s hs)), smul_eq_mul]

/-- **The integral of the Laplacian of a function with logarithmic poles**, integrability. Let
`Ω ⊆ ℂ` be bounded and open, `S ⊆ Ω` finite, and `h : ℂ → ℝ` be `C²` on `Ω \ S`, constant near
`frontier Ω`, and near each `s ∈ S` of the form `c s * log ‖t - s‖² + k t` with `k` `C²` at `s`.
Then `Δh` is integrable on `Ω`. -/
theorem integrableOn_laplacian_of_log_poles (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hS : ↑S ⊆ Ω) (hh : ∀ z ∈ Ω \ ↑S, ContDiffAt ℝ 2 h z)
    (hC : ∀ᶠ t in 𝓝ˢ (frontier Ω), h t = C)
    (hpole : ∀ s ∈ S, ∃ k : ℂ → ℝ, ContDiffAt ℝ 2 k s ∧
      ∀ᶠ t in 𝓝 s, h t = c s * Real.log (‖t - s‖ ^ 2) + k t) :
    IntegrableOn (Δ h) Ω := by
  obtain ⟨g, χ, hg, hgc, -, hχ, hae⟩ :=
    exists_laplacian_ae_eq_add_sum_of_log_poles hΩ hb hS hh hC hpole
  refine Integrable.congr (Integrable.integrableOn ?_) hae.symm
  exact ((hg.laplacian (m := 0) (by norm_num)).continuous.integrable_of_hasCompactSupport
    hgc.laplacian).add (integrable_finsetSum _ fun s hs ↦
      (integrable_laplacian_fun_mul_log_norm_sub_sq (hχ s hs).1 (hχ s hs).2.1
        (hχ s hs).2.2.1).const_mul _)

/-- **The integral of the Laplacian of a function with logarithmic poles.** Let `Ω ⊆ ℂ` be
bounded and open, `S ⊆ Ω` finite, and `h : ℂ → ℝ` be `C²` on `Ω \ S`, constant near
`frontier Ω`, and near each `s ∈ S` of the form `c s * log ‖t - s‖² + k t` with `k` `C²` at `s`.
Then `∫ t in Ω, Δh t = -4π ∑ s ∈ S, c s`. -/
theorem setIntegral_laplacian_eq_of_log_poles (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hS : ↑S ⊆ Ω) (hh : ∀ z ∈ Ω \ ↑S, ContDiffAt ℝ 2 h z)
    (hC : ∀ᶠ t in 𝓝ˢ (frontier Ω), h t = C)
    (hpole : ∀ s ∈ S, ∃ k : ℂ → ℝ, ContDiffAt ℝ 2 k s ∧
      ∀ᶠ t in 𝓝 s, h t = c s * Real.log (‖t - s‖ ^ 2) + k t) :
    ∫ t in Ω, Δ h t = -(4 * Real.pi) * ∑ s ∈ S, c s := by
  obtain ⟨g, χ, hg, hgc, hgΩ, hχ, hae⟩ :=
    exists_laplacian_ae_eq_add_sum_of_log_poles hΩ hb hS hh hC hpole
  have hI (s : ℂ) (hs : s ∈ S) :=
    integrable_laplacian_fun_mul_log_norm_sub_sq (hχ s hs).1 (hχ s hs).2.1 (hχ s hs).2.2.1
  have hpole (s : ℂ) (hs : s ∈ S) :
      ∫ t in Ω, c s * Δ (fun t ↦ χ s t * Real.log (‖t - s‖ ^ 2)) t = c s * -(4 * Real.pi) := by
    rw [integral_const_mul, setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht ↦
        laplacian_of_notMem_tsupport fun h ↦ ht ((hχ s hs).2.2.2 (tsupport_mul_subset_left h)),
      integral_laplacian_fun_mul_log_norm_sub_sq (hχ s hs).1 (hχ s hs).2.1 (hχ s hs).2.2.1]
  rw [integral_congr_ae hae,
    integral_add ((hg.laplacian (m := 0) (by norm_num)).continuous.integrable_of_hasCompactSupport
      hgc.laplacian).integrableOn
      (integrable_finsetSum _ fun s hs ↦ (hI s hs).const_mul _).integrableOn,
    integral_finsetSum _ fun s hs ↦ ((hI s hs).const_mul _).integrableOn,
    setIntegral_eq_integral_of_forall_compl_eq_zero hgΩ,
    integral_laplacian_eq_zero_of_hasCompactSupport hg hgc, Finset.sum_congr rfl hpole,
    ← Finset.sum_mul]
  ring

end Domain

end SymplecticGeometry

end
