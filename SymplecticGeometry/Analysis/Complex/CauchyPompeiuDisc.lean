/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import TauCeti.Analysis.Complex.Wirtinger.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import TauCeti.Analysis.Complex.Pompeiu.Basic
import TauCeti.Analysis.Complex.Pompeiu.Holder.Basic
import TauCeti.Analysis.Complex.Wirtinger.Green

/-!
# The Cauchy–Pompeiu formula on a disc

For a map `f : ℂ → F` into a complex Banach space that is real `C¹` near the closed disc
`|z - c| ≤ r`, and a point `w` of the open disc, the **Cauchy–Pompeiu formula** writes `f w` as
the Cauchy integral of `f` over the boundary circle plus the Cauchy transform of `\bar∂f` over
the disc:

`f w = (2 π i)⁻¹ ∮_{|z - c| = r} (z - w)⁻¹ f(z) dz + π⁻¹ ∫_{|z - c| < r} (w - z)⁻¹ \bar∂f(z) dA`.

The area term has the normalization of Tau Ceti's `TauCeti.cauchyTransform`. When `f` is
holomorphic it vanishes, and the formula is Cauchy's integral formula. When `‖\bar∂f‖ ≤ ε` on the
disc, the area term has norm at most `4 r ε`, so `f` is then within `4 r ε` of the boundary Cauchy
integral, which is holomorphic in `w`.

## Proof

The formula is first proved for two kinds of maps.

* For a `C¹` map `u` whose support lies in the open disc, the circle term vanishes, and the
  formula is Tau Ceti's Cauchy–Pompeiu formula for compactly supported maps
  (`HasCompactSupport.cauchyTransform_conjWirtingerDeriv`).
* For a map `v` that vanishes near `w`, the map `(z - w)⁻¹ v` is `C¹` near the closed disc, and
  Tau Ceti's Green formula (`TauCeti.integral_ball_conjWirtingerDeriv_eq_circleIntegral`) turns
  the area integral of its `\bar∂`, which is `(z - w)⁻¹ \bar∂v`, into its circle integral.

A bump function `χ` equal to `1` near `w` and supported inside the disc then splits `f` as
`χ f + (1 - χ) f`, one map of each kind.

## Main results

* `SymplecticGeometry.two_pi_I_inv_smul_circleIntegral_add_pi_inv_smul_integral_ball`: the
  Cauchy–Pompeiu formula on a disc.
* `SymplecticGeometry.norm_sub_two_pi_I_inv_smul_circleIntegral_le`: `f` is within `4 r ε` of
  its boundary Cauchy integral on the disc when `‖\bar∂f‖ ≤ ε` there.

## References

* [P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, §0.1][GriffithsHarris1978]
-/

public section

open Complex Metric MeasureTheory Set Filter Topology TauCeti
open scoped Real

namespace SymplecticGeometry

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {c w : ℂ} {r : ℝ}

/-- For `g : ℂ → F` real `C¹` near the closed disc `|z - c| ≤ r`, the product
`(w - z)⁻¹ • \bar∂g(z)` of `\bar∂g` with the Cauchy kernel is integrable on the open disc. -/
theorem integrableOn_ball_sub_inv_smul_conjWirtingerDeriv {g : ℂ → F}
    (hg : ∀ z ∈ closedBall c r, ContDiffAt ℝ 1 g z) (w : ℂ) :
    IntegrableOn (fun z ↦ (w - z)⁻¹ • conjWirtingerDeriv g z 1) (ball c r) := by
  have hc : ContinuousOn (fun z ↦ conjWirtingerDeriv g z 1) (closedBall c r) :=
    continuousOn_of_forall_continuousAt fun z hz ↦
      ((hg z hz).conjWirtingerDeriv_apply (m := 0) (by simp) 1).continuousAt
  exact (((locallyIntegrable_sub_inv w).integrableOn_isCompact
    (isCompact_closedBall c r)).smul_continuousOn hc (isCompact_closedBall c r)).mono_set
    ball_subset_closedBall

/-- **The Cauchy–Pompeiu formula for a map vanishing near the point.** If `v : ℂ → F` is real
`C¹` near the closed disc `|z - c| ≤ r`, with `0 ≤ r`, and vanishes near `w`, then the boundary
Cauchy integral `(2 π i)⁻¹ ∮_{|z - c| = r} (z - w)⁻¹ v(z) dz` and the area term
`π⁻¹ ∫_{|z - c| < r} (w - z)⁻¹ \bar∂v(z) dA` sum to `0`. -/
theorem two_pi_I_inv_smul_circleIntegral_add_pi_inv_smul_integral_ball_of_eventuallyEq_zero
    {v : ℂ → F} (hr : 0 ≤ r) (hv : ∀ z ∈ closedBall c r, ContDiffAt ℝ 1 v z)
    (hv0 : v =ᶠ[𝓝 w] 0) :
    ((2 * π * I : ℂ)⁻¹ • ∮ z in C(c, r), (z - w)⁻¹ • v z) +
      (π : ℂ)⁻¹ • ∫ z in ball c r, (w - z)⁻¹ • conjWirtingerDeriv v z 1 = 0 := by
  obtain ⟨δ, hδ, hδv⟩ := Metric.mem_nhds_iff.1 hv0
  have hv0' {z : ℂ} (hz : z ∈ ball w δ) : v =ᶠ[𝓝 z] fun _ ↦ 0 :=
    Filter.mem_of_superset (isOpen_ball.mem_nhds hz) fun _ hy ↦ hδv hy
  -- Green's formula for `h z = (z - w)⁻¹ • v z`, which is `C¹` near the closed disc.
  set h : ℂ → F := fun z ↦ (z - w)⁻¹ • v z
  have hh0 {z : ℂ} (hz : z ∈ ball w δ) : h =ᶠ[𝓝 z] fun _ ↦ 0 := by
    filter_upwards [hv0' hz] with y hy
    simp [h, hy]
  have hzw {z : ℂ} (hz : z ∉ ball w δ) : z - w ≠ 0 :=
    sub_ne_zero.2 fun h ↦ hz (h ▸ mem_ball_self hδ)
  have hhc : ∀ z ∈ closedBall c r, ContDiffAt ℝ 1 h z := fun z hz ↦ by
    by_cases hz' : z ∈ ball w δ
    · exact contDiffAt_const.congr_of_eventuallyEq (hh0 hz')
    · exact ((contDiffAt_id.sub contDiffAt_const).inv (hzw hz')).smul (hv z hz)
  have hdh {z : ℂ} (hz : z ∈ ball c r) :
      (w - z)⁻¹ • conjWirtingerDeriv v z 1 = -conjWirtingerDeriv h z 1 := by
    rw [← neg_sub z w, inv_neg, neg_smul, neg_inj]
    by_cases hz' : z ∈ ball w δ
    · rw [(hh0 hz').conjWirtingerDeriv_eq, (hv0' hz').conjWirtingerDeriv_eq,
        (differentiableAt_const (0 : F)).conjWirtingerDeriv_eq_zero]
      simp
    · have hkd : DifferentiableAt ℂ (fun y : ℂ ↦ (y - w)⁻¹) z :=
        (differentiableAt_id.sub_const w).inv (hzw hz')
      rw [conjWirtingerDeriv_smul_apply (hkd.restrictScalars ℝ)
        ((hv z (ball_subset_closedBall hz)).differentiableAt one_ne_zero),
        hkd.conjWirtingerDeriv_eq_zero]
      simp
  rw [setIntegral_congr_fun measurableSet_ball fun z hz ↦ hdh hz, integral_neg,
    integral_ball_conjWirtingerDeriv_eq_circleIntegral hr hhc, smul_neg, smul_smul,
    show (π : ℂ)⁻¹ * (2 * I)⁻¹ = (2 * π * I)⁻¹ by ring]
  exact add_neg_cancel _

variable [CompleteSpace F]

/-- **The Cauchy–Pompeiu formula for a map supported in the disc.** If `u : ℂ → F` is real `C¹`
and its topological support lies in the open disc `|z - c| < r`, then for every `w`,
`u w = π⁻¹ ∫_{|z - c| < r} (w - z)⁻¹ \bar∂u(z) dA`. -/
theorem pi_inv_smul_integral_ball_sub_inv_smul_conjWirtingerDeriv_of_tsupport_subset
    {u : ℂ → F} (hu : ContDiff ℝ 1 u) (hsupp : tsupport u ⊆ ball c r) (w : ℂ) :
    (π : ℂ)⁻¹ • ∫ z in ball c r, (w - z)⁻¹ • conjWirtingerDeriv u z 1 = u w := by
  have huc : HasCompactSupport u :=
    (isCompact_closedBall c r).of_isClosed_subset (isClosed_tsupport u)
      (hsupp.trans ball_subset_closedBall)
  have hdu0 {z : ℂ} (hz : z ∉ ball c r) : conjWirtingerDeriv u z 1 = 0 := by
    rw [conjWirtingerDeriv_of_notMem_tsupport fun h ↦ hz (hsupp h), zero_apply]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦ by simp [hdu0 hz],
    ← cauchyTransform_apply, huc.cauchyTransform_conjWirtingerDeriv hu]

/-- **The Cauchy–Pompeiu formula on a disc.** For `f : ℂ → F` real `C¹` near the closed disc
`|z - c| ≤ r` and `w` in the open disc, `f w` is the sum of the boundary Cauchy integral
`(2 π i)⁻¹ ∮_{|z - c| = r} (z - w)⁻¹ f(z) dz` and the area term
`π⁻¹ ∫_{|z - c| < r} (w - z)⁻¹ \bar∂f(z) dA`. -/
theorem two_pi_I_inv_smul_circleIntegral_add_pi_inv_smul_integral_ball {f : ℂ → F}
    (hf : ∀ z ∈ closedBall c r, ContDiffAt ℝ 1 f z) (hw : w ∈ ball c r) :
    ((2 * π * I : ℂ)⁻¹ • ∮ z in C(c, r), (z - w)⁻¹ • f z) +
      (π : ℂ)⁻¹ • ∫ z in ball c r, (w - z)⁻¹ • conjWirtingerDeriv f z 1 = f w := by
  -- A bump function `χ`, equal to `1` on `closedBall w δ` and supported in `closedBall w (2δ)`,
  -- which lies in the open disc.
  obtain ⟨δ, hδ, hsub⟩ : ∃ δ > 0, closedBall w (2 * δ) ⊆ ball c r := by
    have := mem_ball.1 hw
    exact ⟨(r - dist w c) / 3, by linarith, closedBall_subset_ball' (by linarith)⟩
  let χb : ContDiffBump w := ⟨δ, 2 * δ, hδ, by linarith⟩
  have hχ1 : ∀ᶠ y in 𝓝 w, χb y = 1 := by
    filter_upwards [ball_mem_nhds w hδ] with y hy
    exact χb.one_of_mem_closedBall (ball_subset_closedBall hy)
  -- `f = u + v`, with `u = χ f` supported in the disc and `v = (1 - χ) f` vanishing near `w`.
  set u : ℂ → F := fun z ↦ (χb z : ℂ) • f z
  have hsupp : tsupport u ⊆ ball c r := by
    have : tsupport (fun z ↦ (χb z : ℂ)) ⊆ tsupport χb := tsupport_comp_subset ofReal_zero _
    exact (tsupport_smul_subset_left _ _).trans (this.trans (χb.tsupport_eq ▸ hsub))
  have hu : ContDiff ℝ 1 u := contDiff_iff_contDiffAt.2 fun z ↦ by
    by_cases hz : z ∈ ball c r
    · exact (ofRealCLM.contDiff.comp χb.contDiff).contDiffAt.smul
        (hf z (ball_subset_closedBall hz))
    · exact contDiffAt_const.congr_of_eventuallyEq
        (notMem_tsupport_iff_eventuallyEq.1 fun h ↦ hz (hsupp h))
  set v : ℂ → F := f - u
  have hvc : ∀ z ∈ closedBall c r, ContDiffAt ℝ 1 v z := fun z hz ↦
    (hf z hz).sub hu.contDiffAt
  have hv0 : v =ᶠ[𝓝 w] 0 := by
    filter_upwards [hχ1] with y hy
    simp [v, u, hy]
  have hr : 0 ≤ r := dist_nonneg.trans (mem_ball.1 hw).le
  have hV := two_pi_I_inv_smul_circleIntegral_add_pi_inv_smul_integral_ball_of_eventuallyEq_zero
    hr hvc hv0
  -- On the boundary circle `u = 0`, so the circle integrals of `f` and `v` agree.
  have hcirc : (∮ z in C(c, r), (z - w)⁻¹ • v z) = ∮ z in C(c, r), (z - w)⁻¹ • f z :=
    circleIntegral.integral_congr hr fun z hz ↦ by
      have : z ∉ tsupport u := fun h ↦ by simpa [mem_sphere.1 hz] using hsupp h
      simp [v, image_eq_zero_of_notMem_tsupport this]
  -- The area term of `f` is the sum of those of `u` and `v`.
  have hsplit : ∫ z in ball c r, (w - z)⁻¹ • conjWirtingerDeriv f z 1 =
      (∫ z in ball c r, (w - z)⁻¹ • conjWirtingerDeriv u z 1) +
        ∫ z in ball c r, (w - z)⁻¹ • conjWirtingerDeriv v z 1 := by
    rw [← integral_add (integrableOn_ball_sub_inv_smul_conjWirtingerDeriv
      (fun z _ ↦ hu.contDiffAt) w) (integrableOn_ball_sub_inv_smul_conjWirtingerDeriv hvc w)]
    refine setIntegral_congr_fun measurableSet_ball fun z hz ↦ ?_
    have hdv : conjWirtingerDeriv v z 1 =
        conjWirtingerDeriv f z 1 - conjWirtingerDeriv u z 1 := by
      rw [conjWirtingerDeriv_sub ((hf z (ball_subset_closedBall hz)).differentiableAt
        one_ne_zero) (hu.differentiable one_ne_zero z)]
      exact sub_apply _ _ _
    simp only [hdv, ← smul_add, add_sub_cancel]
  rw [hsplit, smul_add,
    pi_inv_smul_integral_ball_sub_inv_smul_conjWirtingerDeriv_of_tsupport_subset hu hsupp w,
    ← hcirc, add_left_comm, hV, add_zero]
  simp [u, hχ1.self_of_nhds]

/-- **A map with small `\bar∂` is close to its boundary Cauchy integral.** If `f : ℂ → F` is
real `C¹` near the closed disc `|z - c| ≤ r` and `‖\bar∂f‖ ≤ ε` on the open disc, then at every
point `w` of the open disc `f w` is within `4 r ε` of the boundary Cauchy integral
`(2 π i)⁻¹ ∮_{|z - c| = r} (z - w)⁻¹ f(z) dz`. -/
theorem norm_sub_two_pi_I_inv_smul_circleIntegral_le {f : ℂ → F}
    (hf : ∀ z ∈ closedBall c r, ContDiffAt ℝ 1 f z) (hw : w ∈ ball c r) {ε : ℝ}
    (hε : ∀ z ∈ ball c r, ‖conjWirtingerDeriv f z 1‖ ≤ ε) :
    ‖f w - (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, r), (z - w)⁻¹ • f z‖ ≤ 4 * r * ε := by
  have hr : 0 ≤ r := dist_nonneg.trans (mem_ball.1 hw).le
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hε w hw)
  rw [← two_pi_I_inv_smul_circleIntegral_add_pi_inv_smul_integral_ball hf hw, add_sub_cancel_left,
    ← integral_indicator measurableSet_ball]
  simp_rw [indicator_smul_apply]
  calc _ ≤ 2 * (r + r) * ε := norm_pi_inv_smul_integral_sub_inv_smul_le hr hr
        ((support_indicator_subset).trans ball_subset_closedBall)
        (fun z ↦ by by_cases hz : z ∈ ball c r <;> simp [hz, hε, hε0])
        (ball_subset_closedBall hw)
    _ = 4 * r * ε := by ring

end SymplecticGeometry

end
