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

A bump function `χ` equal to `1` near `w` and supported inside the disc splits `f` as
`χ f + (1 - χ) f`. The first piece is compactly supported and `C¹`, so Tau Ceti's Cauchy–Pompeiu
formula for compactly supported maps (`HasCompactSupport.cauchyTransform_conjWirtingerDeriv`)
recovers `f w = (χ f)(w)` from its `\bar∂`. The second piece vanishes near `w`, so
`(z - w)⁻¹ (1 - χ) f` is `C¹` near the closed disc, and Tau Ceti's Green formula
(`TauCeti.integral_ball_conjWirtingerDeriv_eq_circleIntegral`) turns the area integral of its
`\bar∂`, which is `(z - w)⁻¹ \bar∂((1 - χ) f)`, into its circle integral, where `χ = 0`.

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

/-- A function continuous on a compact subset `K` of the plane stays integrable on `K` after
multiplication by the Cauchy kernel `(w - z)⁻¹`, which is locally integrable. -/
theorem ContinuousOn.integrableOn_sub_inv_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {g : ℂ → E} {K : Set ℂ} (hg : ContinuousOn g K) (hK : IsCompact K) (w : ℂ) :
    IntegrableOn (fun z ↦ (w - z)⁻¹ • g z) K :=
  ((locallyIntegrable_sub_inv w).integrableOn_isCompact hK).smul_continuousOn hg hK

namespace SymplecticGeometry

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {f : ℂ → F} {c w : ℂ} {r : ℝ}

/-- **The Cauchy–Pompeiu formula on a disc.** For `f : ℂ → F` real `C¹` near the closed disc
`|z - c| ≤ r` and `w` in the open disc, `f w` is the sum of the boundary Cauchy integral
`(2 π i)⁻¹ ∮_{|z - c| = r} (z - w)⁻¹ f(z) dz` and the area term
`π⁻¹ ∫_{|z - c| < r} (w - z)⁻¹ \bar∂f(z) dA`. -/
theorem two_pi_I_inv_smul_circleIntegral_add_pi_inv_smul_integral_ball
    (hf : ∀ z ∈ closedBall c r, ContDiffAt ℝ 1 f z) (hw : w ∈ ball c r) :
    ((2 * π * I : ℂ)⁻¹ • ∮ z in C(c, r), (z - w)⁻¹ • f z) +
      (π : ℂ)⁻¹ • ∫ z in ball c r, (w - z)⁻¹ • conjWirtingerDeriv f z 1 = f w := by
  -- A bump function `χ`, equal to `1` on `closedBall w δ` and supported in `closedBall w (2δ)`,
  -- which lies in the open disc.
  obtain ⟨δ, hδ, hsub⟩ : ∃ δ > 0, closedBall w (2 * δ) ⊆ ball c r := by
    have := mem_ball.1 hw
    exact ⟨(r - dist w c) / 3, by linarith, closedBall_subset_ball' (by linarith)⟩
  let χb : ContDiffBump w := ⟨δ, 2 * δ, hδ, by linarith⟩
  let χ : ℂ → ℂ := fun z ↦ (χb z : ℂ)
  have hχd : ContDiff ℝ 1 χ := ofRealCLM.contDiff.comp χb.contDiff
  have hχ0 {z : ℂ} (hz : z ∉ ball c r) : χ =ᶠ[𝓝 z] fun _ ↦ 0 := by
    have : z ∉ tsupport χb := by rw [χb.tsupport_eq]; exact fun h ↦ hz (hsub h)
    filter_upwards [notMem_tsupport_iff_eventuallyEq.1 this] with y hy
    simp [χ, hy]
  have hχ1 : ∀ᶠ y in 𝓝 w, χ y = 1 := by
    filter_upwards [ball_mem_nhds w hδ] with y hy
    simp [χ, χb.one_of_mem_closedBall (ball_subset_closedBall hy)]
  have hfd {z : ℂ} (hz : z ∈ ball c r) : DifferentiableAt ℝ f z :=
    (hf z (ball_subset_closedBall hz)).differentiableAt one_ne_zero
  -- The piece `u = χ f` near `w`: compactly supported and `C¹`.
  set u : ℂ → F := fun z ↦ χ z • f z
  have hu0 {z : ℂ} (hz : z ∉ ball c r) : u =ᶠ[𝓝 z] fun _ ↦ 0 := by
    filter_upwards [hχ0 hz] with y hy
    simp [u, hy]
  have hu : ContDiff ℝ 1 u := contDiff_iff_contDiffAt.2 fun z ↦ by
    by_cases hz : z ∈ ball c r
    · exact hχd.contDiffAt.smul (hf z (ball_subset_closedBall hz))
    · exact contDiffAt_const.congr_of_eventuallyEq (hu0 hz)
  have huc : HasCompactSupport u :=
    (HasCompactSupport.comp_left χb.hasCompactSupport ofReal_zero).smul_right
  have huw : u w = f w := by simp [u, hχ1.self_of_nhds]
  have hdu0 {z : ℂ} (hz : z ∉ ball c r) : conjWirtingerDeriv u z 1 = 0 := by
    rw [(hu0 hz).conjWirtingerDeriv_eq, (differentiableAt_const (0 : F)).conjWirtingerDeriv_eq_zero]
    simp
  -- The Cauchy–Pompeiu formula for `u`, with the integral over the disc.
  have hU : (π : ℂ)⁻¹ • ∫ z in ball c r, (w - z)⁻¹ • conjWirtingerDeriv u z 1 = f w := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦ by simp [hdu0 hz],
      ← cauchyTransform_apply, huc.cauchyTransform_conjWirtingerDeriv hu, huw]
  -- The piece `v = (1 - χ) f` away from `w`: it vanishes on `ball w δ`.
  set v : ℂ → F := f - u
  have hv0 {z : ℂ} (hz : z ∈ ball w δ) : v =ᶠ[𝓝 z] fun _ ↦ 0 := by
    filter_upwards [isOpen_ball.mem_nhds hz] with y hy
    simp [v, u, χ, χb.one_of_mem_closedBall (ball_subset_closedBall hy)]
  have hvc {z : ℂ} (hz : z ∈ closedBall c r) : ContDiffAt ℝ 1 v z := (hf z hz).sub hu.contDiffAt
  have hdv {z : ℂ} (hz : z ∈ ball c r) :
      conjWirtingerDeriv v z 1 = conjWirtingerDeriv f z 1 - conjWirtingerDeriv u z 1 := by
    rw [conjWirtingerDeriv_sub (hfd hz) (hu.differentiable one_ne_zero z)]
    exact sub_apply _ _ _
  -- Green's formula for `h z = (z - w)⁻¹ • v z`, which is `C¹` near the closed disc.
  set h : ℂ → F := fun z ↦ (z - w)⁻¹ • v z
  have hh0 {z : ℂ} (hz : z ∈ ball w δ) : h =ᶠ[𝓝 z] fun _ ↦ 0 := by
    filter_upwards [hv0 hz] with y hy
    simp [h, hy]
  have hk {z : ℂ} (hz : z ∉ ball w δ) : ContDiffAt ℝ 1 (fun y : ℂ ↦ (y - w)⁻¹) z := by
    have hzw : z - w ≠ 0 := sub_ne_zero.2 fun h ↦ hz (h ▸ mem_ball_self hδ)
    exact ((contDiffAt_id.sub contDiffAt_const).inv hzw)
  have hhc : ∀ z ∈ closedBall c r, ContDiffAt ℝ 1 h z := fun z hz ↦ by
    by_cases hzw : z ∈ ball w δ
    · exact contDiffAt_const.congr_of_eventuallyEq (hh0 hzw)
    · exact (hk hzw).smul (hvc hz)
  have hdh {z : ℂ} (hz : z ∈ ball c r) :
      conjWirtingerDeriv h z 1 = (z - w)⁻¹ • conjWirtingerDeriv v z 1 := by
    by_cases hzw : z ∈ ball w δ
    · rw [(hh0 hzw).conjWirtingerDeriv_eq, (hv0 hzw).conjWirtingerDeriv_eq,
        (differentiableAt_const (0 : F)).conjWirtingerDeriv_eq_zero]
      simp
    · have hkd : DifferentiableAt ℂ (fun y : ℂ ↦ (y - w)⁻¹) z :=
        (differentiableAt_id.sub_const w).inv
          (sub_ne_zero.2 fun h ↦ hzw (h ▸ mem_ball_self hδ))
      rw [conjWirtingerDeriv_smul_apply (hkd.restrictScalars ℝ)
        ((hvc (ball_subset_closedBall hz)).differentiableAt one_ne_zero),
        hkd.conjWirtingerDeriv_eq_zero]
      simp
  have hr : 0 ≤ r := dist_nonneg.trans (mem_ball.1 hw).le
  have hG := integral_ball_conjWirtingerDeriv_eq_circleIntegral hr hhc
  -- On the boundary circle `χ = 0`, so `h z = (z - w)⁻¹ • f z` there.
  have hcirc : (∮ z in C(c, r), h z) = ∮ z in C(c, r), (z - w)⁻¹ • f z :=
    circleIntegral.integral_congr hr fun z hz ↦ by
      have : z ∉ ball c r := by simp [mem_sphere.1 hz]
      simp [h, v, u, (hχ0 this).self_of_nhds]
  -- Split the area term of `f` into those of `u` and `v`.
  have hint {g : ℂ → F} (hg : ∀ z ∈ closedBall c r, ContDiffAt ℝ 1 g z) :
      IntegrableOn (fun z ↦ (w - z)⁻¹ • conjWirtingerDeriv g z 1) (ball c r) := by
    have hc : ContinuousOn (fun z ↦ conjWirtingerDeriv g z 1) (closedBall c r) :=
      continuousOn_of_forall_continuousAt fun z hz ↦
        ((hg z hz).conjWirtingerDeriv_apply (m := 0) (by simp) 1).continuousAt
    exact (hc.integrableOn_sub_inv_smul (isCompact_closedBall c r) w).mono_set
      ball_subset_closedBall
  have hsplit : ∫ z in ball c r, (w - z)⁻¹ • conjWirtingerDeriv f z 1 =
      (∫ z in ball c r, (w - z)⁻¹ • conjWirtingerDeriv u z 1) -
        ∫ z in ball c r, conjWirtingerDeriv h z 1 := by
    rw [sub_eq_add_neg, ← integral_neg, ← integral_add (hint fun z _ ↦ hu.contDiffAt)
      ((hint fun z hz ↦ hvc hz).congr_fun (fun z hz ↦ ?_) measurableSet_ball)]
    · refine setIntegral_congr_fun measurableSet_ball fun z hz ↦ ?_
      simp only [hdh hz, hdv hz, smul_sub, ← neg_sub z w, inv_neg, neg_smul]
      abel
    · simp only [hdh hz, ← neg_sub w z, inv_neg, neg_smul, neg_neg]
  rw [hsplit, smul_sub, hU, hG, hcirc, smul_smul,
    show (π : ℂ)⁻¹ * (2 * I)⁻¹ = (2 * π * I)⁻¹ by ring]
  abel

/-- **A map with small `\bar∂` is close to its boundary Cauchy integral.** If `f : ℂ → F` is
real `C¹` near the closed disc `|z - c| ≤ r` and `‖\bar∂f‖ ≤ ε` on the open disc, then at every
point `w` of the open disc `f w` is within `4 r ε` of the boundary Cauchy integral
`(2 π i)⁻¹ ∮_{|z - c| = r} (z - w)⁻¹ f(z) dz`. -/
theorem norm_sub_two_pi_I_inv_smul_circleIntegral_le
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
