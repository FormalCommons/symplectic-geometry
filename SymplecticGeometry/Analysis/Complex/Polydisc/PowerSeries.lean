/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Analytic.Constructions
public import TauCeti.Analysis.Analytic.MultiIndex.Coeff
public import TauCeti.Analysis.Complex.PowerSeries.Polydisc
import Mathlib.Analysis.Calculus.FDeriv.Pi

/-!
# Power series of holomorphic functions on polydiscs

On `ι → ℂ`, for a finite type `ι`, the balls of the sup norm are the polydiscs with equal radii.
This file shows that a function holomorphic on such a polydisc has a power series about its
centre on every smaller concentric polydisc.

## Main results

* `DifferentiableOn.exists_hasFPowerSeriesOnBall_of_lt`: a function holomorphic on the polydisc
  `ball c R` has a power series about `c` on `ball c r` for every `0 < r < R`. The power series
  comes from the multivariate Cauchy expansion of Tau Ceti
  (`ContinuousOn.hasSum_torusIntegral_cauchyCoeff`, with the coefficient bound
  `TauCeti.norm_torusIntegral_cauchyCoeff_le`).

The proof adapts those of Tau Ceti's `DifferentiableOn.exists_differentiable_norm_sub_lt_of_pi`
and of the private lemma `TauCeti.exists_differentiable_norm_sub_lt_of_fin` behind it
(`TauCeti/Analysis/Complex/PowerSeries/Polydisc.lean`): the same Cauchy expansion on a closed
polydisc of intermediate radius, and the same transport from `Fin n → ℂ` to `ι → ℂ`, here
feeding `TauCeti.exists_hasFPowerSeriesOnBall_of_hasSum` instead of a uniform limit. The
transport uses Tau Ceti's `HasFPowerSeriesOnBall.compLinearIsometry`.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, §2.2.
-/

public section

open Complex Metric Real
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The case `ι = Fin n` of `DifferentiableOn.exists_hasFPowerSeriesOnBall_of_lt`: the power
series is the multivariate Cauchy expansion on a closed polydisc of intermediate radius. -/
private theorem DifferentiableOn.exists_hasFPowerSeriesOnBall_of_lt_of_fin [CompleteSpace E]
    {n : ℕ} {h : (Fin n → ℂ) → E} {c : Fin n → ℂ} {R : ℝ} (hh : DifferentiableOn ℂ h (ball c R))
    {r : ℝ≥0} (hr : 0 < r) (hrR : (r : ℝ) < R) :
    ∃ p : FormalMultilinearSeries ℂ (Fin n → ℂ) E, HasFPowerSeriesOnBall h p c r := by
  -- Expand on the closed polydisc of radius `s`, `r < s < R`, which lies in `ball c R`.
  set s : ℝ := (r + R) / 2
  have hrs : (r : ℝ) < s := by simp only [s]; linarith
  have hs : 0 < s := (NNReal.coe_pos.2 hr).trans hrs
  have hsub : (Set.univ.pi fun i ↦ closedBall (c i) s) ⊆ ball c R := fun z hz ↦
    mem_ball.2 <| ((dist_pi_le_iff hs.le).2 fun i ↦ hz i trivial).trans_lt
      (by simp only [s]; linarith)
  have hcont : ContinuousOn h (Set.univ.pi fun i ↦ closedBall (c i) s) :=
    hh.continuousOn.mono hsub
  obtain ⟨M, hM⟩ :=
    (isCompact_univ_pi fun i ↦ isCompact_closedBall (c i) s).exists_bound_of_continuousOn hcont
  have hd : ∀ z ∈ Set.univ.pi (fun i ↦ closedBall (c i) s), ∀ i, z i ∈ ball (c i) s →
      DifferentiableAt ℂ (fun x ↦ h (Function.update z i x)) (z i) := fun z hz i _ ↦ by
    refine DifferentiableAt.comp (z i) ?_ (hasFDerivAt_update z (z i)).differentiableAt
    rw [Function.update_eq_self i z]
    exact hh.differentiableAt (isOpen_ball.mem_nhds (hsub hz))
  have hq : Summable (fun α : Fin n → ℕ ↦ ∏ i, ((r : ℝ) / s) ^ α i) :=
    (TauCeti.hasSum_prod_geometric_of_norm_lt_one (r := fun _ ↦ (r : ℝ) / s) fun _ ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact (div_lt_one hs).2 hrs).summable
  refine (TauCeti.exists_hasFPowerSeriesOnBall_of_hasSum (f := h) (x := c)
    (c := fun α ↦ (2 * π * I : ℂ)⁻¹ ^ n •
      ∯ z in T(c, fun _ ↦ s), (∏ i, (z i - c i) ^ (α i + 1))⁻¹ • h z) hr ?_
    fun y hy ↦ ?_).imp fun _ hp ↦ hp.1
  · refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun α ↦ ?_) (hq.mul_left M)
    have hb := TauCeti.norm_torusIntegral_cauchyCoeff_le (f := h) (c := c) (M := M)
      (fun _ ↦ hs) (fun z hz ↦ hM z fun i _ ↦ sphere_subset_closedBall (hz i trivial)) α
    calc _ ≤ (M * ∏ i, s⁻¹ ^ α i) * (r : ℝ) ^ ∑ i, α i := by gcongr
      _ = M * ∏ i, ((r : ℝ) / s) ^ α i := by
        rw [mul_assoc, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
        simp only [← mul_pow, div_eq_mul_inv, mul_comm]
  · exact hcont.hasSum_torusIntegral_cauchyCoeff hd fun i ↦
      (norm_le_pi_norm y i).trans_lt (hy.trans hrs)


/-- A function holomorphic on the polydisc `ball c R` of `ι → ℂ`, a ball for the sup norm, has
a power series about `c` on the polydisc `ball c r` for every `0 < r < R`. -/
theorem DifferentiableOn.exists_hasFPowerSeriesOnBall_of_lt [CompleteSpace E] {ι : Type*}
    [Fintype ι] {h : (ι → ℂ) → E} {c : ι → ℂ} {R : ℝ} (hh : DifferentiableOn ℂ h (ball c R))
    {r : ℝ≥0} (hr : 0 < r) (hrR : (r : ℝ) < R) :
    ∃ p : FormalMultilinearSeries ℂ (ι → ℂ) E, HasFPowerSeriesOnBall h p c r := by
  -- Transport to `Fin n → ℂ` along the complex-linear isometry `L x = x ∘ e.symm` given by an
  -- enumeration `e` of `ι`.
  let e := Fintype.equivFin ι
  let L := ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : Fin (Fintype.card ι) ↦ ℂ) e
  have hL (x y : ι → ℂ) : dist (L x) (L y) = dist x y :=
    (IsometryEquiv.piCongrLeft (Y := fun _ : Fin (Fintype.card ι) ↦ ℂ) e).dist_eq x y
  obtain ⟨p, hp⟩ := DifferentiableOn.exists_hasFPowerSeriesOnBall_of_lt_of_fin (c := L c)
    (h := h ∘ L.symm) (hh.comp L.symm.differentiable.differentiableOn fun y hy ↦ by
      rwa [mem_ball, ← hL, L.apply_symm_apply]) hr hrR
  let v : (ι → ℂ) →ₗᵢ[ℂ] Fin (Fintype.card ι) → ℂ :=
    ⟨L.toLinearEquiv.toLinearMap, fun x ↦ by simpa using hL x 0⟩
  exact ⟨_, (hp.compLinearIsometry (v := v)).congr fun y _ ↦ by simp [v]⟩

end
