/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Analytic.Constructions
public import TauCeti.Analysis.Analytic.MultiIndex.Coeff
public import TauCeti.Analysis.Complex.PowerSeries.Polydisc

/-!
# Power series of holomorphic functions on polydiscs

On `ι → ℂ`, for a finite type `ι`, the balls of the sup norm are the polydiscs with equal radii.
This file shows that a function holomorphic on such a polydisc has a power series about its
centre on every smaller concentric polydisc.

## Main results

* `DifferentiableOn.exists_hasFPowerSeriesOnBall_of_lt`: a function holomorphic on the polydisc
  `ball c R` has a power series about `c` on `ball c r` for every `0 < r < R`.

On `Fin n → ℂ` the power series is Tau Ceti's multi-index Taylor series: it converges to the
function on the polydisc (`DifferentiableOn.hasSum_mvTaylorCoeff`), and Cauchy's inequality
(`DifferentiableOn.norm_mvTaylorCoeff_le`) on a polydisc of intermediate radius makes it
summable, so that `TauCeti.exists_hasFPowerSeriesOnBall_of_hasSum` applies. The transport from
`Fin n → ℂ` to `ι → ℂ` adapts that of Tau Ceti's
`DifferentiableOn.exists_differentiable_norm_sub_lt_of_pi`
(`TauCeti/Analysis/Complex/PowerSeries/Polydisc.lean`), and uses Tau Ceti's
`HasFPowerSeriesOnBall.compLinearIsometry`.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, §2.2.
-/

public section

open Metric
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The case `ι = Fin n` of `DifferentiableOn.exists_hasFPowerSeriesOnBall_of_lt`: the power
series is the multi-index Taylor series of `h` at `c`. -/
private theorem DifferentiableOn.exists_hasFPowerSeriesOnBall_of_lt_of_fin [CompleteSpace E]
    {n : ℕ} {h : (Fin n → ℂ) → E} {c : Fin n → ℂ} {R : ℝ} (hh : DifferentiableOn ℂ h (ball c R))
    {r : ℝ≥0} (hr : 0 < r) (hrR : (r : ℝ) < R) :
    ∃ p : FormalMultilinearSeries ℂ (Fin n → ℂ) E, HasFPowerSeriesOnBall h p c r := by
  -- Bound `h` on the closed ball of radius `s`, `r < s < R`, which lies in `ball c R`; Cauchy's
  -- inequality on `ball c s` then makes the Taylor series summable at radius `r`.
  set s : ℝ := (r + R) / 2
  have hrs : (r : ℝ) < s := by simp only [s]; linarith
  have hs : 0 < s := (NNReal.coe_pos.2 hr).trans hrs
  have hsR : s < R := by simp only [s]; linarith
  obtain ⟨M, hM⟩ := (isCompact_closedBall c s).exists_bound_of_continuousOn
    (hh.continuousOn.mono (closedBall_subset_ball hsR))
  have hq : Summable (fun α : Fin n → ℕ ↦ ∏ i, ((r : ℝ) / s) ^ α i) :=
    (TauCeti.hasSum_prod_geometric_of_norm_lt_one (r := fun _ ↦ (r : ℝ) / s) fun _ ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact (div_lt_one hs).2 hrs).summable
  refine (TauCeti.exists_hasFPowerSeriesOnBall_of_hasSum (c := TauCeti.mvTaylorCoeff h c) hr ?_
    fun y hy ↦ hh.hasSum_mvTaylorCoeff (hy.trans hrR)).imp fun _ hp ↦ hp.1
  refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun α ↦ ?_) (hq.mul_left M)
  have hb := (hh.mono (ball_subset_ball hsR.le)).norm_mvTaylorCoeff_le hs
    (fun w hw ↦ hM w (ball_subset_closedBall hw)) α
  calc _ ≤ M * s⁻¹ ^ (∑ i, α i) * (r : ℝ) ^ ∑ i, α i := by gcongr
    _ = M * ∏ i, ((r : ℝ) / s) ^ α i := by
      rw [mul_assoc, ← mul_pow, Finset.prod_pow_eq_pow_sum, inv_mul_eq_div]

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
