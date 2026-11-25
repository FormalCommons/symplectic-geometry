/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.MeasureTheory.Measure.MvPolynomialZeroLocus
import Mathlib.Topology.Algebra.MvPolynomial
import SymplecticGeometry.Analysis.Polynomial.CircleAverageLog
import SymplecticGeometry.MeasureTheory.Integral.BallCircleAverage
import TauCeti.RingTheory.MvPolynomial.LineRestriction

/-!
# Averages of `log ‖P‖` over balls for complex polynomials

This file is about the averages of `log ‖eval v.ofLp P‖` over balls of `EuclideanSpace ℂ ι`, for a
multivariate polynomial `P` with complex coefficients. Its aim is the comparison between such an
average and the logarithm of the largest value of `‖P‖` on the ball, a form of the
Bernstein–Walsh inequality, which bounds the growth of a polynomial of degree `d` away from a
compact set by the `d`-th power of the Siciak extremal function.

It starts with the null-set facts that the averages need:

* `MvPolynomial.ae_eval_ne_zero`: a nonzero polynomial does not vanish at almost every point of
  `EuclideanSpace ℂ ι`;
* `MvPolynomial.exists_mem_ball_eval_ne_zero`: every ball of positive radius has a point where a
  nonzero polynomial does not vanish.

The first transfers Tau Ceti's `MvPolynomial.volume_setOfPred_eval_eq_zero` from `ι → ℂ` to
`EuclideanSpace ℂ ι` along Tau Ceti's `PiLp.volume_preserving_symm_measurableEquiv_toLp`, by which
`ofLp` preserves the volume.

Then comes the sub-mean value inequality over balls, which holds because `log ‖P‖` is
plurisubharmonic. Here it is proved from one complex variable:

* `MvPolynomial.setLIntegral_ofReal_log_sub_log_norm_eval_le`: if `P c ≠ 0` and `‖P‖ ≤ M` on
  `Metric.ball c r`, the lower integral of `ofReal (log M - log ‖P‖)` over the ball is at most
  its volume times `log M - log ‖P c‖`. The ball is a family of circles about `c`
  (`MeasureTheory.setLIntegral_ball_eq_mul_setLIntegral_setLAverage_circleMap`); on each of them
  `P` is a polynomial in one variable, by Tau Ceti's `MvPolynomial.eval_aeval_C_add_C_mul_X`,
  and `Polynomial.setLAverage_ofReal_log_sub_log_norm_eval_circleMap_le` bounds its mean. The
  `ofReal` makes the integrand nonnegative even on the zero set of `P`, where `log ‖P‖ = 0`.
* `MvPolynomial.integrableOn_log_norm_eval_ball`: for `P ≠ 0`, `log ‖P‖` is integrable on every
  ball. It is bounded above on a ball, and the bound above controls it from below on a ball whose
  centre is not a zero of `P`; every ball lies in such a ball.
* `MvPolynomial.log_norm_eval_le_setAverage_ball`: if `P c ≠ 0`, then `log ‖P c‖` is at most the
  average of `log ‖P‖` over `Metric.ball c r`, for every `r > 0`.

## References

* [M. Klimek, *Pluripotential Theory*, Oxford University Press, 1991], Chapter 5 (the
  Bernstein–Walsh inequality)
-/

public section

open MeasureTheory Metric Set
open scoped ENNReal Real

namespace MvPolynomial

variable {ι : Type*} [Fintype ι]

/-- A nonzero polynomial in the coordinates of `EuclideanSpace ℂ ι` is nonzero at almost every
point. -/
theorem ae_eval_ne_zero {Q : MvPolynomial ι ℂ} (hQ : Q ≠ 0) :
    ∀ᵐ v : EuclideanSpace ℂ ι, eval v.ofLp Q ≠ 0 := by
  have h := (PiLp.volume_preserving_symm_measurableEquiv_toLp
    (F := fun _ : ι => ℂ)).quasiMeasurePreserving.preimage_null
    (volume_setOfPred_eval_eq_zero Q hQ)
  exact measure_mono_null (fun v hv => by simpa using hv) h

/-- A nonzero polynomial in the coordinates of `EuclideanSpace ℂ ι` is nonzero at some point of
every ball of positive radius. -/
theorem exists_mem_ball_eval_ne_zero {Q : MvPolynomial ι ℂ} (hQ : Q ≠ 0)
    (c : EuclideanSpace ℂ ι) {r : ℝ} (hr : 0 < r) :
    ∃ v ∈ Metric.ball c r, eval v.ofLp Q ≠ 0 := by
  by_contra! h
  refine (Metric.measure_ball_pos volume c hr).ne' (measure_mono_null (fun v hv => ?_)
    (ae_iff.mp (ae_eval_ne_zero hQ)))
  simpa using h v hv

/-- **Sub-mean value inequality for `log ‖P‖`, lower-integral form.** Let `P` be a complex
polynomial on `EuclideanSpace ℂ ι` with `P c ≠ 0`, and let `‖P‖ ≤ M` on `Metric.ball c r`, with
`r > 0`. Then the lower integral of `ofReal (log M - log ‖P‖)` over the ball is at most the volume
of the ball times `ofReal (log M - log ‖P c‖)`. -/
theorem setLIntegral_ofReal_log_sub_log_norm_eval_le {P : MvPolynomial ι ℂ}
    {c : EuclideanSpace ℂ ι} (hc : eval c.ofLp P ≠ 0) {r M : ℝ} (hr : 0 < r)
    (hM : ∀ z ∈ ball c r, ‖eval z.ofLp P‖ ≤ M) :
    ∫⁻ z in ball c r, ENNReal.ofReal (Real.log M - Real.log ‖eval z.ofLp P‖) ≤
      volume (ball c r) * ENNReal.ofReal (Real.log M - Real.log ‖eval c.ofLp P‖) := by
  have hmeas : Measurable fun z : EuclideanSpace ℂ ι =>
      ENNReal.ofReal (Real.log M - Real.log ‖eval z.ofLp P‖) := by
    have : Continuous fun z : EuclideanSpace ℂ ι => eval z.ofLp P :=
      (MvPolynomial.continuous_eval P).comp (PiLp.continuous_ofLp 2 _)
    exact ENNReal.measurable_ofReal.comp
      (measurable_const.sub (Real.measurable_log.comp this.norm.measurable))
  rw [setLIntegral_ball_eq_mul_setLIntegral_setLAverage_circleMap volume hmeas c hr,
    Measure.addHaar_ball_of_pos volume c hr, mul_assoc,
    mul_comm (volume (ball (0 : EuclideanSpace ℂ ι) 1)), ← setLIntegral_const]
  refine mul_le_mul_right (setLIntegral_mono measurable_const fun v hv => ?_) _
  set p : Polynomial ℂ :=
    aeval (fun i => Polynomial.C (c.ofLp i) + Polynomial.C (v.ofLp i) * Polynomial.X) P
  have hpe (t : ℂ) : p.eval t = eval (c + t • v).ofLp P := by
    simp [p, eval_aeval_C_add_C_mul_X]
  have hp0 : p.eval 0 = eval c.ofLp P := by simpa using hpe 0
  simp_rw [← hpe]
  rw [← hp0]
  refine Polynomial.setLAverage_ofReal_log_sub_log_norm_eval_circleMap_le (hp0 ▸ hc) hr.ne'
    fun θ => hpe _ ▸ hM _ ?_
  rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_circleMap_zero, abs_of_pos hr]
  exact mul_lt_of_lt_one_right hr (by simpa using hv)


/-- If a nonzero complex polynomial `P` on `EuclideanSpace ℂ ι` satisfies `‖P‖ ≤ M` on a
measurable set `s`, then `log ‖P‖ ≤ log M` at almost every point of `s`. The exception is the
zero set of `P`, where `log ‖P‖ = 0`. -/
theorem ae_restrict_log_norm_eval_le_log {P : MvPolynomial ι ℂ} (hP : P ≠ 0)
    {s : Set (EuclideanSpace ℂ ι)} (hs : MeasurableSet s) {M : ℝ}
    (hM : ∀ z ∈ s, ‖eval z.ofLp P‖ ≤ M) :
    ∀ᵐ z ∂volume.restrict s, Real.log ‖eval z.ofLp P‖ ≤ Real.log M := by
  filter_upwards [ae_restrict_mem hs, ae_restrict_of_ae (ae_eval_ne_zero hP)] with z hz hz0
  exact Real.log_le_log (norm_pos_iff.2 hz0) (hM z hz)

/-- At a centre where `P` does not vanish, with `‖P‖ ≤ M` on the ball, the nonnegative function
`log M - log ‖P‖` is integrable on the ball, by the lower-integral bound. -/
private theorem integrableOn_log_sub_log_norm_eval_ball {P : MvPolynomial ι ℂ}
    {c : EuclideanSpace ℂ ι} (hc : eval c.ofLp P ≠ 0) {r M : ℝ} (hr : 0 < r)
    (hM : ∀ z ∈ ball c r, ‖eval z.ofLp P‖ ≤ M) :
    IntegrableOn (fun z => Real.log M - Real.log ‖eval z.ofLp P‖) (ball c r) := by
  have hP : P ≠ 0 := fun h => hc (by simp [h])
  have hnn : 0 ≤ᵐ[volume.restrict (ball c r)]
      fun z => Real.log M - Real.log ‖eval z.ofLp P‖ := by
    filter_upwards [ae_restrict_log_norm_eval_le_log hP measurableSet_ball hM] with z hz
    exact sub_nonneg.2 hz
  refine ⟨(measurable_const.sub (Real.measurable_log.comp ((MvPolynomial.continuous_eval P).comp
    (PiLp.continuous_ofLp 2 _)).norm.measurable)).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal hnn).2 ?_⟩
  exact (setLIntegral_ofReal_log_sub_log_norm_eval_le hc hr hM).trans_lt
    (ENNReal.mul_lt_top measure_ball_lt_top ENNReal.ofReal_lt_top)

/-- `log ‖P‖` is integrable on every ball, for a nonzero complex polynomial `P` on
`EuclideanSpace ℂ ι`. -/
theorem integrableOn_log_norm_eval_ball {P : MvPolynomial ι ℂ} (hP : P ≠ 0)
    (c : EuclideanSpace ℂ ι) (r : ℝ) :
    IntegrableOn (fun z => Real.log ‖eval z.ofLp P‖) (ball c r) := by
  obtain ⟨c', hc', hc'P⟩ := exists_mem_ball_eval_ne_zero hP c one_pos
  have hR : 0 < max r 0 + 1 := by positivity
  have hsub : ball c r ⊆ ball c' (max r 0 + 1) := fun z hz => by
    rw [mem_ball] at hz hc' ⊢
    linarith [dist_triangle z c c', dist_comm c c', le_max_left r 0]
  obtain ⟨M, hM⟩ := (isCompact_closedBall c' (max r 0 + 1)).exists_bound_of_continuousOn
    ((MvPolynomial.continuous_eval P).comp (PiLp.continuous_ofLp 2 _)).continuousOn
  have h := integrableOn_log_sub_log_norm_eval_ball hc'P hR
    fun z hz => hM z (ball_subset_closedBall hz)
  exact (((integrableOn_const measure_ball_lt_top.ne).sub h).congr_fun
    (fun z _ => sub_sub_cancel _ _) measurableSet_ball).mono_set hsub

/-- **Sub-mean value inequality for `log ‖P‖` over balls.** If a complex polynomial `P` on
`EuclideanSpace ℂ ι` does not vanish at `c`, then `log ‖P c‖` is at most the average of
`log ‖P‖` over `Metric.ball c r`, for every `r > 0`. -/
theorem log_norm_eval_le_setAverage_ball {P : MvPolynomial ι ℂ} {c : EuclideanSpace ℂ ι}
    (hc : eval c.ofLp P ≠ 0) {r : ℝ} (hr : 0 < r) :
    Real.log ‖eval c.ofLp P‖ ≤ ⨍ z in ball c r, Real.log ‖eval z.ofLp P‖ := by
  have hP : P ≠ 0 := fun h => hc (by simp [h])
  obtain ⟨M, hM'⟩ := (isCompact_closedBall c r).exists_bound_of_continuousOn
    ((MvPolynomial.continuous_eval P).comp (PiLp.continuous_ofLp 2 _)).continuousOn
  have hM : ∀ z ∈ ball c r, ‖eval z.ofLp P‖ ≤ M := fun z hz => hM' z (ball_subset_closedBall hz)
  have hint := integrableOn_log_sub_log_norm_eval_ball hc hr hM
  have hnn : 0 ≤ᵐ[volume.restrict (ball c r)]
      fun z => Real.log M - Real.log ‖eval z.ofLp P‖ := by
    filter_upwards [ae_restrict_log_norm_eval_le_log hP measurableSet_ball hM] with z hz
    exact sub_nonneg.2 hz
  have hK : 0 ≤ Real.log M - Real.log ‖eval c.ofLp P‖ :=
    sub_nonneg.2 (Real.log_le_log (norm_pos_iff.2 hc) (hM c (mem_ball_self hr)))
  have hfin : volume (ball c r) ≠ ∞ := measure_ball_lt_top.ne
  -- The integral of `log M - log ‖P‖` is at most `vol (ball c r) * (log M - log ‖P c‖)`.
  have h1 : ∫ z in ball c r, (Real.log M - Real.log ‖eval z.ofLp P‖) ≤
      volume.real (ball c r) * (Real.log M - Real.log ‖eval c.ofLp P‖) := by
    rw [integral_eq_lintegral_of_nonneg_ae hnn hint.aestronglyMeasurable, measureReal_def,
      ← ENNReal.toReal_ofReal hK, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top hfin ENNReal.ofReal_ne_top)
      (setLIntegral_ofReal_log_sub_log_norm_eval_le hc hr hM)
  rw [integral_sub (integrableOn_const hfin) (integrableOn_log_norm_eval_ball hP c r),
    setIntegral_const, smul_eq_mul] at h1
  have hV : 0 < volume.real (ball c r) :=
    ENNReal.toReal_pos (measure_ball_pos volume c hr).ne' hfin
  rw [setAverage_eq, smul_eq_mul, le_inv_mul_iff₀ hV]
  linarith

end MvPolynomial

end
