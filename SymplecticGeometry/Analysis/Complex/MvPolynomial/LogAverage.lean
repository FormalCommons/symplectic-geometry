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
import SymplecticGeometry.Analysis.Polynomial.CircleAverageLog
import SymplecticGeometry.MeasureTheory.Integral.Average
import SymplecticGeometry.MeasureTheory.Integral.BallCircleAverage
import SymplecticGeometry.Topology.Algebra.MvPolynomial
import TauCeti.MeasureTheory.Measure.Haar.Average
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
* `MvPolynomial.ae_restrict_log_norm_eval_le_log`: for `P ≠ 0`, a bound `‖P‖ ≤ M` on a measurable
  set gives `log ‖P‖ ≤ log M` at almost every point of it.
* `MvPolynomial.integrableOn_log_norm_eval_ball`: for `P ≠ 0`, `log ‖P‖` is integrable on every
  ball. It is bounded above on a ball, and the bound above controls it from below on a ball whose
  centre is not a zero of `P`; every ball lies in such a ball.
* `MvPolynomial.log_norm_eval_le_setAverage_ball`: if `P c ≠ 0`, then `log ‖P c‖` is at most the
  average of `log ‖P‖` over `Metric.ball c r`, for every `r > 0`.
  The lower-integral bound gives it through
  `MeasureTheory.sub_setAverage_le_of_setLIntegral_ofReal_sub_le`.

Last comes the comparison with the maximum:

* `MvPolynomial.norm_eval_le_add_one_pow_totalDegree_mul`: a bound `‖P‖ ≤ M` on
  `Metric.closedBall c r` gives `‖P‖ ≤ (t + 1) ^ P.totalDegree * M` on
  `Metric.closedBall c (t * r)`. On each complex line through `c`, `P` is a polynomial in one
  variable of degree at most `P.totalDegree`, by Tau Ceti's
  `MvPolynomial.natDegree_eval₂_C_add_C_mul_X_le`, and
  `Polynomial.exists_norm_eval_le_add_one_pow_mul` bounds its growth.
* `MvPolynomial.log_sup_sub_setAverage_log_norm_eval_le`: for `P.totalDegree ≤ D` and `R > 0`,
  the logarithm of the supremum of `‖P‖` on `Metric.closedBall y R` exceeds the average of
  `log ‖P‖` over `Metric.ball y R` by at most `4 ^ card ι * D * log 4`. Let `‖P‖` be largest on
  the closed ball at `z₀`; then `P z₀ ≠ 0`, and the sub-mean value inequality at `z₀` on
  `Metric.ball z₀ (2 * R)`, where the growth bound with `t = 3` gives `‖P‖ ≤ 4 ^ D * ‖P z₀‖`,
  bounds the lower average over the larger ball of the gap between the logarithm of that bound
  and `log ‖P‖`. Tau Ceti's `TauCeti.setLAverage_ball_le` passes to the lower average over
  `Metric.ball y R`, at the cost of the factor `2 ^ (2 * card ι) = 4 ^ card ι`, and
  `MeasureTheory.sub_setAverage_le_of_setLIntegral_ofReal_sub_le` turns that bound into one on the
  average of `log ‖P‖`.

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
polynomial on `EuclideanSpace ℂ ι` with `P c ≠ 0`, and let `‖P‖ ≤ M` on `Metric.ball c r`. Then
the lower integral of `ofReal (log M - log ‖P‖)` over the ball is at most the volume of the ball
times `ofReal (log M - log ‖P c‖)`. -/
theorem setLIntegral_ofReal_log_sub_log_norm_eval_le {P : MvPolynomial ι ℂ}
    {c : EuclideanSpace ℂ ι} (hc : eval c.ofLp P ≠ 0) {r M : ℝ}
    (hM : ∀ z ∈ ball c r, ‖eval z.ofLp P‖ ≤ M) :
    ∫⁻ z in ball c r, ENNReal.ofReal (Real.log M - Real.log ‖eval z.ofLp P‖) ≤
      volume (ball c r) * ENNReal.ofReal (Real.log M - Real.log ‖eval c.ofLp P‖) := by
  rcases le_or_gt r 0 with hr | hr
  · simp [ball_eq_empty.2 hr]
  have hmeas : Measurable fun z : EuclideanSpace ℂ ι =>
      ENNReal.ofReal (Real.log M - Real.log ‖eval z.ofLp P‖) := by
    fun_prop
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
  refine Polynomial.setLAverage_ofReal_log_sub_log_norm_eval_circleMap_le (hp0 ▸ hc)
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

/-- At a centre where `P` does not vanish, with `‖P‖ ≤ M` on the ball, `log M - log ‖P‖` is
nonnegative at almost every point of the ball, and `log ‖P‖` is integrable on the ball, by the
lower-integral bound. -/
private theorem integrableOn_log_norm_eval_ball_of_eval_ne_zero {P : MvPolynomial ι ℂ}
    {c : EuclideanSpace ℂ ι} (hc : eval c.ofLp P ≠ 0) {r M : ℝ}
    (hM : ∀ z ∈ ball c r, ‖eval z.ofLp P‖ ≤ M) :
    0 ≤ᵐ[volume.restrict (ball c r)] (fun z => Real.log M - Real.log ‖eval z.ofLp P‖) ∧
      IntegrableOn (fun z => Real.log ‖eval z.ofLp P‖) (ball c r) := by
  have hP : P ≠ 0 := fun h => hc (by simp [h])
  have hnn : 0 ≤ᵐ[volume.restrict (ball c r)]
      fun z => Real.log M - Real.log ‖eval z.ofLp P‖ :=
    (ae_restrict_log_norm_eval_le_log hP measurableSet_ball hM).mono fun _ => sub_nonneg.2
  have hfin : volume (ball c r) ≠ ∞ := measure_ball_lt_top.ne
  have h : IntegrableOn (fun z => Real.log M - Real.log ‖eval z.ofLp P‖) (ball c r) :=
    ⟨(by fun_prop : Measurable _).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hnn).2 ((setLIntegral_ofReal_log_sub_log_norm_eval_le hc
        hM).trans_lt (ENNReal.mul_lt_top hfin.lt_top ENNReal.ofReal_lt_top))⟩
  exact ⟨hnn, ((integrableOn_const hfin).sub h).congr_fun (fun z _ => sub_sub_cancel _ _)
    measurableSet_ball⟩

/-- `log ‖P‖` is integrable on every ball, for a nonzero complex polynomial `P` on
`EuclideanSpace ℂ ι`. -/
theorem integrableOn_log_norm_eval_ball {P : MvPolynomial ι ℂ} (hP : P ≠ 0)
    (c : EuclideanSpace ℂ ι) (r : ℝ) :
    IntegrableOn (fun z => Real.log ‖eval z.ofLp P‖) (ball c r) := by
  obtain ⟨c', hc', hc'P⟩ := exists_mem_ball_eval_ne_zero hP c one_pos
  have hsub : ball c r ⊆ ball c' (max r 0 + 1) := fun z hz => by
    rw [mem_ball] at hz hc' ⊢
    linarith [dist_triangle z c c', dist_comm c c', le_max_left r 0]
  obtain ⟨M, hM⟩ := (isCompact_closedBall c' (max r 0 + 1)).exists_bound_of_continuousOn
    (by fun_prop : Continuous fun z : EuclideanSpace ℂ ι => eval z.ofLp P).continuousOn
  exact (integrableOn_log_norm_eval_ball_of_eval_ne_zero hc'P
    fun z hz => hM z (ball_subset_closedBall hz)).2.mono_set hsub

/-- **Sub-mean value inequality for `log ‖P‖` over balls.** If a complex polynomial `P` on
`EuclideanSpace ℂ ι` does not vanish at `c`, then `log ‖P c‖` is at most the average of
`log ‖P‖` over `Metric.ball c r`, for every `r > 0`. -/
theorem log_norm_eval_le_setAverage_ball {P : MvPolynomial ι ℂ} {c : EuclideanSpace ℂ ι}
    (hc : eval c.ofLp P ≠ 0) {r : ℝ} (hr : 0 < r) :
    Real.log ‖eval c.ofLp P‖ ≤ ⨍ z in ball c r, Real.log ‖eval z.ofLp P‖ := by
  obtain ⟨M, hM'⟩ := (isCompact_closedBall c r).exists_bound_of_continuousOn
    (by fun_prop : Continuous fun z : EuclideanSpace ℂ ι => eval z.ofLp P).continuousOn
  have hM : ∀ z ∈ ball c r, ‖eval z.ofLp P‖ ≤ M := fun z hz => hM' z (ball_subset_closedBall hz)
  obtain ⟨hnn, hu⟩ := integrableOn_log_norm_eval_ball_of_eval_ne_zero hc hM
  have hK : 0 ≤ Real.log M - Real.log ‖eval c.ofLp P‖ :=
    sub_nonneg.2 (Real.log_le_log (norm_pos_iff.2 hc) (hM c (mem_ball_self hr)))
  have h := sub_setAverage_le_of_setLIntegral_ofReal_sub_le
    (measure_ball_pos volume c hr).ne' measure_ball_lt_top.ne hu
    (hnn.mono fun _ => sub_nonneg.1) hK (setLIntegral_ofReal_log_sub_log_norm_eval_le hc hM)
  linarith

/-- **Growth of `‖P‖` from a ball to a larger ball.** If a complex polynomial `P` on
`EuclideanSpace ℂ ι` satisfies `‖P‖ ≤ M` on `Metric.closedBall c r` with `r > 0`, then
`‖P‖ ≤ (t + 1) ^ P.totalDegree * M` on `Metric.closedBall c (t * r)`, for every `t ≥ 0`. -/
theorem norm_eval_le_add_one_pow_totalDegree_mul (P : MvPolynomial ι ℂ)
    {c : EuclideanSpace ℂ ι} {r t M : ℝ} (hr : 0 < r) (ht : 0 ≤ t)
    (hM : ∀ z ∈ closedBall c r, ‖eval z.ofLp P‖ ≤ M) {z : EuclideanSpace ℂ ι}
    (hz : z ∈ closedBall c (t * r)) :
    ‖eval z.ofLp P‖ ≤ (t + 1) ^ P.totalDegree * M := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM c (mem_closedBall_self hr.le))
  rcases eq_or_ne z c with rfl | hzc
  · exact (hM z (mem_closedBall_self hr.le)).trans
      (le_mul_of_one_le_left hM0 (one_le_pow₀ (by linarith)))
  set v := z - c with hv_def
  have hv : 0 < ‖v‖ := norm_pos_iff.2 (sub_ne_zero.2 hzc)
  set p : Polynomial ℂ :=
    aeval (fun i => Polynomial.C (c.ofLp i) + Polynomial.C (v.ofLp i) * Polynomial.X) P
  have hpe (s : ℂ) : p.eval s = eval (c + s • v).ofLp P := by
    simp [p, eval_aeval_C_add_C_mul_X]
  have hdeg : p.natDegree ≤ P.totalDegree := by
    simpa [p, aeval_def, Polynomial.algebraMap_eq] using
      P.natDegree_eval₂_C_add_C_mul_X_le (RingHom.id ℂ) c.ofLp v.ofLp
  obtain ⟨s, hs, hle⟩ := p.exists_norm_eval_le_add_one_pow_mul (div_pos hr hv) ht
  have h1 := hle 1 (by
    rw [norm_one, mul_div_assoc', le_div_iff₀ hv, one_mul]
    simpa [mem_closedBall, dist_eq_norm, v] using hz)
  rw [hpe, one_smul, hv_def, add_sub_cancel] at h1
  have h2 : ‖p.eval s‖ ≤ M := hpe s ▸ hM _ (by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, hs,
      div_mul_cancel₀ _ hv.ne'])
  calc ‖eval z.ofLp P‖ ≤ (t + 1) ^ p.natDegree * ‖p.eval s‖ := h1
    _ ≤ (t + 1) ^ P.totalDegree * M := by
      gcongr
      linarith

/-- **The average of `log ‖P‖` over a ball is close to its maximum.** For a complex polynomial
`P` on `EuclideanSpace ℂ ι` of total degree at most `D`, the logarithm of the supremum of `‖P‖`
over `Metric.closedBall y R` exceeds the average of `log ‖P‖` over `Metric.ball y R` by at most
`4 ^ card ι * D * log 4`, for every `R > 0`. This is a form of the Bernstein–Walsh
inequality. -/
theorem log_sup_sub_setAverage_log_norm_eval_le (P : MvPolynomial ι ℂ) {D : ℕ}
    (hD : P.totalDegree ≤ D) (y : EuclideanSpace ℂ ι) {R : ℝ} (hR : 0 < R) :
    Real.log (sSup ((fun z => ‖eval z.ofLp P‖) '' closedBall y R)) -
        ⨍ z in ball y R, Real.log ‖eval z.ofLp P‖ ≤
      4 ^ Fintype.card ι * D * Real.log 4 := by
  rcases eq_or_ne P 0 with rfl | hP
  · simp only [map_zero, norm_zero, (nonempty_closedBall.2 hR.le).image_const, csSup_singleton,
      Real.log_zero, average_zero, sub_zero]
    positivity
  obtain ⟨z₀, hz₀, hmax⟩ := (isCompact_closedBall y R).exists_isMaxOn
    (nonempty_closedBall.2 hR.le)
    (by fun_prop : Continuous fun z : EuclideanSpace ℂ ι => ‖eval z.ofLp P‖).continuousOn
  have hmax' : ∀ z ∈ closedBall y R, ‖eval z.ofLp P‖ ≤ ‖eval z₀.ofLp P‖ := fun z hz => hmax hz
  rw [(show IsGreatest _ _ from ⟨mem_image_of_mem _ hz₀, forall_mem_image.2 hmax'⟩).csSup_eq]
  have hz₀P : eval z₀.ofLp P ≠ 0 := by
    intro h
    obtain ⟨v, hv, hv0⟩ := exists_mem_ball_eval_ne_zero hP y hR
    have := hmax' v (ball_subset_closedBall hv)
    rw [h, norm_zero] at this
    exact hv0 (norm_le_zero_iff.1 this)
  have hM₁ : 0 < ‖eval z₀.ofLp P‖ := norm_pos_iff.2 hz₀P
  set M := (4 : ℝ) ^ D * ‖eval z₀.ofLp P‖
  have hM : ∀ z ∈ ball z₀ (2 * R), ‖eval z.ofLp P‖ ≤ M := fun z hz => by
    refine (P.norm_eval_le_add_one_pow_totalDegree_mul (t := 3) hR (by norm_num) hmax' ?_).trans
      ?_
    · rw [mem_ball] at hz
      rw [mem_closedBall] at hz₀ ⊢
      linarith [dist_triangle z z₀ y]
    · norm_num only
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hD) hM₁.le
  have hsub : ball y R ⊆ ball z₀ (2 * R) := fun z hz => by
    rw [mem_ball] at hz ⊢
    rw [mem_closedBall] at hz₀
    linarith [dist_triangle z y z₀, dist_comm z₀ y]
  have hlogM : Real.log M - Real.log ‖eval z₀.ofLp P‖ = D * Real.log 4 := by
    rw [Real.log_mul (by positivity) hM₁.ne', Real.log_pow]
    ring
  have hpos : volume (ball y R) ≠ 0 := (measure_ball_pos volume y hR).ne'
  -- The lower average over `ball y R` is at most `2 ^ (2 * card ι)` times that over the big ball.
  have h := (TauCeti.setLAverage_ball_le (μ := volume) _ hR hsub).trans <| mul_le_mul_right
    ((setLAverage_eq _ _ _).trans_le <| ENNReal.div_le_of_le_mul'
      (setLIntegral_ofReal_log_sub_log_norm_eval_le hz₀P hM)) _
  rw [setLAverage_eq, ENNReal.div_le_iff_le_mul (Or.inl hpos) (Or.inl measure_ball_lt_top.ne),
    mul_div_cancel_right₀ _ hR.ne', finrank_real_of_complex, finrank_euclideanSpace, pow_mul,
    show (2 : ℝ) ^ 2 = 4 by norm_num, hlogM, ← ENNReal.ofReal_mul (by positivity), mul_comm] at h
  have := sub_setAverage_le_of_setLIntegral_ofReal_sub_le hpos measure_ball_lt_top.ne
    (integrableOn_log_norm_eval_ball hP y R)
    (ae_restrict_log_norm_eval_le_log hP measurableSet_ball fun z hz => hM z (hsub hz))
    (by positivity) h
  have : 0 ≤ (D : ℝ) * Real.log 4 := by positivity
  linarith

end MvPolynomial

end
