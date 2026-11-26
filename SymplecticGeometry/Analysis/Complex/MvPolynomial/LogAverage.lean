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
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import SymplecticGeometry.Analysis.Polynomial.CircleAverageLog
import SymplecticGeometry.MeasureTheory.Integral.BallCircleAverage
import SymplecticGeometry.Topology.Algebra.MvPolynomial
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
  bounds the lower integral over the smaller ball `Metric.ball y R`. The ratio of the volumes of
  the two balls is `2 ^ (2 * card ι) = 4 ^ card ι`.

Finally, how the average `V c r` of `log ‖P‖` over `Metric.ball c r` grows with `r`:

* `MvPolynomial.setAverage_log_norm_eval_sub_le`: for `P.totalDegree ≤ D` and `0 < r₁ ≤ r₂`,
  `0 ≤ V c r₂ - V c r₁`, and `V c r₂ - V c r₁` is at most `D * log (r₂ / r₁)` times the
  proportion of the `v` in the unit ball for which `P` vanishes at some `c + s • v` with
  `‖s‖ < r₂`.
* `MvPolynomial.log_div_le_setAverage_log_norm_eval_sub`: for `P ≠ 0` with `P y = 0`,
  `log (r₂ / r₁) ≤ V y r₂ - V y r₁`.

Both compare the two radii line by line. With `log ‖P‖ ≤ log M` on `Metric.closedBall c r₂`,
the balls as families of circles turn `volume (ball 0 1) * (log M - V c ρ)`, for `ρ ≤ r₂`, into
the lower integral over the unit ball of `log M` minus the circle average of `log ‖P‖` at
radius `ρ` on the line `s ↦ c + s • v`. On each line `P` is a polynomial in one variable of
degree at most `D`, and the bounds of `Polynomial.circleAverage_log_norm_eval_sub_le`,
`Polynomial.rootMultiplicity_mul_log_le_circleAverage_sub` and
`Polynomial.circleAverage_log_norm_eval_sub_eq_zero` compare its circle averages at `r₁` and
`r₂`. For the second result, `P` vanishes on no line through `y` in almost every direction,
since `P (y + v) ≠ 0` for almost every `v`, and each such line has a root at `0`.

## References

* [M. Klimek, *Pluripotential Theory*, Oxford University Press, 1991], Chapter 5 (the
  Bernstein–Walsh inequality)
-/

public section

open MeasureTheory Metric Set
open scoped ENNReal Real

namespace MvPolynomial

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- The restriction of `P` to the complex line through `c` in the direction `v` is a polynomial in
one variable of degree at most `P.totalDegree`. -/
private theorem exists_polynomial_eval_eq (P : MvPolynomial ι ℂ) (c v : EuclideanSpace ℂ ι) :
    ∃ p : Polynomial ℂ, p.natDegree ≤ P.totalDegree ∧
      ∀ s : ℂ, p.eval s = eval (c + s • v).ofLp P :=
  ⟨aeval (fun i => Polynomial.C (c.ofLp i) + Polynomial.C (v.ofLp i) * Polynomial.X) P,
    by simpa [aeval_def, Polynomial.algebraMap_eq] using
      P.natDegree_eval₂_C_add_C_mul_X_le (RingHom.id ℂ) c.ofLp v.ofLp,
    fun s => by simp [eval_aeval_C_add_C_mul_X]⟩

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
  obtain ⟨p, -, hpe⟩ := exists_polynomial_eval_eq P c v
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
  have hfin : volume (ball c r) ≠ ∞ := measure_ball_lt_top.ne
  have hpos : volume (ball c r) ≠ 0 := (measure_ball_pos volume c hr).ne'
  have hint : IntegrableOn (fun z => Real.log M - Real.log ‖eval z.ofLp P‖) (ball c r) :=
    (integrableOn_const hfin).sub hu
  have h := setLIntegral_ofReal_log_sub_log_norm_eval_le hc hM
  rw [mul_comm, ← ENNReal.div_le_iff_le_mul (Or.inl hpos) (Or.inl hfin),
    ← ofReal_setAverage hint hnn, ENNReal.ofReal_le_ofReal_iff hK,
    setAverage_fun_sub (integrableOn_const hfin) hu, setAverage_const hpos hfin] at h
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
  obtain ⟨p, hdeg, hpe⟩ := exists_polynomial_eval_eq P c v
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
  have hvol : volume (ball z₀ (2 * R)) =
      ENNReal.ofReal (4 ^ Fintype.card ι) * volume (ball y R) := by
    rw [Measure.addHaar_ball_mul_of_pos volume z₀ two_pos, ← Measure.addHaar_ball_center volume y,
      finrank_real_of_complex, finrank_euclideanSpace, pow_mul]
    norm_num
  have h := (lintegral_mono_set hsub).trans
    (setLIntegral_ofReal_log_sub_log_norm_eval_le hz₀P hM)
  rw [hvol, hlogM, mul_comm (ENNReal.ofReal _), mul_assoc,
    ← ENNReal.ofReal_mul (by positivity)] at h
  have hnn : 0 ≤ᵐ[volume.restrict (ball y R)]
      fun z => Real.log M - Real.log ‖eval z.ofLp P‖ :=
    (ae_restrict_log_norm_eval_le_log hP measurableSet_ball fun z hz => hM z (hsub hz)).mono
      fun _ => sub_nonneg.2
  have hu := integrableOn_log_norm_eval_ball hP y R
  have hfin : volume (ball y R) ≠ ∞ := measure_ball_lt_top.ne
  have hpos : volume (ball y R) ≠ 0 := (measure_ball_pos volume y hR).ne'
  have hint : IntegrableOn (fun z => Real.log M - Real.log ‖eval z.ofLp P‖) (ball y R) :=
    (integrableOn_const hfin).sub hu
  rw [mul_comm, ← ENNReal.div_le_iff_le_mul (Or.inl hpos) (Or.inl hfin),
    ← ofReal_setAverage hint hnn, ENNReal.ofReal_le_ofReal_iff (by positivity),
    setAverage_fun_sub (integrableOn_const hfin) hu, setAverage_const hpos hfin] at h
  have : 0 ≤ (D : ℝ) * Real.log 4 := by positivity
  linarith

/-! ### Growth of the averages with the radius -/

/-- `log ‖P‖` is bounded above by some `log M` on every closed ball. -/
private theorem exists_log_norm_eval_le_log (P : MvPolynomial ι ℂ) (c : EuclideanSpace ℂ ι)
    (r : ℝ) : ∃ M : ℝ, ∀ z ∈ closedBall c r, Real.log ‖eval z.ofLp P‖ ≤ Real.log M := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall c r).exists_bound_of_continuousOn
    (by fun_prop : Continuous fun z : EuclideanSpace ℂ ι => eval z.ofLp P).continuousOn
  refine ⟨max M 1, fun z hz => ?_⟩
  rcases eq_or_ne (eval z.ofLp P) 0 with h0 | h0
  · rw [h0, norm_zero, Real.log_zero]
    exact Real.log_nonneg (le_max_right _ _)
  · exact Real.log_le_log (norm_pos_iff.2 h0) ((hM z hz).trans (le_max_left _ _))

/-- On the complex lines through `c` in the directions `v` of the unit ball, the circle averages of
`log ‖P‖` at radii `ρ ≤ r` are at most `log M`, when `log ‖P‖ ≤ log M` on `closedBall c r`. -/
private theorem circleAverage_log_norm_eval_line_le {P : MvPolynomial ι ℂ}
    {c : EuclideanSpace ℂ ι} {r ρ M : ℝ} (hρ : 0 ≤ ρ) (hρr : ρ ≤ r)
    (hM : ∀ z ∈ closedBall c r, Real.log ‖eval z.ofLp P‖ ≤ Real.log M)
    {v : EuclideanSpace ℂ ι} (hv : v ∈ ball (0 : EuclideanSpace ℂ ι) 1) :
    Real.circleAverage (fun s : ℂ => Real.log ‖eval (c + s • v).ofLp P‖) 0 ρ ≤ Real.log M := by
  obtain ⟨p, -, hpe⟩ := exists_polynomial_eval_eq P c v
  simp_rw [← hpe]
  have han : AnalyticOnNhd ℂ (fun z => p.eval z) univ := fun z _ =>
    p.differentiable.analyticAt z
  refine Real.circleAverage_mono_on_of_le_circle
    ((han.mono (subset_univ _)).meromorphicOn.circleIntegrable_log_norm) fun z hz => ?_
  rw [hpe]
  refine hM _ ?_
  rw [mem_sphere_zero_iff_norm, abs_of_nonneg hρ] at hz
  rw [mem_ball_zero_iff] at hv
  rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, hz]
  exact (mul_le_of_le_one_right hρ hv.le).trans hρr

/-- **Step 2 for `log M - log ‖P‖`.** If `log ‖P‖ ≤ log M` on `closedBall c r` and `0 < ρ ≤ r`,
then `log M` is at least the average `V` of `log ‖P‖` over `ball c ρ`, and the lower integral,
over the unit ball, of `ofReal (log M - A v)` is `ofReal` of the volume of the unit ball times
`log M - V`, where `A v` is the circle average of `log ‖P‖` at radius `ρ` on the complex line
through `c` in the direction `v`. -/
private theorem setLIntegral_ofReal_log_sub_circleAverage {P : MvPolynomial ι ℂ} (hP : P ≠ 0)
    {c : EuclideanSpace ℂ ι} {r ρ M : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r)
    (hM : ∀ z ∈ closedBall c r, Real.log ‖eval z.ofLp P‖ ≤ Real.log M) :
    0 ≤ Real.log M - ⨍ z in ball c ρ, Real.log ‖eval z.ofLp P‖ ∧
      ∫⁻ v in ball (0 : EuclideanSpace ℂ ι) 1, ENNReal.ofReal (Real.log M -
          Real.circleAverage (fun s : ℂ => Real.log ‖eval (c + s • v).ofLp P‖) 0 ρ) =
        ENNReal.ofReal (volume.real (ball (0 : EuclideanSpace ℂ ι) 1) *
          (Real.log M - ⨍ z in ball c ρ, Real.log ‖eval z.ofLp P‖)) := by
  have hsub : ball c ρ ⊆ closedBall c r :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall hρr)
  have hu := integrableOn_log_norm_eval_ball hP c ρ
  have hfin : volume (ball c ρ) ≠ ∞ := measure_ball_lt_top.ne
  have hpos : volume (ball c ρ) ≠ 0 := (measure_ball_pos volume c hρ).ne'
  have hint : IntegrableOn (fun z => Real.log M - Real.log ‖eval z.ofLp P‖) (ball c ρ) :=
    (integrableOn_const hfin).sub hu
  have hnn : ∀ z ∈ ball c ρ, 0 ≤ Real.log M - Real.log ‖eval z.ofLp P‖ :=
    fun z hz => sub_nonneg.2 (hM z (hsub hz))
  have havg : ⨍ z in ball c ρ, (Real.log M - Real.log ‖eval z.ofLp P‖) =
      Real.log M - ⨍ z in ball c ρ, Real.log ‖eval z.ofLp P‖ := by
    rw [setAverage_fun_sub (integrableOn_const hfin) hu, setAverage_const hpos hfin]
  refine ⟨?_, ?_⟩
  · rw [← havg]
    exact average_nonneg_of_ae (ae_restrict_of_forall_mem measurableSet_ball hnn)
  have hmeas : Measurable fun z : EuclideanSpace ℂ ι =>
      ENNReal.ofReal (Real.log M - Real.log ‖eval z.ofLp P‖) := by
    fun_prop
  have h2 := setLIntegral_ball_eq_mul_setLIntegral_setLAverage_circleMap volume hmeas c hρ
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_restrict_of_forall_mem measurableSet_ball hnn),
    ← measure_smul_setAverage _ hfin, havg, measureReal_def,
    Measure.addHaar_ball_of_pos volume c hρ,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), smul_eq_mul, mul_assoc,
    ENNReal.ofReal_mul (by positivity), ← measureReal_def] at h2
  rw [(ENNReal.mul_right_inj (ENNReal.ofReal_pos.2 (by positivity)).ne' ENNReal.ofReal_ne_top).1
    h2]
  refine setLIntegral_congr_fun measurableSet_ball fun v hv => ?_
  obtain ⟨p, -, hpe⟩ := exists_polynomial_eval_eq P c v
  simp_rw [← hpe]
  refine (Polynomial.setLAverage_ofReal_log_sub_log_norm_eval_circleMap p fun θ => ?_).symm
  rw [hpe]
  refine hM _ ?_
  rw [mem_ball_zero_iff] at hv
  rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_circleMap_zero,
    abs_of_pos hρ]
  exact (mul_le_of_le_one_right hρ.le hv.le).trans hρr

omit [Fintype ι] in
/-- Step 1 on the complex line through `c` in the direction `v`: the difference of the circle
averages of `log ‖P‖` at radii `0 < r₁ ≤ r₂` is nonnegative, at most `D * log (r₂ / r₁)`, and
zero if `P` vanishes at no `c + s • v` with `‖s‖ < r₂`. -/
private theorem circleAverage_log_norm_eval_line_sub {P : MvPolynomial ι ℂ} {D : ℕ}
    (hD : P.totalDegree ≤ D) (c v : EuclideanSpace ℂ ι) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁)
    (h : r₁ ≤ r₂) :
    0 ≤ Real.circleAverage (fun s : ℂ => Real.log ‖eval (c + s • v).ofLp P‖) 0 r₂ -
        Real.circleAverage (fun s : ℂ => Real.log ‖eval (c + s • v).ofLp P‖) 0 r₁ ∧
      Real.circleAverage (fun s : ℂ => Real.log ‖eval (c + s • v).ofLp P‖) 0 r₂ -
          Real.circleAverage (fun s : ℂ => Real.log ‖eval (c + s • v).ofLp P‖) 0 r₁ ≤
        D * Real.log (r₂ / r₁) ∧
      ((∀ s : ℂ, ‖s‖ < r₂ → eval (c + s • v).ofLp P ≠ 0) →
        Real.circleAverage (fun s : ℂ => Real.log ‖eval (c + s • v).ofLp P‖) 0 r₂ -
          Real.circleAverage (fun s : ℂ => Real.log ‖eval (c + s • v).ofLp P‖) 0 r₁ = 0) := by
  have hL : 0 ≤ Real.log (r₂ / r₁) := Real.log_nonneg ((one_le_div hr₁).2 h)
  obtain ⟨p, hpD, hpe⟩ := exists_polynomial_eval_eq P c v
  simp_rw [← hpe]
  refine ⟨(by positivity : (0 : ℝ) ≤ p.rootMultiplicity 0 * Real.log (r₂ / r₁)).trans
      (p.rootMultiplicity_mul_log_le_circleAverage_sub hr₁ h),
    (p.circleAverage_log_norm_eval_sub_le hr₁ h).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hpD.trans hD : (p.natDegree : ℝ) ≤ D)
        hL), fun hne => ?_⟩
  refine p.circleAverage_log_norm_eval_sub_eq_zero hr₁ h fun a ha => ?_
  by_contra! hlt
  have h0 := (Polynomial.isRoot_of_mem_roots ha).eq_zero
  exact hne a hlt h0

omit [Fintype ι] in
/-- Step 1 on the complex line through a zero `y` of `P` in the direction `v`, when `P` does not
vanish on the whole line: the difference of the circle averages of `log ‖P‖` at radii
`0 < r₁ ≤ r₂` is at least `log (r₂ / r₁)`. -/
private theorem log_div_le_circleAverage_log_norm_eval_line_sub {P : MvPolynomial ι ℂ}
    {y : EuclideanSpace ℂ ι} (hy : eval y.ofLp P = 0) {v : EuclideanSpace ℂ ι}
    (hv : ∃ s : ℂ, eval (y + s • v).ofLp P ≠ 0) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (h : r₁ ≤ r₂) :
    Real.log (r₂ / r₁) ≤
      Real.circleAverage (fun s : ℂ => Real.log ‖eval (y + s • v).ofLp P‖) 0 r₂ -
        Real.circleAverage (fun s : ℂ => Real.log ‖eval (y + s • v).ofLp P‖) 0 r₁ := by
  have hL : 0 ≤ Real.log (r₂ / r₁) := Real.log_nonneg ((one_le_div hr₁).2 h)
  obtain ⟨p, -, hpe⟩ := exists_polynomial_eval_eq P y v
  have hp0 : p ≠ 0 := by
    obtain ⟨s, hs⟩ := hv
    rintro rfl
    exact hs (by rw [← hpe, Polynomial.eval_zero])
  have hroot : 1 ≤ p.rootMultiplicity 0 :=
    (Polynomial.rootMultiplicity_pos hp0).2 (by simpa [Polynomial.IsRoot, hpe] using hy)
  simp_rw [← hpe]
  calc Real.log (r₂ / r₁) ≤ p.rootMultiplicity 0 * Real.log (r₂ / r₁) :=
        le_mul_of_one_le_left hL (by exact_mod_cast hroot)
    _ ≤ _ := p.rootMultiplicity_mul_log_le_circleAverage_sub hr₁ h

/-- **Growth of the averages of `log ‖P‖` with the radius.** Let `P` be a complex polynomial on
`EuclideanSpace ℂ ι` of total degree at most `D`, and `0 < r₁ ≤ r₂`. The average of `log ‖P‖`
over `Metric.ball c r` does not decrease from `r = r₁` to `r = r₂`, and it grows by at most
`D * log (r₂ / r₁)` times the proportion, in volume, of the `v` in the unit ball for which `P`
vanishes at some `c + s • v` with `‖s‖ < r₂`. -/
theorem setAverage_log_norm_eval_sub_le (P : MvPolynomial ι ℂ) {D : ℕ}
    (hD : P.totalDegree ≤ D) (c : EuclideanSpace ℂ ι) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁)
    (h : r₁ ≤ r₂) :
    0 ≤ (⨍ z in ball c r₂, Real.log ‖eval z.ofLp P‖) -
        ⨍ z in ball c r₁, Real.log ‖eval z.ofLp P‖ ∧
      (⨍ z in ball c r₂, Real.log ‖eval z.ofLp P‖) -
          ⨍ z in ball c r₁, Real.log ‖eval z.ofLp P‖ ≤
        D * Real.log (r₂ / r₁) *
          (volume.real {v ∈ ball (0 : EuclideanSpace ℂ ι) 1 |
              ∃ s : ℂ, ‖s‖ < r₂ ∧ eval (c + s • v).ofLp P = 0} /
            volume.real (ball (0 : EuclideanSpace ℂ ι) 1)) := by
  have hL : 0 ≤ Real.log (r₂ / r₁) := Real.log_nonneg ((one_le_div hr₁).2 h)
  rcases eq_or_ne P 0 with rfl | hP
  · simp only [map_zero, norm_zero, Real.log_zero, average_zero, sub_self, le_refl, true_and]
    positivity
  obtain ⟨M, hM⟩ := exists_log_norm_eval_le_log P c r₂
  have k₁ := setLIntegral_ofReal_log_sub_circleAverage hP hr₁ h hM
  have k₂ := setLIntegral_ofReal_log_sub_circleAverage hP (hr₁.trans_le h) le_rfl hM
  set B := ball (0 : EuclideanSpace ℂ ι) 1
  set S := {v ∈ B | ∃ s : ℂ, ‖s‖ < r₂ ∧ eval (c + s • v).ofLp P = 0}
  set A : EuclideanSpace ℂ ι → ℝ → ℝ := fun v ρ =>
    Real.circleAverage (fun s : ℂ => Real.log ‖eval (c + s • v).ofLp P‖) 0 ρ with hA
  have hB : 0 < volume.real B :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  have pw (v : EuclideanSpace ℂ ι) := circleAverage_log_norm_eval_line_sub hD c v hr₁ h
  constructor
  · have hle : ∫⁻ v in B, ENNReal.ofReal (Real.log M - A v r₂) ≤
        ∫⁻ v in B, ENNReal.ofReal (Real.log M - A v r₁) :=
      lintegral_mono fun v => ENNReal.ofReal_le_ofReal (by linarith [(pw v).1])
    simp only [hA] at hle
    rw [k₁.2, k₂.2, ENNReal.ofReal_le_ofReal_iff (mul_nonneg hB.le k₁.1)] at hle
    linarith [le_of_mul_le_mul_left hle hB]
  set T := toMeasurable volume S
  have hT : MeasurableSet T := measurableSet_toMeasurable _ _
  have hSfin : volume S ≠ ∞ := ((measure_mono (sep_subset _ _)).trans_lt measure_ball_lt_top).ne
  have hup : ∫⁻ v in B, ENNReal.ofReal (Real.log M - A v r₁) ≤
      ∫⁻ v in B, (ENNReal.ofReal (Real.log M - A v r₂) +
        T.indicator (fun _ => ENNReal.ofReal (D * Real.log (r₂ / r₁))) v) := by
    refine setLIntegral_mono' measurableSet_ball fun v hv => ?_
    by_cases hvS : v ∈ S
    · rw [indicator_of_mem (subset_toMeasurable _ _ hvS)]
      exact (ENNReal.ofReal_le_ofReal (by linarith [(pw v).2.1])).trans ENNReal.ofReal_add_le
    · have h0 := (pw v).2.2 fun s hs h0 => hvS ⟨hv, s, hs, h0⟩
      rw [show Real.log M - A v r₁ = Real.log M - A v r₂ by simp only [hA]; linarith]
      exact le_self_add
  have hind : ∫⁻ v in B, (ENNReal.ofReal (Real.log M - A v r₂) +
        T.indicator (fun _ => ENNReal.ofReal (D * Real.log (r₂ / r₁))) v) ≤
      (∫⁻ v in B, ENNReal.ofReal (Real.log M - A v r₂)) +
        ENNReal.ofReal (D * Real.log (r₂ / r₁)) * volume S := by
    rw [lintegral_add_right _ (measurable_const.indicator hT), lintegral_indicator_const hT]
    exact add_le_add_right (mul_le_mul_of_nonneg_left
      ((Measure.restrict_apply_le _ _).trans (measure_toMeasurable S).le) bot_le) _
  have hup' := hup.trans hind
  simp only [hA] at hup'
  rw [k₁.2, k₂.2, ← ofReal_measureReal hSfin, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (mul_nonneg hB.le k₂.1) (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by have := k₂.1; positivity)] at hup'
  rw [← mul_div_assoc, le_div_iff₀ hB]
  nlinarith

/-- **The averages of `log ‖P‖` about a zero grow at least logarithmically.** If a nonzero
complex polynomial `P` on `EuclideanSpace ℂ ι` vanishes at `y`, then for `0 < r₁ ≤ r₂` the
average of `log ‖P‖` over `Metric.ball y r₂` exceeds that over `Metric.ball y r₁` by at least
`log (r₂ / r₁)`. -/
theorem log_div_le_setAverage_log_norm_eval_sub {P : MvPolynomial ι ℂ} (hP : P ≠ 0)
    {y : EuclideanSpace ℂ ι} (hy : eval y.ofLp P = 0) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁)
    (h : r₁ ≤ r₂) :
    Real.log (r₂ / r₁) ≤ (⨍ z in ball y r₂, Real.log ‖eval z.ofLp P‖) -
      ⨍ z in ball y r₁, Real.log ‖eval z.ofLp P‖ := by
  have hL : 0 ≤ Real.log (r₂ / r₁) := Real.log_nonneg ((one_le_div hr₁).2 h)
  obtain ⟨M, hM⟩ := exists_log_norm_eval_le_log P y r₂
  have k₁ := setLIntegral_ofReal_log_sub_circleAverage hP hr₁ h hM
  have k₂ := setLIntegral_ofReal_log_sub_circleAverage hP (hr₁.trans_le h) le_rfl hM
  set B := ball (0 : EuclideanSpace ℂ ι) 1
  set A : EuclideanSpace ℂ ι → ℝ → ℝ := fun v ρ =>
    Real.circleAverage (fun s : ℂ => Real.log ‖eval (y + s • v).ofLp P‖) 0 ρ with hA
  have hB : 0 < volume.real B :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  have hae : ∀ᵐ v : EuclideanSpace ℂ ι, eval (y + v).ofLp P ≠ 0 :=
    (measurePreserving_add_left volume y).quasiMeasurePreserving.ae (ae_eval_ne_zero hP)
  have hlow : ∫⁻ v in B, (ENNReal.ofReal (Real.log M - A v r₂) +
      ENNReal.ofReal (Real.log (r₂ / r₁))) ≤
        ∫⁻ v in B, ENNReal.ofReal (Real.log M - A v r₁) := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae hae] with v hvB hv
    have hd := log_div_le_circleAverage_log_norm_eval_line_sub hy ⟨1, by simpa using hv⟩ hr₁ h
    have hA₂ : A v r₂ ≤ Real.log M :=
      circleAverage_log_norm_eval_line_le (hr₁.trans_le h).le le_rfl hM hvB
    rw [← ENNReal.ofReal_add (sub_nonneg.2 hA₂) hL]
    exact ENNReal.ofReal_le_ofReal (by simp only [hA] at hA₂ ⊢; linarith)
  simp only [hA] at hlow
  rw [lintegral_add_right _ measurable_const, setLIntegral_const, k₁.2, k₂.2,
    ← ofReal_measureReal (measure_ball_lt_top (x := (0 : EuclideanSpace ℂ ι))).ne,
    ← ENNReal.ofReal_mul hL, ← ENNReal.ofReal_add (mul_nonneg hB.le k₂.1) (by positivity),
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg hB.le k₁.1)] at hlow
  nlinarith

end MvPolynomial

end
