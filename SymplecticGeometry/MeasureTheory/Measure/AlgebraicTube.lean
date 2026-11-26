/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.MetricSpace.Thickening
public import SymplecticGeometry.Analysis.Complex.MvPolynomial.LogAverage
import Mathlib.Analysis.Convex.Mul
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import SymplecticGeometry.Algebra.MvPolynomial.Degrees
import SymplecticGeometry.MeasureTheory.Integral.Average
import SymplecticGeometry.MeasureTheory.Measure.Lebesgue.LineSlice
import SymplecticGeometry.RingTheory.MvPolynomial.LineRestriction
import SymplecticGeometry.Topology.Algebra.MvPolynomial
import TauCeti.MeasureTheory.Measure.Haar.Average
import TauCeti.RingTheory.MvPolynomial.Homogeneous
import TauCeti.RingTheory.MvPolynomial.Rescale

/-!
# Volumes of tubes around complex algebraic hypersurfaces

Let `P` be a nonzero complex polynomial of total degree at most `D` on `EuclideanSpace ℂ ι`, and
write `V c r` for the average of `log ‖P‖` over `Metric.ball c r`. This file proves a bound on
the volume of the points near the zero set of `P`, found by counting, for a point `c` close to a
zero `y`, the complex lines through `c` that meet the zero set near `c`, and integrating that
count over the points near the zero set.

## Main results

* `MvPolynomial.setAverage_log_norm_eval_sub_ge_of_dist_lt` (change of centre): let `K` be at
  least `2 * (2 * m + (2 * m + 4 ^ m) * 4 ^ m)`, where `m = card ι`. If `P y = 0` and
  `dist c y < a`, then with `ρ₁ = K * D * a`, `log 4 / 2 ≤ V c (4 * ρ₁) - V c ρ₁`.
* `MvPolynomial.volume_ball_le_mul_volume_setOfPred_exists_root`: under the same hypotheses, the
  directions `v` in the unit ball for which `P` vanishes at some `c + s • v` with
  `‖s‖ < 4 * ρ₁` have at least `1 / (2 * D)` of the volume of the unit ball.
* `MvPolynomial.volume_thickening_zeroLocus_le_pow_four_mul_sq`: the part of the `t`-thickening
  of the zero set of `P` in the unit ball has volume at most `C * D ^ 4 * t ^ 2`, with `C`
  depending on `ι` only, not on `P`, `D` or `t`.
* `MvPolynomial.volume_thickening_zeroLocus_le`: the same volume is at most
  `C * D ^ (2 * card ι) * t`.
* `MvPolynomial.volume_thickening_zeroLocus_inter_ball_le`: on the ball of radius `r` about `0`,
  the same volume is at most `C * D ^ (2 * card ι) * r ^ (2 * card ι) * (t / r)`.

## The change of centre

Let `R = 4 * ρ₁ + a` and let `L` be the logarithm of the largest value of `‖P‖` on
`Metric.closedBall y R`. On every ball `B` inside `Metric.ball y R`, `L - log ‖P‖` is
nonnegative almost everywhere, so its average over `B` is `L - V` and is also its lower average.
Since `Metric.ball y (ρ₁ - a) ⊆ Metric.ball c ρ₁` and `Metric.ball c (4 * ρ₁) ⊆ Metric.ball y R`,
Tau Ceti's `TauCeti.setLAverage_ball_le` compares these averages about `c` and about `y`, up to
factors `(1 - e) ^ (2 * m)` and `(1 + e / 4) ^ (2 * m)` with `e = 1 / (K * D)`. About the zero
`y`, `MvPolynomial.log_div_le_setAverage_log_norm_eval_sub` gives
`V y R - V y (ρ₁ - a) ≥ log 4`, and `MvPolynomial.log_sup_sub_setAverage_log_norm_eval_le`
bounds `L - V y R` by `4 ^ m * D * log 4`. In the loss from moving the centre the factor `D`
of this bound meets the factor `1 / D` of `e`, so a constant `K` depending on `m` alone
suffices. The second result follows from the first and
`MvPolynomial.setAverage_log_norm_eval_sub_le`.

## The volume bound

Let `T` be the part of the `t`-thickening of the zero set `Z` in the unit ball `B`, and
`ρ = 4 * (K * D * t)`. Each `c ∈ T` is within `t` of a zero, so by the change of centre at least
`1 / (2 * D)` of the directions `v ∈ B` give a line `s ↦ c + s • v` that meets `Z` within
`‖s‖ ≤ ρ`. The pairs `(c, v)` with this property form a closed set
(`IsClosed.setOfPred_exists_norm_le_fst_add_smul_snd_mem`), so Tonelli's theorem applies to its
indicator on `T × B`, and `volume B * volume T` is at most `2 * D` times the integral over
`v ∈ B` of the volume of the `c ∈ T` that reach `Z` along `v`. For almost every `v` the top
homogeneous component of `P` does not vanish at `v` (`MvPolynomial.ae_eval_ne_zero`), so every
line in the direction `v` meets `Z` in at most `D` points
(`MvPolynomial.encard_setOfPred_eval_add_smul_eq_zero_le`), and
`MeasureTheory.volume_setOfPred_exists_add_smul_mem_le` bounds that volume by a constant times
`D * ρ ^ 2`. This gives `C * D ^ 4 * t ^ 2`. As the volume is also at most that of `B`, it is at
most a constant times `D ^ 2 * t`, by cases on whether `D ^ 2 * t ≤ 1`, and `D ^ 2 ≤ D ^ (2 * m)`
when `Z` is not empty, since then `P` is not constant.

No published source is known to us for this argument. Its idea, counting the zeros of `P` on the
complex lines through a point, is the one behind Lelong numbers and Crofton's formula; the bound
on `L - V y R` is a form of the Bernstein–Walsh inequality.

## References

* [M. Klimek, *Pluripotential Theory*, Oxford University Press, 1991], Chapter 5 (the
  Bernstein–Walsh inequality)
-/

public section

open MeasureTheory Metric Set
open scoped ENNReal Pointwise Real

namespace MvPolynomial

variable {ι : Type*} [Fintype ι]

/-- The volume ratios of the change of centre: for `0 < a` with `2 * a ≤ ρ` and `e = a / ρ`,
`((ρ - a) / ρ) ^ (2 * m)` is at least `1 - 2 * m * e`, and `((4 * ρ + a) / (4 * ρ)) ^ (2 * m)` is
at most `1 + 4 ^ m * e`. -/
private theorem ratio_pow_bounds (m : ℕ) {a ρ : ℝ} (ha : 0 < a) (h : 2 * a ≤ ρ) :
    1 - 2 * m * (a / ρ) ≤ ((ρ - a) / ρ) ^ (2 * m) ∧
      ((4 * ρ + a) / (4 * ρ)) ^ (2 * m) ≤ 1 + 4 ^ m * (a / ρ) := by
  have hρ : 0 < ρ := by linarith
  have he0 : 0 < a / ρ := div_pos ha hρ
  have he1 : a / ρ ≤ 1 / 2 := by rw [div_le_iff₀ hρ]; linarith
  constructor
  · have h := one_add_mul_le_pow (a := -(a / ρ)) (by linarith) (2 * m)
    rw [show (ρ - a) / ρ = 1 + -(a / ρ) by field_simp; ring]
    push_cast at h
    linarith
  · -- `x ↦ x ^ (2 * m)` is convex, so on `[1, 2]` its graph lies below the chord
    have h : (1 + a / ρ / 4) ^ (2 * m) ≤ 1 + (2 ^ (2 * m) - 1) * (a / ρ / 4) := by
      have := (convexOn_pow (2 * m)).2 (Set.mem_Ici.2 zero_le_one) (Set.mem_Ici.2 zero_le_two)
        (sub_nonneg.2 (by linarith : a / ρ / 4 ≤ 1)) (by positivity : (0 : ℝ) ≤ a / ρ / 4)
        (sub_add_cancel 1 (a / ρ / 4))
      simp only [smul_eq_mul, one_pow, mul_one] at this
      linear_combination this
    rw [show (2 : ℝ) ^ (2 * m) = 4 ^ m by rw [pow_mul]; norm_num] at h
    rw [show (4 * ρ + a) / (4 * ρ) = 1 + a / ρ / 4 by field_simp]
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 4 ^ m) he0.le]

/-- The arithmetic of the change of centre, with `e = 1 / (K * D)`, `X` the gap between `log M`
and the average about the zero over the large ball, and `Y₁`, `Y₂` those about the new centre. -/
private theorem log_four_div_two_le_sub {m : ℕ} {D K e X Y₁ Y₂ : ℝ} (hD : 1 ≤ D) (he : 0 < e)
    (heKD : e * (K * D) = 1) (hK : 2 * (2 * m + (2 * m + 4 ^ m) * 4 ^ m) ≤ K)
    (hX : X ≤ 4 ^ m * D * Real.log 4) (hY₁ : (1 - 2 * m * e) * (X + Real.log 4) ≤ Y₁)
    (hY₂ : Y₂ ≤ (1 + 4 ^ m * e) * X) :
    Real.log 4 / 2 ≤ Y₁ - Y₂ := by
  have h1 : (2 * m + 4 ^ m) * e * X ≤ (2 * m + 4 ^ m) * e * (4 ^ m * D * Real.log 4) :=
    mul_le_mul_of_nonneg_left hX (by positivity)
  have h2 : 2 * m * e * Real.log 4 ≤ 2 * m * e * D * Real.log 4 := by
    have := mul_le_mul_of_nonneg_left hD (by positivity : (0 : ℝ) ≤ 2 * m * e * Real.log 4)
    linarith
  have h3 : 2 * (2 * m + (2 * m + 4 ^ m) * 4 ^ m) * (e * D * Real.log 4) ≤
      K * (e * D * Real.log 4) :=
    mul_le_mul_of_nonneg_right hK (by positivity)
  have h4 : K * (e * D * Real.log 4) = Real.log 4 := by
    linear_combination Real.log 4 * heKD
  nlinarith

/-- **Change of centre for the averages of `log ‖P‖`.** Let `P` be a nonzero complex polynomial
on `EuclideanSpace ℂ ι` of total degree at most `D`, vanishing at `y`, and let `dist c y < a`.
If `K ≥ 2 * (2 * m + (2 * m + 4 ^ m) * 4 ^ m)`, where `m = card ι`, then with `ρ₁ = K * D * a`,
the average of `log ‖P‖` over `Metric.ball c (4 * ρ₁)` exceeds that over `Metric.ball c ρ₁` by
at least `log 4 / 2`. -/
theorem setAverage_log_norm_eval_sub_ge_of_dist_lt {P : MvPolynomial ι ℂ} (hP : P ≠ 0) {D : ℕ}
    (hD : P.totalDegree ≤ D) {K : ℝ}
    (hK : 2 * (2 * Fintype.card ι + (2 * Fintype.card ι + 4 ^ Fintype.card ι) *
      4 ^ Fintype.card ι) ≤ K)
    {y c : EuclideanSpace ℂ ι} (hy : eval y.ofLp P = 0) {a : ℝ} (hc : dist c y < a) :
    Real.log 4 / 2 ≤ (⨍ z in ball c (4 * (K * D * a)), Real.log ‖eval z.ofLp P‖) -
      ⨍ z in ball c (K * D * a), Real.log ‖eval z.ofLp P‖ := by
  set m := Fintype.card ι
  set V : EuclideanSpace ℂ ι → ℝ → ℝ := fun x r => ⨍ z in ball x r, Real.log ‖eval z.ofLp P‖
    with hV
  have ha : 0 < a := dist_nonneg.trans_lt hc
  -- `D ≥ 1`, since a polynomial of degree `0` with a zero is `0`.
  have hD1 : (1 : ℝ) ≤ D := Nat.one_le_cast.2
    ((Nat.one_le_iff_ne_zero.2 (totalDegree_ne_zero_of_eval_eq_zero hP hy)).trans hD)
  have hm : (2 : ℝ) ≤ 2 * (2 * m + (2 * m + 4 ^ m) * 4 ^ m) := by
    have : (1 : ℝ) ≤ 4 ^ m := one_le_pow₀ (by norm_num)
    nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hK2 : 2 ≤ K := hm.trans hK
  set ρ₁ := K * D * a with hρ₁
  set R := 4 * ρ₁ + a with hR
  have hKD : 2 ≤ K * D := by nlinarith
  have hρa : 2 * a ≤ ρ₁ := by rw [hρ₁]; nlinarith
  have hρ₁a : 0 < ρ₁ - a := by linarith
  have hRpos : 0 < R := by linarith
  -- The bound `‖P‖ ≤ M` on `ball y R`, with `M` the maximum of `‖P‖` on `closedBall y R`.
  set M := sSup ((fun z => ‖eval z.ofLp P‖) '' closedBall y R)
  have hbdd : BddAbove ((fun z => ‖eval z.ofLp P‖) '' closedBall y R) :=
    ((isCompact_closedBall y R).image (by fun_prop)).bddAbove
  have hM : ∀ z ∈ ball y R, ‖eval z.ofLp P‖ ≤ M := fun z hz =>
    le_csSup hbdd (mem_image_of_mem _ (ball_subset_closedBall hz))
  -- On a ball inside `ball y R`, `log M` bounds the average of `log ‖P‖`, and the lower average
  -- of `ofReal (log M - log ‖P‖)` is `ofReal` of their difference.
  have k {x : EuclideanSpace ℂ ι} {r : ℝ} (hr : 0 < r) (hs : ball x r ⊆ ball y R) :
      0 ≤ Real.log M - ⨍ z in ball x r, Real.log ‖eval z.ofLp P‖ ∧
        ⨍⁻ z in ball x r, ENNReal.ofReal (Real.log M - Real.log ‖eval z.ofLp P‖) =
          ENNReal.ofReal (Real.log M - ⨍ z in ball x r, Real.log ‖eval z.ofLp P‖) := by
    have hae := ae_restrict_log_norm_eval_le_log hP measurableSet_ball fun z hz => hM z (hs hz)
    exact ⟨sub_nonneg.2 (setAverage_log_norm_eval_le_of_ae_le hP hr hae),
      setLAverage_ofReal_sub_eq (measure_ball_pos volume x hr).ne' measure_ball_lt_top.ne
        (integrableOn_log_norm_eval_ball hP x r) hae⟩
  have hs₁ : ball y (ρ₁ - a) ⊆ ball c ρ₁ := ball_subset_ball' (by rw [dist_comm]; linarith)
  have hs₂ : ball c (4 * ρ₁) ⊆ ball y R := ball_subset_ball' (by rw [hR]; linarith)
  have hs₃ : ball c ρ₁ ⊆ ball y R := (ball_subset_ball (by linarith)).trans hs₂
  have hs₄ : ball y (ρ₁ - a) ⊆ ball y R := hs₁.trans hs₃
  have kY₁ := k (by linarith) hs₃
  have kY₂ := k (by linarith) hs₂
  have kX₁ := k hρ₁a hs₄
  have kX₂ := k hRpos subset_rfl
  have hfin : Module.finrank ℝ (EuclideanSpace ℂ ι) = 2 * m := by
    rw [finrank_real_of_complex, finrank_euclideanSpace]
  -- The comparisons of the lower averages over nested balls.
  have c₁ := TauCeti.setLAverage_ball_le (μ := volume)
    (fun z => ENNReal.ofReal (Real.log M - Real.log ‖eval z.ofLp P‖)) hρ₁a hs₁
  have c₂ := TauCeti.setLAverage_ball_le (μ := volume)
    (fun z => ENNReal.ofReal (Real.log M - Real.log ‖eval z.ofLp P‖)) (by linarith) hs₂
  rw [kX₁.2, kY₁.2, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by positivity) kY₁.1), hfin] at c₁
  rw [kX₂.2, kY₂.2, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by positivity) kX₂.1), hfin] at c₂
  -- About the zero `y`, and the bound by the maximum.
  have hd := log_div_le_setAverage_log_norm_eval_sub hP hy hρ₁a (by linarith : ρ₁ - a ≤ R)
  have hlog4 : Real.log 4 ≤ Real.log (R / (ρ₁ - a)) :=
    Real.log_le_log (by norm_num) ((le_div_iff₀ hρ₁a).2 (by linarith))
  have hb := log_sup_sub_setAverage_log_norm_eval_le P hD y hRpos
  -- The algebra, with `e = a / ρ₁ = 1 / (K * D)`.
  have hρ₁0 : 0 < ρ₁ := by linarith
  have heKD : a / ρ₁ * (K * D) = 1 := by rw [hρ₁]; field_simp
  obtain ⟨hγ, hβ⟩ := ratio_pow_bounds m ha hρa
  refine (log_four_div_two_le_sub (X := Real.log M - V y R) (Y₁ := Real.log M - V c ρ₁)
    (Y₂ := Real.log M - V c (4 * ρ₁)) hD1 (div_pos ha hρ₁0) heKD hK
    hb ?_ ?_).trans_eq (by simp only [hV]; ring)
  · have hγq : ((ρ₁ - a) / ρ₁) ^ (2 * m) * (ρ₁ / (ρ₁ - a)) ^ (2 * m) = 1 := by
      rw [← mul_pow, div_mul_div_comm, mul_comm (ρ₁ - a), div_self (by positivity), one_pow]
    calc (1 - 2 * m * (a / ρ₁)) * (Real.log M - V y R + Real.log 4)
        ≤ ((ρ₁ - a) / ρ₁) ^ (2 * m) * (Real.log M - V y (ρ₁ - a)) :=
          mul_le_mul hγ (by simp only [hV] at hd ⊢; linarith)
            (by linarith [kX₂.1, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]) (by positivity)
      _ ≤ ((ρ₁ - a) / ρ₁) ^ (2 * m) * ((ρ₁ / (ρ₁ - a)) ^ (2 * m) * (Real.log M - V c ρ₁)) :=
          mul_le_mul_of_nonneg_left c₁ (by positivity)
      _ = Real.log M - V c ρ₁ := by rw [← mul_assoc, hγq, one_mul]
  · exact c₂.trans (mul_le_mul_of_nonneg_right hβ kX₂.1)

/-- **Many complex lines through `c` meet the zero set near `c`.** Under the hypotheses of
`MvPolynomial.setAverage_log_norm_eval_sub_ge_of_dist_lt`, the volume of the unit ball of
`EuclideanSpace ℂ ι` is at most `2 * D` times that of the set of `v` in it for which `P` vanishes
at some `c + s • v` with `‖s‖ < 4 * (K * D * a)`. -/
theorem volume_ball_le_mul_volume_setOfPred_exists_root {P : MvPolynomial ι ℂ}
    (hP : P ≠ 0) {D : ℕ} (hD : P.totalDegree ≤ D) {K : ℝ}
    (hK : 2 * (2 * Fintype.card ι + (2 * Fintype.card ι + 4 ^ Fintype.card ι) *
      4 ^ Fintype.card ι) ≤ K)
    {y c : EuclideanSpace ℂ ι} (hy : eval y.ofLp P = 0) {a : ℝ} (hc : dist c y < a) :
    volume (ball (0 : EuclideanSpace ℂ ι) 1) ≤
      2 * D * volume {v ∈ ball (0 : EuclideanSpace ℂ ι) 1 |
        ∃ s : ℂ, ‖s‖ < 4 * (K * D * a) ∧ eval (c + s • v).ofLp P = 0} := by
  set S := {v ∈ ball (0 : EuclideanSpace ℂ ι) 1 |
    ∃ s : ℂ, ‖s‖ < 4 * (K * D * a) ∧ eval (c + s • v).ofLp P = 0}
  have h1 := setAverage_log_norm_eval_sub_ge_of_dist_lt hP hD hK hy hc
  have hρ : 0 < K * D * a := by
    by_contra! h
    rw [ball_eq_empty.2 (by linarith : 4 * (K * D * a) ≤ 0),
      ball_eq_empty.2 h] at h1
    simp only [Measure.restrict_empty, sub_self] at h1
    linarith [Real.log_pos (by norm_num : (1 : ℝ) < 4)]
  have h2 := (setAverage_log_norm_eval_sub_le P hD c hρ (r₂ := 4 * (K * D * a)) (by linarith)).2
  rw [mul_div_assoc, div_self hρ.ne', mul_one] at h2
  have hB : 0 < volume.real (ball (0 : EuclideanSpace ℂ ι) 1) :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  have hSfin : volume S ≠ ∞ :=
    ((measure_mono (sep_subset _ _)).trans_lt measure_ball_lt_top).ne
  have hlog : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hle : volume.real (ball (0 : EuclideanSpace ℂ ι) 1) ≤ 2 * D * volume.real S := by
    have h3 := h1.trans h2
    rw [mul_div_assoc', le_div_iff₀ hB] at h3
    nlinarith
  rw [← ofReal_measureReal measure_ball_lt_top.ne, ← ofReal_measureReal hSfin]
  refine (ENNReal.ofReal_le_ofReal hle).trans_eq ?_
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
  simp

/-- **Volumes of tubes around complex algebraic hypersurfaces, `D ^ 4 * t ^ 2` form.** There is
a constant `C`, depending only on `ι` and not on `P`, `D` or `t`, such that for every nonzero
complex polynomial `P` on `EuclideanSpace ℂ ι` of total degree at most `D` and every `t`, the
part of the `t`-thickening of the zero set of `P` inside the unit ball has volume at most
`C * D ^ 4 * t ^ 2`. -/
theorem volume_thickening_zeroLocus_le_pow_four_mul_sq : ∃ C : ℝ, ∀ P : MvPolynomial ι ℂ,
    P ≠ 0 → ∀ D : ℕ, P.totalDegree ≤ D → ∀ t : ℝ,
      volume (thickening t {z : EuclideanSpace ℂ ι | eval z.ofLp P = 0} ∩
        ball (0 : EuclideanSpace ℂ ι) 1) ≤ ENNReal.ofReal (C * D ^ 4 * t ^ 2) := by
  set m := Fintype.card ι
  set K : ℝ := 2 * (2 * m + (2 * m + 4 ^ m) * 4 ^ m)
  refine ⟨128 * K ^ 2 * volume.real (ball (0 : EuclideanSpace ℂ ι) 2),
    fun P hP D hD t ↦ ?_⟩
  set Z := {z : EuclideanSpace ℂ ι | eval z.ofLp P = 0}
  set B := ball (0 : EuclideanSpace ℂ ι) 1
  set T := thickening t Z ∩ B
  set ρ := 4 * (K * D * t)
  set F := {q : EuclideanSpace ℂ ι × EuclideanSpace ℂ ι | ∃ s : ℂ, ‖s‖ ≤ ρ ∧ q.1 + s • q.2 ∈ Z}
  rcases T.eq_empty_or_nonempty with hT | ⟨c₀, hc₀⟩
  · simp [hT]
  obtain ⟨y₀, hy₀, hcy₀⟩ := mem_thickening_iff.1 hc₀.1
  have ht : 0 < t := dist_nonneg.trans_lt hcy₀
  have hD1 : (1 : ℝ) ≤ D := Nat.one_le_cast.2
    ((Nat.one_le_iff_ne_zero.2 (totalDegree_ne_zero_of_eval_eq_zero hP hy₀)).trans hD)
  have hρ : 0 < ρ := by positivity
  have hZ : IsClosed Z := isClosed_eq (by fun_prop) continuous_const
  have hF : MeasurableSet F := (hZ.setOfPred_exists_norm_le_fst_add_smul_snd_mem ρ).measurableSet
  have hTm : MeasurableSet T := isOpen_thickening.measurableSet.inter measurableSet_ball
  have hB0 : volume B ≠ 0 := (measure_ball_pos volume 0 one_pos).ne'
  have hBt : volume B ≠ ∞ := measure_ball_lt_top.ne
  set N : ℝ≥0∞ :=
    ENNReal.ofReal (volume.real (ball (0 : EuclideanSpace ℂ ι) 2) * D * (2 * ρ) ^ 2)
  -- The change of centre, at each point of `T`.
  have h4 : ∀ c ∈ T, volume B ≤ 2 * D * ∫⁻ v in B, F.indicator 1 (c, v) := by
    intro c hc
    obtain ⟨y, hy, hcy⟩ := mem_thickening_iff.1 hc.1
    refine (volume_ball_le_mul_volume_setOfPred_exists_root hP hD le_rfl hy hcy).trans ?_
    have hm : MeasurableSet (Prod.mk c ⁻¹' F) := measurable_prodMk_left hF
    rw [show (fun v ↦ F.indicator 1 (c, v)) = (Prod.mk c ⁻¹' F).indicator 1 by
        funext v; exact (indicator_comp_right (g := 1) (Prod.mk c)).symm,
      lintegral_indicator_one hm, Measure.restrict_apply hm]
    gcongr
    rintro v ⟨hv, s, hs, h⟩
    exact ⟨⟨s, hs.le, h⟩, hv⟩
  -- The slices, in every direction off the zero set of the top homogeneous component.
  have h5 : ∀ᵐ v ∂volume.restrict B, ∫⁻ c in T, F.indicator 1 (c, v) ≤ N := by
    filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae
      (ae_eval_ne_zero (homogeneousComponent_totalDegree_ne_zero P hP))] with v hvB hv
    have hm : MeasurableSet ((fun c ↦ (c, v)) ⁻¹' F) := measurable_prodMk_right hF
    rw [show (fun c ↦ F.indicator 1 (c, v)) = ((fun c ↦ (c, v)) ⁻¹' F).indicator 1 by
        funext c; exact (indicator_comp_right (g := 1) fun c ↦ (c, v)).symm,
      lintegral_indicator_one hm, Measure.restrict_apply hm]
    have hN : ∀ c : EuclideanSpace ℂ ι, {s : ℂ | c + s • v ∈ Z}.encard ≤ D := fun c ↦ by
      refine le_trans ?_ (Nat.cast_le.2 hD)
      simpa [Z] using encard_setOfPred_eval_add_smul_eq_zero_le c.ofLp v.ofLp hv
    calc volume ((fun c ↦ (c, v)) ⁻¹' F ∩ T)
        ≤ volume {c ∈ B | ∃ s : ℂ, ‖s‖ < 2 * ρ ∧ c + s • v ∈ Z} :=
          measure_mono fun c ⟨⟨s, hs, h⟩, hc⟩ ↦ ⟨hc.2, s, by linarith, h⟩
      _ ≤ ENNReal.ofReal (volume.real (ball (0 : EuclideanSpace ℂ ι) 2) * D * (2 * ρ) ^ 2 *
          ‖v‖ ^ 2) := volume_setOfPred_exists_add_smul_mem_le hZ v D hN (2 * ρ)
      _ ≤ N := by
        refine ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right (by positivity) ?_)
        have := mem_ball_zero_iff.1 hvB
        nlinarith [norm_nonneg v]
  -- Tonelli's theorem on `T × B`.
  have key : volume B * volume T ≤ volume B * (2 * D * N) := by
    calc volume B * volume T = ∫⁻ _ in T, volume B := by rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ c in T, 2 * D * ∫⁻ v in B, F.indicator 1 (c, v) := setLIntegral_mono' hTm h4
      _ = 2 * D * ∫⁻ v in B, ∫⁻ c in T, F.indicator 1 (c, v) := by
        rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
          (ENNReal.natCast_ne_top D)), lintegral_lintegral_swap
          (f := fun c v ↦ F.indicator 1 (c, v))
          -- `Function.uncurry` of this function is `F.indicator 1` up to the eta rule for pairs
          (by exact (measurable_one.indicator hF).aemeasurable)]
      _ ≤ 2 * D * ∫⁻ _ in B, N := by gcongr 1; exact lintegral_mono_ae h5
      _ = volume B * (2 * D * N) := by rw [setLIntegral_const]; ring
  refine ((ENNReal.mul_le_mul_iff_right hB0 hBt).1 key).trans_eq ?_
  rw [show (2 * D : ℝ≥0∞) = ENNReal.ofReal (2 * D) by
      rw [ENNReal.ofReal_mul (by norm_num)]; simp, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [ρ]
  ring

/-- **Volumes of tubes around complex algebraic hypersurfaces.** Write `m = card ι`. There is a
constant `C`, depending only on `ι` and not on `P`, `D` or `t`, such that for every nonzero
complex polynomial `P` on `EuclideanSpace ℂ ι` of total degree at most `D` and every `t`, the
part of the `t`-thickening of the zero set of `P` inside the unit ball has volume at most
`C * D ^ (2 * m) * t`. -/
theorem volume_thickening_zeroLocus_le : ∃ C : ℝ, ∀ P : MvPolynomial ι ℂ, P ≠ 0 → ∀ D : ℕ,
    P.totalDegree ≤ D → ∀ t : ℝ,
      volume (thickening t {z : EuclideanSpace ℂ ι | eval z.ofLp P = 0} ∩
        ball (0 : EuclideanSpace ℂ ι) 1) ≤
        ENNReal.ofReal (C * D ^ (2 * Fintype.card ι) * t) := by
  obtain ⟨C₁, h₁⟩ := volume_thickening_zeroLocus_le_pow_four_mul_sq (ι := ι)
  set A := volume.real (ball (0 : EuclideanSpace ℂ ι) 1)
  refine ⟨A + max C₁ 0, fun P hP D hD t ↦ ?_⟩
  set Z := {z : EuclideanSpace ℂ ι | eval z.ofLp P = 0}
  set T := thickening t Z ∩ ball (0 : EuclideanSpace ℂ ι) 1
  rcases T.eq_empty_or_nonempty with hT | ⟨c₀, hc₀⟩
  · simp [hT]
  obtain ⟨y₀, hy₀, hcy₀⟩ := mem_thickening_iff.1 hc₀.1
  have ht : 0 < t := dist_nonneg.trans_lt hcy₀
  -- A zero exists, so `P` is not constant: `1 ≤ D` and `ι` is nonempty.
  have hne : P.totalDegree ≠ 0 := totalDegree_ne_zero_of_eval_eq_zero hP hy₀
  have hD1 : (1 : ℝ) ≤ D := Nat.one_le_cast.2 ((Nat.one_le_iff_ne_zero.2 hne).trans hD)
  have hm : 1 ≤ Fintype.card ι := by
    refine Nat.one_le_iff_ne_zero.2 fun h ↦ hne ?_
    have := Fintype.card_eq_zero_iff.1 h
    obtain ⟨a, rfl⟩ := C_surjective ι P
    exact totalDegree_C a
  have hA : volume T ≤ ENNReal.ofReal A := by
    rw [ofReal_measureReal measure_ball_lt_top.ne]
    exact measure_mono inter_subset_right
  have hC : volume T ≤ ENNReal.ofReal (max C₁ 0 * D ^ 4 * t ^ 2) :=
    (h₁ P hP D hD t).trans (ENNReal.ofReal_le_ofReal (by gcongr; exact le_max_left _ _))
  have hA0 : 0 ≤ A := measureReal_nonneg
  have hC0 : 0 ≤ max C₁ 0 := le_max_right _ _
  have hpow : (D : ℝ) ^ 2 ≤ D ^ (2 * Fintype.card ι) := pow_le_pow_right₀ hD1 (by omega)
  have hgoal : (A + max C₁ 0) * D ^ 2 * t ≤ (A + max C₁ 0) * D ^ (2 * Fintype.card ι) * t := by
    gcongr
  rcases le_or_gt ((D : ℝ) ^ 2 * t) 1 with h | h
  · refine hC.trans (ENNReal.ofReal_le_ofReal (le_trans ?_ hgoal))
    have : max C₁ 0 * D ^ 4 * t ^ 2 = max C₁ 0 * (D ^ 2 * t) * (D ^ 2 * t) := by ring
    rw [this]
    have hx : (0 : ℝ) ≤ D ^ 2 * t := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h (mul_nonneg hC0 hx), mul_nonneg hA0 hx]
  · refine hA.trans (ENNReal.ofReal_le_ofReal (le_trans ?_ hgoal))
    nlinarith [mul_le_mul_of_nonneg_left h.le hA0, mul_nonneg hC0 (by positivity :
      (0 : ℝ) ≤ D ^ 2 * t)]

/-- **Volumes of tubes around complex algebraic hypersurfaces, on a ball of any radius.** Write
`m = card ι`. There is a constant `C`, depending only on `ι` and not on `P`, `D`, `r` or `t`, such
that for every nonzero complex polynomial `P` on `EuclideanSpace ℂ ι` of total degree at most `D`,
every `0 < r` and every `t`, the part of the `t`-thickening of the zero set of `P` inside the ball
of radius `r` about `0` has volume at most `C * D ^ (2 * m) * r ^ (2 * m) * (t / r)`. -/
theorem volume_thickening_zeroLocus_inter_ball_le : ∃ C : ℝ, ∀ P : MvPolynomial ι ℂ, P ≠ 0 →
    ∀ D : ℕ, P.totalDegree ≤ D → ∀ r : ℝ, 0 < r → ∀ t : ℝ,
      volume (thickening t {z : EuclideanSpace ℂ ι | eval z.ofLp P = 0} ∩
        ball (0 : EuclideanSpace ℂ ι) r) ≤
        ENNReal.ofReal (C * D ^ (2 * Fintype.card ι) * r ^ (2 * Fintype.card ι) * (t / r)) := by
  obtain ⟨C₀, hC₀⟩ := volume_thickening_zeroLocus_le (ι := ι)
  refine ⟨C₀, fun P hP D hD r hr t ↦ ?_⟩
  -- The polynomial `z ↦ P (r • z)`.
  set Q := rescale (fun _ : ι ↦ (r : ℂ)) P
  have hQ : ∀ z : ι → ℂ, eval z Q = eval (fun i ↦ (r : ℂ) * z i) P := fun z ↦ by
    simpa using aeval_rescale (fun _ : ι ↦ (r : ℂ)) z P
  have hQ0 : Q ≠ 0 := fun h ↦ hP <| by
    rw [← rescale_rescale_of_mul_eq_one (b := fun _ ↦ (r : ℂ)⁻¹)
      (fun _ ↦ mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 hr.ne')) P]
    simp [Q] at h; simp [h]
  have hQD : Q.totalDegree ≤ D :=
    (totalDegree_le_of_support_subset (support_rescale_subset _ P)).trans hD
  set Z := {z : EuclideanSpace ℂ ι | eval z.ofLp P = 0}
  have hZ : (r • ·) ⁻¹' Z = {z : EuclideanSpace ℂ ι | eval z.ofLp Q = 0} := by
    ext z
    simp [Z, hQ, Pi.smul_def, Complex.real_smul]
  have hsub : r • (thickening (t / r) {z : EuclideanSpace ℂ ι | eval z.ofLp Q = 0} ∩ ball 0 1) =
      thickening t Z ∩ ball 0 r := by
    rw [← hZ, smul_set_inter₀ hr.ne', smul_unitBall_of_pos hr, ← add_ball_zero, smul_add,
      smul_ball hr.ne', smul_zero, Real.norm_of_nonneg hr.le, mul_div_cancel₀ _ hr.ne',
      preimage_smul₀ hr.ne', smul_inv_smul₀ hr.ne', add_ball_zero]
  rw [← hsub, Measure.addHaar_smul, finrank_real_of_complex, finrank_euclideanSpace,
    abs_of_pos (pow_pos hr _)]
  refine (?_ : _ ≤ ENNReal.ofReal (r ^ (2 * Fintype.card ι)) *
    ENNReal.ofReal (C₀ * D ^ (2 * Fintype.card ι) * (t / r))).trans_eq ?_
  · gcongr
    exact hC₀ Q hQ0 D hQD (t / r)
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

end MvPolynomial

end
