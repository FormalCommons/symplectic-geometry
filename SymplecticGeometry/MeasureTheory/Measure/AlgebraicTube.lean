/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.Complex.MvPolynomial.LogAverage
import Mathlib.Analysis.Convex.Mul
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import SymplecticGeometry.MeasureTheory.Integral.Average
import SymplecticGeometry.Topology.Algebra.MvPolynomial
import TauCeti.MeasureTheory.Measure.Haar.Average

/-!
# Volumes of tubes around complex algebraic hypersurfaces

Let `P` be a nonzero complex polynomial of total degree at most `D` on `EuclideanSpace ℂ ι`, and
write `V c r` for the average of `log ‖P‖` over `Metric.ball c r`. This file aims at a bound on
the volume of the points near the zero set of `P`, found by counting, for a point `c` close to a
zero `y`, the complex lines through `c` that meet the zero set near `c`.

## Main results

* `MvPolynomial.setAverage_log_norm_eval_sub_ge_of_dist_lt` (change of centre): let `K` be at
  least `2 * (2 * m + (2 * m + 4 ^ m) * 4 ^ m)`, where `m = card ι`. If `P y = 0` and
  `dist c y < a`, then with `ρ₁ = K * D * a`, `log 4 / 2 ≤ V c (4 * ρ₁) - V c ρ₁`.
* `MvPolynomial.volume_ball_le_mul_volume_setOf_exists_root`: under the same hypotheses, the
  directions `v` in the unit ball for which `P` vanishes at some `c + s • v` with
  `‖s‖ < 4 * ρ₁` have at least `1 / (2 * D)` of the volume of the unit ball.

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

No published source is known to us for this argument. Its idea, counting the zeros of `P` on the
complex lines through a point, is the one behind Lelong numbers and Crofton's formula; the bound
on `L - V y R` is a form of the Bernstein–Walsh inequality.

## References

* [M. Klimek, *Pluripotential Theory*, Oxford University Press, 1991], Chapter 5 (the
  Bernstein–Walsh inequality)
-/

public section

open MeasureTheory Metric Set
open scoped ENNReal Real

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
  have hD1 : (1 : ℝ) ≤ D := by
    refine Nat.one_le_cast.2 (Nat.one_le_iff_ne_zero.2 fun h0 => hP ?_)
    have hC := totalDegree_eq_zero_iff_eq_C.1 (Nat.le_zero.1 (h0 ▸ hD))
    rw [hC, eval_C] at hy
    rw [hC, hy, map_zero]
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
theorem volume_ball_le_mul_volume_setOf_exists_root {P : MvPolynomial ι ℂ} (hP : P ≠ 0) {D : ℕ}
    (hD : P.totalDegree ≤ D) {K : ℝ}
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

end MvPolynomial

end
