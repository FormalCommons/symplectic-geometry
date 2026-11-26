/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Polynomial.MahlerMeasure
public import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Log
import TauCeti.Analysis.Complex.JensenFormula

/-!
# Circle averages of `log ‖p‖` for complex polynomials

For a polynomial `p : ℂ[X]` and `r > 0`, Jensen's formula computes the average of
`log ‖p.eval z‖` over the circle `‖z‖ = r`: it is `log ‖p.leadingCoeff‖` plus, for each root `a`
counted with multiplicity, `log (max r ‖a‖)` (`Polynomial.circleAverage_log_norm_eval`). The
proof rescales the circle to the unit circle and applies Mathlib's formula for the logarithmic
Mahler measure, `Polynomial.logMahlerMeasure_eq_log_leadingCoeff_add_sum_log_roots`, to
`p.comp (C r * X)`.

Consequences for two radii `0 < r₁ ≤ r₂`: each root adds to the difference of the averages a
number between `0` and `log (r₂ / r₁)`, which is `log (r₂ / r₁)` for the root `0` and `0` for a
root of norm at least `r₂`. So the difference is at most `p.natDegree * log (r₂ / r₁)`, at least
`p.rootMultiplicity 0 * log (r₂ / r₁)`, and `0` when no root has norm less than `r₂`.

Finally, the maximum of `‖p‖` on the circle of radius `r` is at least the exponential of the
average, and so the maximum of `‖p‖` on the disc of radius `t * r` is at most
`(t + 1) ^ p.natDegree` times the maximum on the circle of radius `r`.

The sub-mean-value inequality `log ‖p.eval 0‖ ≤ circleAverage (fun z ↦ log ‖p.eval z‖) 0 r` for
`p.eval 0 ≠ 0` is not restated here: it is Tau Ceti's
`AnalyticOnNhd.log_norm_le_circleAverage_log_norm`. What is proved here is its consequence for the
lower average of `ofReal (log M - log ‖p‖)` when `‖p‖ ≤ M` on the circle: since `p` has
finitely many roots, `log M - log ‖p‖` is nonnegative at almost every point of the circle, and it
is circle-integrable, so that lower average is `ofReal` of its Bochner average.

## Main results

* `Polynomial.circleAverage_log_norm_eval`: Jensen's formula for polynomials at any radius.
* `Polynomial.circleAverage_log_norm_eval_sub_le`,
  `Polynomial.rootMultiplicity_mul_log_le_circleAverage_sub`,
  `Polynomial.circleAverage_log_norm_eval_sub_eq_zero`: bounds on the difference of the
  averages at two radii.
* `Polynomial.exp_circleAverage_log_norm_eval_le`: a bound for `‖p‖` on a circle bounds the
  exponential of the average.
* `Polynomial.exists_norm_eval_le_add_one_pow_mul`: growth of `‖p‖` from a circle to a disc.
* `Polynomial.setLAverage_ofReal_log_sub_log_norm_eval_circleMap_le`: the sub-mean value
  inequality in the form of a lower average.

## References

* L. V. Ahlfors, *Complex Analysis*, 3rd ed., McGraw-Hill, 1979, Ch. 5, §3.1.
* E. C. Titchmarsh, *The Theory of Functions*, 2nd ed., Oxford University Press, 1939, §3.61.
-/

public section

open Metric Real

namespace Polynomial

/-- **Jensen's formula for polynomials.** For `r > 0`, the average of `log ‖p.eval z‖` over the
circle of radius `r` about `0` is `log ‖p.leadingCoeff‖ + ∑ a ∈ p.roots, log (max r ‖a‖)`, the
roots counted with multiplicity. -/
theorem circleAverage_log_norm_eval (p : ℂ[X]) {r : ℝ} (hr : 0 < r) :
    circleAverage (fun z ↦ log ‖p.eval z‖) 0 r =
      log ‖p.leadingCoeff‖ + (p.roots.map fun a ↦ log (max r ‖a‖)).sum := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  set q := p.comp (C (r : ℂ) * X + C 0) with hq
  have havg : circleAverage (fun z ↦ log ‖p.eval z‖) 0 r = q.logMahlerMeasure := by
    rw [circleAverage_eq_circleAverage_zero_one, logMahlerMeasure_def]
    simp [hq, eval_comp]
  have hlc : q.leadingCoeff = p.leadingCoeff * (r : ℂ) ^ p.natDegree := by
    rw [hq, map_zero, add_zero, leadingCoeff_comp (by simp [natDegree_C_mul_X _ hr0]),
      leadingCoeff_C_mul_X]
  have hroots : p.roots = q.roots.map fun b ↦ (r : ℂ) * b + 0 :=
    (map_roots_comp_C_mul_X_add_C p _ _ (Ne.isUnit hr0)).symm
  have hcard : q.roots.card = p.natDegree := by
    rw [← IsAlgClosed.card_roots_eq_natDegree, hroots, Multiset.card_map]
  rw [havg, logMahlerMeasure_eq_log_leadingCoeff_add_sum_log_roots, hlc, hroots,
    Multiset.map_map]
  rcases eq_or_ne p 0 with rfl | hp
  · simp [hq]
  have hterm : ∀ b : ℂ, log (max r ‖(r : ℂ) * b + 0‖) = log r + log⁺ ‖b‖ := by
    intro b
    rw [add_zero, norm_mul, Complex.norm_real, norm_of_nonneg hr.le,
      show max r (r * ‖b‖) = r * max 1 ‖b‖ by rw [mul_max_of_nonneg _ _ hr.le, mul_one],
      log_mul hr.ne' (by positivity), posLog_eq_log_max_one (norm_nonneg b)]
  simp only [Function.comp_def, hterm, Multiset.sum_map_add, Multiset.map_const',
    Multiset.sum_replicate, hcard, norm_mul, norm_pow, Complex.norm_real, norm_of_nonneg hr.le,
    nsmul_eq_mul]
  rw [log_mul (by simpa using hp) (by positivity), log_pow]
  ring

/-- The difference of the averages of `log ‖p‖` over the circles of radii `r₂` and `r₁` is the sum
over the roots `a` of `log (max r₂ ‖a‖) - log (max r₁ ‖a‖)`. -/
theorem circleAverage_log_norm_eval_sub (p : ℂ[X]) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) :
    circleAverage (fun z ↦ log ‖p.eval z‖) 0 r₂ - circleAverage (fun z ↦ log ‖p.eval z‖) 0 r₁ =
      (p.roots.map fun a ↦ log (max r₂ ‖a‖) - log (max r₁ ‖a‖)).sum := by
  rw [circleAverage_log_norm_eval p hr₁, circleAverage_log_norm_eval p hr₂,
    Multiset.sum_map_sub]
  ring

/-- For `0 < r₁ ≤ r₂`, the average of `log ‖p‖` over the circle of radius `r₂` exceeds the one
over the circle of radius `r₁` by at most `p.natDegree * log (r₂ / r₁)`. -/
theorem circleAverage_log_norm_eval_sub_le (p : ℂ[X]) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁)
    (h : r₁ ≤ r₂) :
    circleAverage (fun z ↦ log ‖p.eval z‖) 0 r₂ - circleAverage (fun z ↦ log ‖p.eval z‖) 0 r₁ ≤
      p.natDegree * log (r₂ / r₁) := by
  have hr₂ := hr₁.trans_le h
  rw [circleAverage_log_norm_eval_sub p hr₁ hr₂, ← IsAlgClosed.card_roots_eq_natDegree,
    ← Multiset.card_map (fun a ↦ log (max r₂ ‖a‖) - log (max r₁ ‖a‖)), ← nsmul_eq_mul]
  refine Multiset.sum_le_card_nsmul _ _ fun x hx ↦ ?_
  obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hx
  rw [← log_div (by positivity) (by positivity)]
  refine log_le_log (by positivity) ?_
  rw [div_le_div_iff₀ (by positivity) hr₁]
  rcases le_total ‖a‖ r₁ with h₁ | h₁ <;> rcases le_total ‖a‖ r₂ with h₂ | h₂ <;>
    simp only [max_eq_left, max_eq_right, h₁, h₂] <;> nlinarith

/-- For `0 < r₁ ≤ r₂`, the average of `log ‖p‖` over the circle of radius `r₂` exceeds the one
over the circle of radius `r₁` by at least `p.rootMultiplicity 0 * log (r₂ / r₁)`. -/
theorem rootMultiplicity_mul_log_le_circleAverage_sub (p : ℂ[X]) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁)
    (h : r₁ ≤ r₂) :
    p.rootMultiplicity 0 * log (r₂ / r₁) ≤
      circleAverage (fun z ↦ log ‖p.eval z‖) 0 r₂ -
        circleAverage (fun z ↦ log ‖p.eval z‖) 0 r₁ := by
  classical
  have hr₂ := hr₁.trans_le h
  have hnn : ∀ a : ℂ, 0 ≤ log (max r₂ ‖a‖) - log (max r₁ ‖a‖) := fun a ↦
    sub_nonneg.2 (log_le_log (by positivity) (max_le_max_right _ h))
  rw [circleAverage_log_norm_eval_sub p hr₁ hr₂, Finset.sum_multiset_map_count]
  by_cases h0 : (0 : ℂ) ∈ p.roots.toFinset
  · refine le_trans ?_ (Finset.single_le_sum (fun a _ ↦ nsmul_nonneg (hnn a) _) h0)
    simp [count_roots, hr₁.le, hr₂.le, log_div hr₂.ne' hr₁.ne']
  · rw [← count_roots, Multiset.count_eq_zero.2 (by simpa using h0), Nat.cast_zero, zero_mul]
    exact Finset.sum_nonneg fun a _ ↦ nsmul_nonneg (hnn a) _

/-- For `0 < r₁ ≤ r₂`, if every root of `p` has norm at least `r₂`, then the averages of
`log ‖p‖` over the circles of radii `r₁` and `r₂` are equal. -/
theorem circleAverage_log_norm_eval_sub_eq_zero (p : ℂ[X]) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁)
    (h : r₁ ≤ r₂) (hroots : ∀ a ∈ p.roots, r₂ ≤ ‖a‖) :
    circleAverage (fun z ↦ log ‖p.eval z‖) 0 r₂ -
      circleAverage (fun z ↦ log ‖p.eval z‖) 0 r₁ = 0 := by
  rw [circleAverage_log_norm_eval_sub p hr₁ (hr₁.trans_le h)]
  refine Multiset.sum_eq_zero fun x hx ↦ ?_
  obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hx
  rw [max_eq_right (hroots a ha), max_eq_right (h.trans (hroots a ha)), sub_self]

/-- If `p ≠ 0` and `‖p‖ ≤ M` on the circle of radius `r > 0` about `0`, then the exponential of
the average of `log ‖p‖` over that circle is at most `M`. In particular `M > 0`. -/
theorem exp_circleAverage_log_norm_eval_le {p : ℂ[X]} (hp : p ≠ 0) {r M : ℝ} (hr : 0 < r)
    (hM : ∀ w : ℂ, ‖w‖ = r → ‖p.eval w‖ ≤ M) :
    exp (circleAverage (fun z ↦ log ‖p.eval z‖) 0 r) ≤ M := by
  set A := circleAverage (fun z ↦ log ‖p.eval z‖) 0 r
  -- Scaling `p` by `c > 0` with `c * M ≤ 1` makes `log ‖c • p‖ ≤ 0` on the circle, roots included,
  -- and its average is `log c + A` by Jensen's formula.
  have key : ∀ c : ℝ, 0 < c → c * M ≤ 1 → log c + A ≤ 0 := by
    intro c hc hcM
    have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
    have h := circleAverage_log_norm_eval (C (c : ℂ) * p) hr
    rw [leadingCoeff_mul, leadingCoeff_C, roots_C_mul _ hc0, norm_mul, Complex.norm_real,
      norm_of_nonneg hc.le, log_mul hc.ne' (by simpa using hp), add_assoc,
      ← circleAverage_log_norm_eval p hr] at h
    rw [← h]
    refine circleAverage_mono_on_of_le_circle
      (MeromorphicOn.circleIntegrable_log_norm fun z _ ↦
        ((C (c : ℂ) * p).differentiable.analyticAt z).meromorphicAt) fun w hw ↦ ?_
    rw [mem_sphere_zero_iff_norm, abs_of_pos hr] at hw
    rw [eval_mul, eval_C, norm_mul, Complex.norm_real, norm_of_nonneg hc.le]
    exact log_nonpos (by positivity) ((mul_le_mul_of_nonneg_left (hM w hw) hc.le).trans hcM)
  rcases le_or_gt M 0 with hM0 | hM0
  · have := key (exp (1 - A)) (exp_pos _) (by nlinarith [exp_pos (1 - A)])
    rw [log_exp] at this
    linarith
  · have := key M⁻¹ (inv_pos.2 hM0) (inv_mul_cancel₀ hM0.ne').le
    rw [log_inv] at this
    rw [← exp_log hM0]
    exact exp_le_exp.2 (by linarith)

/-- For `r > 0` and `t ≥ 0`, there is a point `s` of the circle of radius `r` about `0` such that
`‖p.eval z‖ ≤ (t + 1) ^ p.natDegree * ‖p.eval s‖` for every `z` with `‖z‖ ≤ t * r`. -/
theorem exists_norm_eval_le_add_one_pow_mul (p : ℂ[X]) {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) :
    ∃ s : ℂ, ‖s‖ = r ∧
      ∀ z : ℂ, ‖z‖ ≤ t * r → ‖p.eval z‖ ≤ (t + 1) ^ p.natDegree * ‖p.eval s‖ := by
  obtain ⟨s, hs, hmax⟩ := (isCompact_sphere (0 : ℂ) r).exists_isMaxOn
    (NormedSpace.sphere_nonempty.2 hr.le) (p.continuous.norm.continuousOn)
  rw [mem_sphere_zero_iff_norm] at hs
  refine ⟨s, hs, fun z hz ↦ ?_⟩
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  have hle := exp_circleAverage_log_norm_eval_le hp hr fun w hw ↦
    hmax (mem_sphere_zero_iff_norm.2 hw)
  have hcard := IsAlgClosed.card_roots_eq_natDegree (p := p)
  have hexp : exp (circleAverage (fun z ↦ log ‖p.eval z‖) 0 r) =
      ‖p.leadingCoeff‖ * (p.roots.map fun a ↦ max r ‖a‖).prod := by
    rw [circleAverage_log_norm_eval p hr, exp_add, exp_log (by simpa using hp),
      exp_multiset_sum, Multiset.map_map]
    exact congrArg _ (congrArg _
      (Multiset.map_congr rfl fun a _ ↦ exp_log (lt_max_of_lt_left hr)))
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (hexp ▸ hle) (by positivity))
  conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C hcard]
  rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map, norm_mul, Multiset.norm_prod,
    Multiset.map_map, mul_left_comm, ← hcard, ← Multiset.prod_replicate,
    ← Multiset.map_const' p.roots (t + 1), ← Multiset.prod_map_mul]
  gcongr
  refine Multiset.prod_map_le_prod_map₀ _ _ (fun _ _ ↦ norm_nonneg _) fun a _ ↦ ?_
  simp only [Function.comp_apply, eval_sub, eval_X, eval_C]
  calc ‖z - a‖ ≤ t * r + ‖a‖ := (norm_sub_le _ _).trans (by gcongr)
    _ ≤ (t + 1) * max r ‖a‖ := by
      nlinarith [le_max_left r ‖a‖, le_max_right r ‖a‖, norm_nonneg a]

open MeasureTheory Set in
open scoped ENNReal in
/-- **Sub-mean value inequality on a circle, lower-average form.** If `p.eval 0 ≠ 0` and
`‖p‖ ≤ M` on the circle of radius `r` about `0`, then the lower average of
`ofReal (log M - log ‖p‖)` over that circle is at most `ofReal (log M - log ‖p.eval 0‖)`. -/
theorem setLAverage_ofReal_log_sub_log_norm_eval_circleMap_le {p : ℂ[X]}
    (hp : p.eval 0 ≠ 0) {r M : ℝ} (hM : ∀ θ, ‖p.eval (circleMap 0 r θ)‖ ≤ M) :
    ⨍⁻ θ in Ioc 0 (2 * π), ENNReal.ofReal (Real.log M - Real.log ‖p.eval (circleMap 0 r θ)‖) ≤
      ENNReal.ofReal (Real.log M - Real.log ‖p.eval 0‖) := by
  have hIoc : volume (Ioc 0 (2 * π)) ≠ ∞ := measure_Ioc_lt_top.ne
  rcases eq_or_ne r 0 with rfl | hr
  · simp only [circleMap_zero_radius, Function.const_apply]
    exact (setLAverage_const (by simp [Real.pi_pos]) hIoc _).le
  have hp0 : p ≠ 0 := fun h => hp (by simp [h])
  have han : AnalyticOnNhd ℂ (fun z => p.eval z) univ := fun z _ =>
    p.differentiable.analyticAt z
  have hint : IntegrableOn (fun θ => Real.log ‖p.eval (circleMap 0 r θ)‖) (Ioc 0 (2 * π)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).1
      ((han.mono (subset_univ _)).meromorphicOn.circleIntegrable_log_norm)
  have hnull : ∀ᵐ θ ∂(volume.restrict (Ioc 0 (2 * π))), p.eval (circleMap 0 r θ) ≠ 0 := by
    refine ae_restrict_of_ae (measure_mono_null (fun θ hθ => ?_)
      ((p.roots.toFinset.countable_toSet.preimage_circleMap 0 hr).measure_zero _))
    simpa [mem_roots hp0] using hθ
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc 0 (2 * π))]
      fun θ => Real.log M - Real.log ‖p.eval (circleMap 0 r θ)‖ := by
    filter_upwards [hnull] with θ hθ
    exact sub_nonneg.2 (Real.log_le_log (norm_pos_iff.2 hθ) (hM θ))
  have havg : ⨍ θ in Ioc 0 (2 * π), Real.log ‖p.eval (circleMap 0 r θ)‖ =
      circleAverage (fun z => Real.log ‖p.eval z‖) 0 r := by
    rw [circleAverage_eq_intervalAverage, interval_average_eq_div, setAverage_eq,
      intervalIntegral.integral_of_le Real.two_pi_pos.le, Real.volume_real_Ioc_of_le
      Real.two_pi_pos.le, sub_zero, smul_eq_mul, inv_mul_eq_div]
  have hsub : ⨍ θ in Ioc 0 (2 * π), (Real.log M - Real.log ‖p.eval (circleMap 0 r θ)‖) =
      Real.log M - circleAverage (fun z => Real.log ‖p.eval z‖) 0 r := by
    rw [setAverage_fun_sub (integrableOn_const hIoc) hint,
      setAverage_const (by simp [Real.pi_pos]) hIoc, havg]
  have hint' : IntegrableOn (fun θ => Real.log M - Real.log ‖p.eval (circleMap 0 r θ)‖)
      (Ioc 0 (2 * π)) := (integrableOn_const hIoc).sub hint
  rw [setLAverage_eq, ← ofReal_setAverage hint' hnn, hsub]
  gcongr
  exact (han.mono (subset_univ _)).log_norm_le_circleAverage_log_norm hp


end Polynomial

end
