/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import TauCeti.Analysis.SpecialFunctions.SmoothTransition

/-!
# A smoothed maximum of two real numbers

For `δ > 0`, `SymplecticGeometry.smoothedSign δ` is a smooth odd nondecreasing step from `-1` to
`1` across `[-δ, δ]`, built from `Real.smoothTransition`. Its primitive
`SymplecticGeometry.smoothedAbs δ`, normalized to be `t` for `t ≥ δ`, is a smooth even convex
function with slope in `[-1, 1]` that is equal to `|t|` wherever `δ ≤ |t|`.

From it, `SymplecticGeometry.smoothedMax δ a b = (a + b + smoothedAbs δ (a - b)) / 2` is a smooth
function of `(a, b)` that is equal to `max a b` wherever `δ ≤ |a - b|`, and lies between
`max a b` and `max a b + δ / 2`. The convexity of `smoothedAbs δ` and the bound on its slope are
what `Geometry/Manifold/Complex/JConvex/Smoothing.lean` uses to show that the smoothed maximum of
two strictly plurisubharmonic functions is strictly plurisubharmonic.

## Main declarations

* `SymplecticGeometry.smoothedSign`: the smooth step, with `smoothedSign_of_le`,
  `smoothedSign_of_le_neg`, `smoothedSign_neg`, `abs_smoothedSign_le_one` and
  `monotone_smoothedSign`.
* `SymplecticGeometry.smoothedAbs`: the smoothing of `|t|` on `(-δ, δ)`.
* `SymplecticGeometry.contDiff_smoothedAbs`, `SymplecticGeometry.deriv_smoothedAbs`,
  `SymplecticGeometry.abs_deriv_smoothedAbs_le_one`,
  `SymplecticGeometry.iteratedDeriv_two_smoothedAbs_nonneg`: smoothness, derivative, and the
  bounds on its first two derivatives.
* `SymplecticGeometry.smoothedAbs_eq_abs`, `SymplecticGeometry.abs_le_smoothedAbs`,
  `SymplecticGeometry.smoothedAbs_le_abs_add`: comparison with `|t|`.
* `SymplecticGeometry.smoothedMax`: the smoothed maximum, with `contDiff_smoothedMax`,
  `smoothedMax_eq_max`, `smoothedMax_eq_left`, `smoothedMax_eq_right`, `le_smoothedMax` and
  `smoothedMax_le`.

## References

* [K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Chapter 3, smoothing of maxima.
-/

public section

noncomputable section

open Set intervalIntegral

namespace SymplecticGeometry

/-! ### The smoothed sign -/

/-- A smooth odd nondecreasing step from `-1` to `1` across `[-δ, δ]`:
`s ↦ 2 ψ((s + δ) / (2 δ)) - 1`, with `ψ = Real.smoothTransition`. For `δ > 0` it is `-1` on
`(-∞, -δ]` and `1` on `[δ, ∞)`. -/
def smoothedSign (δ s : ℝ) : ℝ :=
  2 * Real.smoothTransition ((s + δ) / (2 * δ)) - 1

theorem smoothedSign_def (δ s : ℝ) :
    smoothedSign δ s = 2 * Real.smoothTransition ((s + δ) / (2 * δ)) - 1 :=
  (rfl)

variable {δ : ℝ}

theorem contDiff_smoothedSign {n : ℕ∞} (δ : ℝ) : ContDiff ℝ n (smoothedSign δ) :=
  (contDiff_const.mul (Real.smoothTransition.contDiff.comp
    ((contDiff_id.add contDiff_const).div_const _))).sub contDiff_const

theorem continuous_smoothedSign (δ : ℝ) : Continuous (smoothedSign δ) :=
  (contDiff_smoothedSign (n := 0) δ).continuous

/-- For `δ > 0`, `smoothedSign δ s = 1` for `s ≥ δ`. -/
theorem smoothedSign_of_le (hδ : 0 < δ) {s : ℝ} (hs : δ ≤ s) : smoothedSign δ s = 1 := by
  rw [smoothedSign_def,
    Real.smoothTransition.one_of_one_le ((one_le_div (by positivity)).2 (by linarith))]
  norm_num

/-- For `δ > 0`, `smoothedSign δ` is odd. -/
@[simp]
theorem smoothedSign_neg (hδ : 0 < δ) (s : ℝ) : smoothedSign δ (-s) = -smoothedSign δ s := by
  have : (-s + δ) / (2 * δ) = 1 - (s + δ) / (2 * δ) := by field_simp; ring
  rw [smoothedSign_def, smoothedSign_def, this, Real.smoothTransition.one_sub]
  ring

/-- For `δ > 0`, `smoothedSign δ s = -1` for `s ≤ -δ`. -/
theorem smoothedSign_of_le_neg (hδ : 0 < δ) {s : ℝ} (hs : s ≤ -δ) : smoothedSign δ s = -1 := by
  rw [← neg_neg s, smoothedSign_neg hδ, smoothedSign_of_le hδ (le_neg_of_le_neg hs)]

/-- `smoothedSign δ` takes its values in `[-1, 1]`. -/
theorem abs_smoothedSign_le_one (δ s : ℝ) : |smoothedSign δ s| ≤ 1 := by
  have h₀ := Real.smoothTransition.nonneg ((s + δ) / (2 * δ))
  have h₁ := Real.smoothTransition.le_one ((s + δ) / (2 * δ))
  rw [smoothedSign_def, abs_le]
  constructor <;> linarith

/-- For `δ ≥ 0`, `smoothedSign δ` is nondecreasing. -/
theorem monotone_smoothedSign (hδ : 0 ≤ δ) : Monotone (smoothedSign δ) := by
  intro s t hst
  have := Real.smoothTransition.monotone
    (div_le_div_of_nonneg_right (by linarith : s + δ ≤ t + δ) (by positivity : (0 : ℝ) ≤ 2 * δ))
  rw [smoothedSign_def, smoothedSign_def]
  linarith

/-- For `δ > 0`, `smoothedSign δ` is nonnegative on `[0, ∞)`. -/
theorem smoothedSign_nonneg (hδ : 0 < δ) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ smoothedSign δ s := by
  have := monotone_smoothedSign hδ.le (neg_le_self hs)
  rw [smoothedSign_neg hδ] at this
  linarith

/-! ### The smoothed absolute value -/

/-- A smoothing of the absolute value on `(-δ, δ)`: the primitive of `smoothedSign δ`, shifted so
that it is equal to `|t|` wherever `δ ≤ |t|` (`smoothedAbs_eq_abs`, for `0 < δ`). -/
def smoothedAbs (δ t : ℝ) : ℝ :=
  (∫ s in (0 : ℝ)..t, smoothedSign δ s) + (δ - ∫ s in (0 : ℝ)..δ, smoothedSign δ s)

theorem smoothedAbs_def (δ t : ℝ) :
    smoothedAbs δ t =
      (∫ s in (0 : ℝ)..t, smoothedSign δ s) + (δ - ∫ s in (0 : ℝ)..δ, smoothedSign δ s) :=
  (rfl)

/-- The derivative of `smoothedAbs δ` at `t` is `smoothedSign δ t`. -/
theorem hasDerivAt_smoothedAbs (δ t : ℝ) : HasDerivAt (smoothedAbs δ) (smoothedSign δ t) t := by
  have h := ((continuous_smoothedSign δ).integral_hasStrictDerivAt 0 t).hasDerivAt
  exact (h.add_const _).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s ↦ smoothedAbs_def δ s)

/-- The derivative of `smoothedAbs δ` is `smoothedSign δ`. -/
@[simp]
theorem deriv_smoothedAbs (δ : ℝ) : deriv (smoothedAbs δ) = smoothedSign δ :=
  funext fun t ↦ (hasDerivAt_smoothedAbs δ t).deriv

theorem differentiable_smoothedAbs (δ : ℝ) : Differentiable ℝ (smoothedAbs δ) :=
  fun t ↦ (hasDerivAt_smoothedAbs δ t).differentiableAt

/-- `smoothedAbs δ` is smooth. -/
theorem contDiff_smoothedAbs {n : ℕ∞} (δ : ℝ) : ContDiff ℝ n (smoothedAbs δ) := by
  have : ContDiff ℝ (⊤ : ℕ∞) (smoothedAbs δ) :=
    contDiff_infty_iff_deriv.2 ⟨differentiable_smoothedAbs δ, by
      rw [deriv_smoothedAbs]; exact contDiff_smoothedSign δ⟩
  exact this.of_le (by exact_mod_cast le_top)

/-- The derivative of `smoothedAbs δ` lies in `[-1, 1]`. -/
theorem abs_deriv_smoothedAbs_le_one (δ t : ℝ) : |deriv (smoothedAbs δ) t| ≤ 1 := by
  rw [deriv_smoothedAbs]
  exact abs_smoothedSign_le_one δ t

/-- For `δ ≥ 0`, `smoothedAbs δ` is convex: its second derivative is nonnegative. -/
theorem iteratedDeriv_two_smoothedAbs_nonneg (hδ : 0 ≤ δ) (t : ℝ) :
    0 ≤ iteratedDeriv 2 (smoothedAbs δ) t := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_smoothedAbs]
  exact (monotone_smoothedSign hδ).deriv_nonneg

/-- `smoothedAbs δ t = t` for `t ≥ δ > 0`. -/
theorem smoothedAbs_of_le (hδ : 0 < δ) {t : ℝ} (ht : δ ≤ t) : smoothedAbs δ t = t := by
  have hc := continuous_smoothedSign δ
  have h₁ : (∫ s in δ..t, smoothedSign δ s) = t - δ := by
    rw [integral_congr (g := fun _ ↦ (1 : ℝ)) fun s hs ↦ ?_]
    · simp
    · rw [uIcc_of_le ht] at hs
      exact smoothedSign_of_le hδ hs.1
  rw [smoothedAbs_def, ← integral_add_adjacent_intervals (b := δ) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _), h₁]
  ring

/-- For `δ > 0`, `smoothedAbs δ` is even. -/
@[simp]
theorem smoothedAbs_neg (hδ : 0 < δ) (t : ℝ) : smoothedAbs δ (-t) = smoothedAbs δ t := by
  have hd : Differentiable ℝ fun s ↦ smoothedAbs δ (-s) - smoothedAbs δ s :=
    ((differentiable_smoothedAbs δ).comp differentiable_neg).sub (differentiable_smoothedAbs δ)
  have h := is_const_of_deriv_eq_zero hd (fun s ↦ by
    have : HasDerivAt (fun s ↦ smoothedAbs δ (-s) - smoothedAbs δ s) _ s :=
      ((hasDerivAt_smoothedAbs δ (-s)).comp s (hasDerivAt_neg s)).sub
        (hasDerivAt_smoothedAbs δ s)
    rw [this.deriv, smoothedSign_neg hδ]
    ring) t 0
  simp only [neg_zero, sub_self] at h
  linarith

/-- For `δ > 0`, `smoothedAbs δ t = |t|` wherever `δ ≤ |t|`. -/
theorem smoothedAbs_eq_abs (hδ : 0 < δ) {t : ℝ} (ht : δ ≤ |t|) : smoothedAbs δ t = |t| := by
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg h] at ht ⊢
    exact smoothedAbs_of_le hδ ht
  · rw [abs_of_nonpos h] at ht ⊢
    rw [← smoothedAbs_neg hδ, smoothedAbs_of_le hδ ht]

/-- `t ↦ smoothedAbs δ t - t` is nonincreasing, since the slope of `smoothedAbs δ` is at most
`1`. -/
theorem antitone_smoothedAbs_sub_id (δ : ℝ) : Antitone fun t ↦ smoothedAbs δ t - t :=
  antitone_of_deriv_nonpos ((differentiable_smoothedAbs δ).sub differentiable_id) fun t ↦ by
    have : HasDerivAt (fun t ↦ smoothedAbs δ t - t) _ t :=
      (hasDerivAt_smoothedAbs δ t).sub (hasDerivAt_id t)
    rw [this.deriv]
    linarith [(abs_le.1 (abs_smoothedSign_le_one δ t)).2]

/-- For `δ > 0`, `smoothedAbs δ` lies above the absolute value. -/
theorem abs_le_smoothedAbs (hδ : 0 < δ) (t : ℝ) : |t| ≤ smoothedAbs δ t := by
  have key (t : ℝ) : t ≤ smoothedAbs δ t := by
    rcases le_total δ t with h | h
    · exact (smoothedAbs_of_le hδ h).ge
    · have := antitone_smoothedAbs_sub_id δ h
      simp only [smoothedAbs_of_le hδ le_rfl, sub_self] at this
      linarith
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg h]; exact key t
  · rw [abs_of_nonpos h, ← smoothedAbs_neg hδ]; exact key (-t)

/-- For `δ > 0`, `smoothedAbs δ` lies below `|t| + δ`. -/
theorem smoothedAbs_le_abs_add (hδ : 0 < δ) (t : ℝ) : smoothedAbs δ t ≤ |t| + δ := by
  have h0 : smoothedAbs δ 0 ≤ δ := by
    rw [smoothedAbs_def, integral_same, zero_add, sub_le_self_iff]
    exact integral_nonneg hδ.le fun s hs ↦ smoothedSign_nonneg hδ hs.1
  have key {t : ℝ} (ht : 0 ≤ t) : smoothedAbs δ t ≤ t + δ := by
    have := antitone_smoothedAbs_sub_id δ ht
    simp only [sub_zero] at this
    linarith
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg h]; exact key h
  · rw [abs_of_nonpos h, ← smoothedAbs_neg hδ]; exact key (neg_nonneg.2 h)

/-! ### The smoothed maximum -/

/-- The **smoothed maximum** `(a + b + smoothedAbs δ (a - b)) / 2` of two real numbers. For
`δ > 0` it is `max a b` wherever `δ ≤ |a - b|` (`smoothedMax_eq_max`), and a smooth function of
`(a, b)` (`contDiff_smoothedMax`). -/
def smoothedMax (δ a b : ℝ) : ℝ :=
  (a + b + smoothedAbs δ (a - b)) / 2

theorem smoothedMax_def (δ a b : ℝ) : smoothedMax δ a b = (a + b + smoothedAbs δ (a - b)) / 2 :=
  (rfl)

/-- The smoothed maximum is a smooth function of its two arguments. -/
theorem contDiff_smoothedMax {n : ℕ∞} (δ : ℝ) :
    ContDiff ℝ n fun p : ℝ × ℝ ↦ smoothedMax δ p.1 p.2 := by
  simp only [smoothedMax_def]
  exact ((contDiff_fst.add contDiff_snd).add
    ((contDiff_smoothedAbs δ).comp (contDiff_fst.sub contDiff_snd))).div_const _

theorem smoothedMax_comm (hδ : 0 < δ) (a b : ℝ) : smoothedMax δ a b = smoothedMax δ b a := by
  rw [smoothedMax_def, smoothedMax_def, ← neg_sub, smoothedAbs_neg hδ, add_comm a]

/-- For `δ > 0`, the smoothed maximum is the maximum wherever `δ ≤ |a - b|`. -/
theorem smoothedMax_eq_max (hδ : 0 < δ) {a b : ℝ} (h : δ ≤ |a - b|) :
    smoothedMax δ a b = max a b := by
  rw [smoothedMax_def, smoothedAbs_eq_abs hδ h]
  rcases le_total a b with hab | hab
  · rw [max_eq_right hab, abs_of_nonpos (sub_nonpos.2 hab)]; ring
  · rw [max_eq_left hab, abs_of_nonneg (sub_nonneg.2 hab)]; ring

/-- For `δ > 0`, the smoothed maximum of `a` and `b` is `a` when `b + δ ≤ a`. -/
theorem smoothedMax_eq_left (hδ : 0 < δ) {a b : ℝ} (h : b + δ ≤ a) : smoothedMax δ a b = a := by
  rw [smoothedMax_eq_max hδ (by rw [abs_of_nonneg (by linarith)]; linarith),
    max_eq_left (by linarith)]

/-- For `δ > 0`, the smoothed maximum of `a` and `b` is `b` when `a + δ ≤ b`. -/
theorem smoothedMax_eq_right (hδ : 0 < δ) {a b : ℝ} (h : a + δ ≤ b) : smoothedMax δ a b = b := by
  rw [smoothedMax_comm hδ, smoothedMax_eq_left hδ h]

/-- For `δ > 0`, the smoothed maximum lies above the maximum. -/
theorem le_smoothedMax (hδ : 0 < δ) (a b : ℝ) : max a b ≤ smoothedMax δ a b := by
  have := abs_le_smoothedAbs hδ (a - b)
  rw [smoothedMax_def]
  rcases le_total a b with hab | hab
  · rw [max_eq_right hab, abs_of_nonpos (sub_nonpos.2 hab)] at *; linarith
  · rw [max_eq_left hab, abs_of_nonneg (sub_nonneg.2 hab)] at *; linarith

/-- For `δ > 0`, the smoothed maximum lies below `max a b + δ / 2`. -/
theorem smoothedMax_le (hδ : 0 < δ) (a b : ℝ) : smoothedMax δ a b ≤ max a b + δ / 2 := by
  have := smoothedAbs_le_abs_add hδ (a - b)
  rw [smoothedMax_def]
  rcases le_total a b with hab | hab
  · rw [max_eq_right hab, abs_of_nonpos (sub_nonpos.2 hab)] at *; linarith
  · rw [max_eq_left hab, abs_of_nonneg (sub_nonneg.2 hab)] at *; linarith

end SymplecticGeometry
