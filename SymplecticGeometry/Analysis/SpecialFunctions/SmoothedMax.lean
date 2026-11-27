/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import SymplecticGeometry.Analysis.Calculus.IteratedDeriv.Defs
import SymplecticGeometry.Analysis.SpecialFunctions.SmoothTransition.Deriv

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
  `smoothedSign_of_le_neg`, `smoothedSign_neg`, `abs_smoothedSign_le_one`,
  `monotone_smoothedSign`, and its derivative `hasDerivAt_smoothedSign`,
  `deriv_smoothedSign`.
* `SymplecticGeometry.smoothedAbs`: the smoothing of `|t|` on `(-δ, δ)`.
* `SymplecticGeometry.contDiff_smoothedAbs`, `SymplecticGeometry.deriv_smoothedAbs`,
  `SymplecticGeometry.abs_deriv_smoothedAbs_le_one`,
  `SymplecticGeometry.iteratedDeriv_two_smoothedAbs`,
  `SymplecticGeometry.iteratedDeriv_two_smoothedAbs_nonneg`: smoothness, the first two
  derivatives, and bounds on them.
* `SymplecticGeometry.exists_pos_div_le_iteratedDeriv_two_smoothedAbs`: for each `ε > 0` there is
  `c > 0` such that `c / δ ≤ (smoothedAbs δ)''(t)` wherever `|smoothedSign δ t| ≤ 1 - ε`. It
  follows from the positive lower bound, by compactness, on the derivative of
  `Real.smoothTransition` where its values stay away from `0` and `1`
  (`Real.smoothTransition.exists_pos_le_deriv`).
  `SymplecticGeometry.one_sub_smoothedSign_sq_div_two_mul_lt` turns it into the bound on the error
  of a smoothing that the smoothed maximum and minimum of two `i`-convex shapes use, and
  `SymplecticGeometry.exists_pos_forall_one_sub_smoothedSign_sq_div_two_mul_lt` gives a `δ₀ > 0`
  below which that bound holds for given margins and bounds.
* `SymplecticGeometry.two_mul_one_sub_smoothedSign_sq_div_le_iteratedDeriv_two_smoothedAbs` and
  `SymplecticGeometry.exists_forall_iteratedDeriv_two_smoothedAbs_le`: the curvature of
  `smoothedAbs δ` lies between `2 (1 - s²) / δ`, with `s = smoothedSign δ t`, and `C / δ` for a
  constant `C`. The lower bound follows from `8 ψ (1 - ψ) ≤ ψ'` for `ψ = Real.smoothTransition`
  (`Real.smoothTransition.eight_mul_mul_one_sub_le_deriv`).
* `SymplecticGeometry.convexOn_smoothedAbs`: convexity.
* `SymplecticGeometry.smoothedAbs_eq_abs`, `SymplecticGeometry.abs_le_smoothedAbs`,
  `SymplecticGeometry.smoothedAbs_le_abs_add`: comparison with `|t|`.
* `SymplecticGeometry.smoothedMax`: the smoothed maximum, with `contDiff_smoothedMax`,
  `hasDerivAt_smoothedMax_left`, `hasDerivAt_smoothedMax_right`, monotonicity in each argument
  (`monotone_smoothedMax_left`, `monotone_smoothedMax_right`, `smoothedMax_le_smoothedMax`), the
  first and second derivatives `hasDerivAt_smoothedMax`, `deriv_smoothedMax` and
  `iteratedDeriv_two_smoothedMax` of the smoothed maximum of two functions, the first one also
  as a weighted average (`hasDerivAt_smoothedMax_weighted`, `deriv_smoothedMax_weighted`, with
  the weight in `[0, 1]` by `one_add_smoothedSign_div_two_mem_Icc`), the bounds
  `min_deriv_le_deriv_smoothedMax` and `deriv_smoothedMax_le_max`, `smoothedMax_eq_max`,
  `smoothedMax_eq_left`, `smoothedMax_eq_right`, `max_le_smoothedMax`, `smoothedMax_le_max_add`
  and `one_div_smoothedMax_le`.

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

/-- The derivative of `smoothedSign δ` at `s` is `ψ'((s + δ) / (2 δ)) / δ`, with
`ψ = Real.smoothTransition`. For `δ = 0` both sides vanish. -/
theorem hasDerivAt_smoothedSign (δ s : ℝ) :
    HasDerivAt (smoothedSign δ) (deriv Real.smoothTransition ((s + δ) / (2 * δ)) / δ) s := by
  have h := ((((hasDerivAt_id s).add_const δ).div_const (2 * δ)).smoothTransition.const_mul
    2).sub_const 1
  convert h using 1
  · exact funext fun x ↦ smoothedSign_def δ x
  · simp only [id_eq]
    field_simp

/-- The derivative of `smoothedSign δ` is `s ↦ ψ'((s + δ) / (2 δ)) / δ`, with
`ψ = Real.smoothTransition`. -/
@[simp]
theorem deriv_smoothedSign (δ : ℝ) :
    deriv (smoothedSign δ) = fun s ↦ deriv Real.smoothTransition ((s + δ) / (2 * δ)) / δ :=
  funext fun s ↦ (hasDerivAt_smoothedSign δ s).deriv

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

/-- For `δ ≥ 0`, `smoothedAbs δ` is convex on `ℝ`. -/
theorem convexOn_smoothedAbs (hδ : 0 ≤ δ) : ConvexOn ℝ univ (smoothedAbs δ) :=
  Monotone.convexOn_univ_of_deriv (differentiable_smoothedAbs δ)
    (by rw [deriv_smoothedAbs]; exact monotone_smoothedSign hδ)

/-- For `δ ≥ 0`, the second derivative of `smoothedAbs δ` is nonnegative. -/
theorem iteratedDeriv_two_smoothedAbs_nonneg (hδ : 0 ≤ δ) (t : ℝ) :
    0 ≤ iteratedDeriv 2 (smoothedAbs δ) t := by
  rw [iteratedDeriv_two, deriv_smoothedAbs]
  exact (monotone_smoothedSign hδ).deriv_nonneg

/-- The second derivative of `smoothedAbs δ` at `t` is `ψ'((t + δ) / (2 δ)) / δ`, with
`ψ = Real.smoothTransition`. -/
theorem iteratedDeriv_two_smoothedAbs (δ t : ℝ) :
    iteratedDeriv 2 (smoothedAbs δ) t =
      deriv Real.smoothTransition ((t + δ) / (2 * δ)) / δ := by
  rw [iteratedDeriv_two, deriv_smoothedAbs, deriv_smoothedSign]

/-- Away from the ends `±1` of its slope, `smoothedAbs δ` curves at a rate of order `1 / δ`: for
each `ε > 0` there is `c > 0` such that `c / δ ≤ (smoothedAbs δ)''(t)` for all `δ > 0` and all
`t` with `|smoothedSign δ t| ≤ 1 - ε`. -/
theorem exists_pos_div_le_iteratedDeriv_two_smoothedAbs {ε : ℝ} (hε : 0 < ε) :
    ∃ c > 0, ∀ δ > 0, ∀ t, |smoothedSign δ t| ≤ 1 - ε →
      c / δ ≤ iteratedDeriv 2 (smoothedAbs δ) t := by
  obtain ⟨c, hc, hcK⟩ := Real.smoothTransition.exists_pos_le_deriv (half_pos hε)
  refine ⟨c, hc, fun δ hδ t ht ↦ ?_⟩
  rw [iteratedDeriv_two_smoothedAbs]
  have hu : Real.smoothTransition ((t + δ) / (2 * δ)) ∈ Icc (ε / 2) (1 - ε / 2) := by
    rw [smoothedSign_def, abs_le] at ht
    constructor <;> linarith
  gcongr
  exact hcK _ hu

/-- The curvature of `smoothedAbs δ` is at least `2 (1 - s²) / δ`, where `s = smoothedSign δ t` is
its slope: a lower bound of order `1 / δ` that degrades only as fast as `1 - s²` where the slope
nears `±1`. -/
theorem two_mul_one_sub_smoothedSign_sq_div_le_iteratedDeriv_two_smoothedAbs (hδ : 0 < δ)
    (t : ℝ) : 2 * (1 - smoothedSign δ t ^ 2) / δ ≤ iteratedDeriv 2 (smoothedAbs δ) t := by
  rw [iteratedDeriv_two_smoothedAbs, smoothedSign_def]
  gcongr
  linarith [Real.smoothTransition.eight_mul_mul_one_sub_le_deriv ((t + δ) / (2 * δ))]

/-- The curvature of `smoothedAbs δ` is at most of order `1 / δ`: there is `C` with
`(smoothedAbs δ)''(t) ≤ C / δ` for all `δ > 0` and all `t`. -/
theorem exists_forall_iteratedDeriv_two_smoothedAbs_le :
    ∃ C, ∀ δ > 0, ∀ t, iteratedDeriv 2 (smoothedAbs δ) t ≤ C / δ := by
  obtain ⟨L, hL⟩ := Real.smoothTransition.exists_forall_norm_deriv_le
  refine ⟨L, fun δ hδ t ↦ ?_⟩
  rw [iteratedDeriv_two_smoothedAbs]
  gcongr
  exact (le_abs_self _).trans (hL _)

/-- **The error of a smoothing by `smoothedAbs δ`.** Let `s = smoothedSign δ t` and
`p = (smoothedAbs δ)'' t`. If `0 ≤ g`, `0 ≤ T ≤ Q`, `g T ≤ G` and `ε G < a`, and if `c / δ ≤ p`
wherever `|s| ≤ 1 - ε`, with `δ Q ≤ c`, then `(1 - s²) / 2 · g T < a + p g / 2`: where `|s|` is
near `1` the weight `(1 - s²) / 2` is below `ε`, and elsewhere the curvature `p ≥ Q` makes up for
the error. -/
theorem one_sub_smoothedSign_sq_div_two_mul_lt {δ ε a c g T Q G t : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hg : 0 ≤ g) (hT : 0 ≤ T) (hTQ : T ≤ Q) (hG : g * T ≤ G) (hεG : ε * G < a)
    (hc : |smoothedSign δ t| ≤ 1 - ε → c / δ ≤ iteratedDeriv 2 (smoothedAbs δ) t)
    (hδQ : δ * Q ≤ c) :
    (1 - smoothedSign δ t ^ 2) / 2 * (g * T) < a + iteratedDeriv 2 (smoothedAbs δ) t * g / 2 := by
  have hp := iteratedDeriv_two_smoothedAbs_nonneg hδ.le t
  set s := smoothedSign δ t
  set p := iteratedDeriv 2 (smoothedAbs δ) t
  have hgT : 0 ≤ g * T := mul_nonneg hg hT
  by_cases hsε : |s| ≤ 1 - ε
  · have ha : 0 < a := lt_of_le_of_lt (mul_nonneg hε.le (hgT.trans hG)) hεG
    have hpQ : Q ≤ p := le_trans ((le_div_iff₀ hδ).2 (by linarith)) (hc hsε)
    calc (1 - s ^ 2) / 2 * (g * T) ≤ 1 / 2 * (g * p) := by
          gcongr
          · linarith [sq_nonneg s]
          · exact hTQ.trans hpQ
      _ < a + p * g / 2 := by linarith
  · have hs₃ : (1 - s ^ 2) / 2 < ε := by
      rw [not_le] at hsε
      rcases le_or_gt 0 (1 - ε) with h | h
      · have : (1 - ε) ^ 2 < s ^ 2 := by
          rw [← sq_abs s]
          exact pow_lt_pow_left₀ hsε h two_ne_zero
        linarith [sq_nonneg ε]
      · linarith [sq_nonneg s]
    calc (1 - s ^ 2) / 2 * (g * T) ≤ ε * (g * T) := by gcongr
      _ ≤ ε * G := by gcongr
      _ < a := hεG
      _ ≤ a + p * g / 2 := by linarith [mul_nonneg hp hg]

/-- **A uniform choice of the smoothing parameter.** For `a > 0` and bounds `G` and `Q` there is
`δ₀ > 0` such that for every `δ ∈ (0, δ₀]`, all `g ≥ 0` and `T ∈ [0, Q]` with `g T ≤ G`, and
all `t`, `(1 - s²) / 2 · g T < a + p g / 2`, where `s = smoothedSign δ t` and
`p = (smoothedAbs δ)'' t`. -/
theorem exists_pos_forall_one_sub_smoothedSign_sq_div_two_mul_lt {a : ℝ} (ha : 0 < a) (G Q : ℝ) :
    ∃ δ₀ > 0, ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ {g T : ℝ}, 0 ≤ g → 0 ≤ T → T ≤ Q → g * T ≤ G → ∀ t,
      (1 - smoothedSign δ t ^ 2) / 2 * (g * T) <
        a + iteratedDeriv 2 (smoothedAbs δ) t * g / 2 := by
  set ε := a / (2 * (|G| + 1))
  have hε : 0 < ε := by positivity
  have hεG : ε * G < a := by
    calc ε * G ≤ ε * |G| := by gcongr; exact le_abs_self G
      _ < a := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [abs_nonneg G]
  obtain ⟨c, hc, hcδ⟩ := exists_pos_div_le_iteratedDeriv_two_smoothedAbs hε
  refine ⟨c / (|Q| + 1), by positivity, fun δ hδ hδ₀ g T hg hT hTQ hG t ↦
    one_sub_smoothedSign_sq_div_two_mul_lt hδ hε hg hT hTQ hG hεG (hcδ δ hδ t) ?_⟩
  calc δ * Q ≤ δ * |Q| := by gcongr; exact le_abs_self Q
    _ ≤ c / (|Q| + 1) * |Q| := by gcongr
    _ ≤ c := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [abs_nonneg Q]

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

/-- The derivative of the smoothed maximum of two functions: at `x`, it is the convex combination
`(f' + g' + smoothedSign δ (f x - g x) * (f' - g')) / 2` of their derivatives. -/
theorem hasDerivAt_smoothedMax {f g : ℝ → ℝ} {f' g' x : ℝ} (hf : HasDerivAt f f' x)
    (hg : HasDerivAt g g' x) :
    HasDerivAt (fun x ↦ smoothedMax δ (f x) (g x))
      ((f' + g' + smoothedSign δ (f x - g x) * (f' - g')) / 2) x := by
  have h := ((hf.add hg).add ((hasDerivAt_smoothedAbs δ (f x - g x)).comp x
    (hf.sub hg))).div_const 2
  convert h using 1
  funext y
  simp only [smoothedMax_def, Pi.add_apply, Pi.sub_apply, Function.comp_apply]

/-- The derivative of the smoothed maximum in its first argument: at `a`, it is
`(1 + smoothedSign δ (a - b)) / 2`. -/
theorem hasDerivAt_smoothedMax_left (δ b a : ℝ) :
    HasDerivAt (fun a ↦ smoothedMax δ a b) ((1 + smoothedSign δ (a - b)) / 2) a := by
  simpa using hasDerivAt_smoothedMax (δ := δ) (hasDerivAt_id a) (hasDerivAt_const a b)

/-- The derivative of the smoothed maximum in its second argument: at `b`, it is
`(1 - smoothedSign δ (a - b)) / 2`. -/
theorem hasDerivAt_smoothedMax_right (δ a b : ℝ) :
    HasDerivAt (fun b ↦ smoothedMax δ a b) ((1 - smoothedSign δ (a - b)) / 2) b := by
  convert hasDerivAt_smoothedMax (δ := δ) (hasDerivAt_const b a) (hasDerivAt_id' b) using 1
  ring

/-- The smoothed maximum is monotone in its first argument, since its partial derivative
`(1 + smoothedSign δ (a - b)) / 2` is nonnegative. -/
theorem monotone_smoothedMax_left (δ b : ℝ) : Monotone fun a ↦ smoothedMax δ a b :=
  monotone_of_deriv_nonneg (fun a ↦ (hasDerivAt_smoothedMax_left δ b a).differentiableAt)
    fun a ↦ by
      rw [(hasDerivAt_smoothedMax_left δ b a).deriv]
      linarith [(abs_le.1 (abs_smoothedSign_le_one δ (a - b))).1]

/-- The smoothed maximum is monotone in its second argument, since its partial derivative
`(1 - smoothedSign δ (a - b)) / 2` is nonnegative. -/
theorem monotone_smoothedMax_right (δ a : ℝ) : Monotone fun b ↦ smoothedMax δ a b :=
  monotone_of_deriv_nonneg (fun b ↦ (hasDerivAt_smoothedMax_right δ a b).differentiableAt)
    fun b ↦ by
      rw [(hasDerivAt_smoothedMax_right δ a b).deriv]
      linarith [(abs_le.1 (abs_smoothedSign_le_one δ (a - b))).2]

/-- The smoothed maximum is monotone in both arguments together. -/
@[gcongr]
theorem smoothedMax_le_smoothedMax {a a' b b' : ℝ} (ha : a ≤ a') (hb : b ≤ b') :
    smoothedMax δ a b ≤ smoothedMax δ a' b' :=
  (monotone_smoothedMax_left δ b ha).trans (monotone_smoothedMax_right δ a' hb)

/-- The derivative of the smoothed maximum of two functions differentiable at `x`. -/
theorem deriv_smoothedMax {f g : ℝ → ℝ} {x : ℝ} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    deriv (fun x ↦ smoothedMax δ (f x) (g x)) x =
      (deriv f x + deriv g x + smoothedSign δ (f x - g x) * (deriv f x - deriv g x)) / 2 :=
  (hasDerivAt_smoothedMax hf.hasDerivAt hg.hasDerivAt).deriv

/-- The weight `(1 + smoothedSign δ t) / 2` of the derivative of the smoothed maximum lies in
`[0, 1]`. -/
theorem one_add_smoothedSign_div_two_mem_Icc (δ t : ℝ) :
    (1 + smoothedSign δ t) / 2 ∈ Icc (0 : ℝ) 1 := by
  have hs := abs_le.1 (abs_smoothedSign_le_one δ t)
  constructor <;> linarith

/-- The derivative of the smoothed maximum of two functions, as a weighted average: with
`w = (1 + smoothedSign δ (f x - g x)) / 2`, which lies in `[0, 1]`
(`one_add_smoothedSign_div_two_mem_Icc`), it is `w * f' + (1 - w) * g'`. -/
theorem hasDerivAt_smoothedMax_weighted {f g : ℝ → ℝ} {f' g' x : ℝ} (hf : HasDerivAt f f' x)
    (hg : HasDerivAt g g' x) :
    HasDerivAt (fun x ↦ smoothedMax δ (f x) (g x))
      ((1 + smoothedSign δ (f x - g x)) / 2 * f' +
        (1 - (1 + smoothedSign δ (f x - g x)) / 2) * g') x := by
  convert hasDerivAt_smoothedMax hf hg using 1
  ring

/-- The derivative of the smoothed maximum of two functions differentiable at `x`, as a weighted
average: with `w = (1 + smoothedSign δ (f x - g x)) / 2`, which lies in `[0, 1]`
(`one_add_smoothedSign_div_two_mem_Icc`), it is `w * f'(x) + (1 - w) * g'(x)`. -/
theorem deriv_smoothedMax_weighted {f g : ℝ → ℝ} {x : ℝ} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    deriv (fun x ↦ smoothedMax δ (f x) (g x)) x =
      (1 + smoothedSign δ (f x - g x)) / 2 * deriv f x +
        (1 - (1 + smoothedSign δ (f x - g x)) / 2) * deriv g x :=
  (hasDerivAt_smoothedMax_weighted hf.hasDerivAt hg.hasDerivAt).deriv

/-- The derivative of the smoothed maximum of two functions differentiable at `x` is at least
the smaller of their derivatives. -/
theorem min_deriv_le_deriv_smoothedMax {f g : ℝ → ℝ} {x : ℝ} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    min (deriv f x) (deriv g x) ≤ deriv (fun x ↦ smoothedMax δ (f x) (g x)) x := by
  have hw := one_add_smoothedSign_div_two_mem_Icc δ (f x - g x)
  rw [deriv_smoothedMax_weighted hf hg, ← smul_eq_mul, ← smul_eq_mul (1 - _)]
  exact Convex.min_le_combo _ _ hw.1 (sub_nonneg.2 hw.2) (add_sub_cancel _ _)

/-- The derivative of the smoothed maximum of two functions differentiable at `x` is at most
the larger of their derivatives. -/
theorem deriv_smoothedMax_le_max {f g : ℝ → ℝ} {x : ℝ} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    deriv (fun x ↦ smoothedMax δ (f x) (g x)) x ≤ max (deriv f x) (deriv g x) := by
  have hw := one_add_smoothedSign_div_two_mem_Icc δ (f x - g x)
  rw [deriv_smoothedMax_weighted hf hg, ← smul_eq_mul, ← smul_eq_mul (1 - _)]
  exact Convex.combo_le_max _ _ hw.1 (sub_nonneg.2 hw.2) (add_sub_cancel _ _)

/-- The second derivative of the smoothed maximum of two `C²` functions `f` and `g`: with
`s = smoothedSign δ (f x - g x)`, it is
`(f'' + g'' + s (f'' - g'') + (smoothedAbs δ)'' (f x - g x) (f' - g')²) / 2`. -/
theorem iteratedDeriv_two_smoothedMax {f g : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (x : ℝ) :
    iteratedDeriv 2 (fun x ↦ smoothedMax δ (f x) (g x)) x =
      (iteratedDeriv 2 f x + iteratedDeriv 2 g x +
        smoothedSign δ (f x - g x) * (iteratedDeriv 2 f x - iteratedDeriv 2 g x) +
        iteratedDeriv 2 (smoothedAbs δ) (f x - g x) * (deriv f x - deriv g x) ^ 2) / 2 := by
  have h : (fun x ↦ smoothedMax δ (f x) (g x)) =
      fun x ↦ (f x + g x + (smoothedAbs δ ∘ (f - g)) x) / 2 := by
    funext y
    simp only [smoothedMax_def, Function.comp_apply, Pi.sub_apply]
  have hh := (contDiff_smoothedAbs (n := 2) δ).contDiffAt (x := (f - g) x)
  have hfg := (hf.sub hg).contDiffAt (x := x)
  have hf₂ := hf.contDiffAt (x := x)
  have hg₂ := hg.contDiffAt (x := x)
  rw [h, iteratedDeriv_div_const, iteratedDeriv_fun_add (hf₂.add hg₂) ((hh.comp x hfg)),
    iteratedDeriv_fun_add hf₂ hg₂, iteratedDeriv_comp_two hh hfg, iteratedDeriv_sub hf₂ hg₂,
    deriv_smoothedAbs, deriv_sub (hf.differentiable two_ne_zero x)
      (hg.differentiable two_ne_zero x)]
  simp only [Pi.sub_apply]
  ring

theorem smoothedMax_comm (hδ : 0 < δ) (a b : ℝ) : smoothedMax δ a b = smoothedMax δ b a := by
  rw [smoothedMax_def, smoothedMax_def, ← neg_sub, smoothedAbs_neg hδ, add_comm a]

/-- For `δ > 0`, the smoothed maximum is the maximum wherever `δ ≤ |a - b|`. -/
theorem smoothedMax_eq_max (hδ : 0 < δ) {a b : ℝ} (h : δ ≤ |a - b|) :
    smoothedMax δ a b = max a b := by
  rw [smoothedMax_def, smoothedAbs_eq_abs hδ h]
  linarith [max_sub_min_eq_abs' a b, min_add_max a b]

/-- For `δ > 0`, the smoothed maximum of `a` and `b` is `a` when `b + δ ≤ a`. -/
theorem smoothedMax_eq_left (hδ : 0 < δ) {a b : ℝ} (h : b + δ ≤ a) : smoothedMax δ a b = a := by
  rw [smoothedMax_eq_max hδ (by rw [abs_of_nonneg (by linarith)]; linarith),
    max_eq_left (by linarith)]

/-- For `δ > 0`, the smoothed maximum of `a` and `b` is `b` when `a + δ ≤ b`. -/
theorem smoothedMax_eq_right (hδ : 0 < δ) {a b : ℝ} (h : a + δ ≤ b) : smoothedMax δ a b = b := by
  rw [smoothedMax_comm hδ, smoothedMax_eq_left hδ h]

/-- For `δ > 0`, the smoothed maximum lies above the maximum. -/
theorem max_le_smoothedMax (hδ : 0 < δ) (a b : ℝ) : max a b ≤ smoothedMax δ a b := by
  rw [smoothedMax_def]
  linarith [abs_le_smoothedAbs hδ (a - b), max_sub_min_eq_abs' a b, min_add_max a b]

/-- For `δ > 0`, the smoothed maximum lies below `max a b + δ / 2`. -/
theorem smoothedMax_le_max_add (hδ : 0 < δ) (a b : ℝ) :
    smoothedMax δ a b ≤ max a b + δ / 2 := by
  rw [smoothedMax_def]
  linarith [smoothedAbs_le_abs_add hδ (a - b), max_sub_min_eq_abs' a b, min_add_max a b]

/-- For `δ > 0` and `a, b > 0`, the reciprocal of the smoothed maximum of `a` and `b` is at most
the convex combination of `1 / a` and `1 / b` with the weights `(1 ± smoothedSign δ (a - b)) / 2`
of the derivative of `smoothedMax δ`. -/
theorem one_div_smoothedMax_le (hδ : 0 < δ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    1 / smoothedMax δ a b ≤
      (1 + smoothedSign δ (a - b)) / 2 * (1 / a) + (1 - smoothedSign δ (a - b)) / 2 * (1 / b) := by
  have hs := abs_le.1 (abs_smoothedSign_le_one δ (a - b))
  have hm := max_le_smoothedMax hδ a b
  have h₁ : 1 / smoothedMax δ a b ≤ 1 / a :=
    one_div_le_one_div_of_le ha ((le_max_left _ _).trans hm)
  have h₂ : 1 / smoothedMax δ a b ≤ 1 / b :=
    one_div_le_one_div_of_le hb ((le_max_right _ _).trans hm)
  nlinarith [mul_le_mul_of_nonneg_left h₁ (by linarith : 0 ≤ (1 + smoothedSign δ (a - b)) / 2),
    mul_le_mul_of_nonneg_left h₂ (by linarith : 0 ≤ (1 - smoothedSign δ (a - b)) / 2)]

end SymplecticGeometry
