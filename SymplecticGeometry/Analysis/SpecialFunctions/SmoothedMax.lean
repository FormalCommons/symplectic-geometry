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
  `monotone_smoothedSign`, its signs `smoothedSign_nonneg` and `smoothedSign_nonpos`, and its
  derivative `hasDerivAt_smoothedSign`, `deriv_smoothedSign`.
* `SymplecticGeometry.smoothedAbs`: the smoothing of `|t|` on `(-δ, δ)`.
* `SymplecticGeometry.contDiff_smoothedAbs`, `SymplecticGeometry.deriv_smoothedAbs`,
  `SymplecticGeometry.abs_deriv_smoothedAbs_le_one`,
  `SymplecticGeometry.iteratedDeriv_two_smoothedAbs`,
  `SymplecticGeometry.iteratedDeriv_two_smoothedAbs_nonneg`: smoothness, the first two
  derivatives, and bounds on them.
* `SymplecticGeometry.exists_pos_div_le_iteratedDeriv_two_smoothedAbs`: for each `ε > 0` there is
  `c > 0` such that `c / δ ≤ (smoothedAbs δ)''(t)` wherever `|smoothedSign δ t| ≤ 1 - ε`; it is
  a consequence of the lower bound of the next item, with `c = 2 min ε 1`.
  `SymplecticGeometry.one_sub_smoothedSign_sq_div_two_mul_lt` turns it into the bound on the error
  of a smoothing that the smoothed maximum and minimum of two `i`-convex shapes use, and
  `SymplecticGeometry.exists_pos_forall_one_sub_smoothedSign_sq_div_two_mul_lt` gives a `δ₀ > 0`
  below which that bound holds for given margins and bounds.
* `SymplecticGeometry.two_mul_one_sub_smoothedSign_sq_div_le_iteratedDeriv_two_smoothedAbs` and
  `SymplecticGeometry.exists_forall_iteratedDeriv_two_smoothedAbs_le`: the curvature of
  `smoothedAbs δ` lies between `2 (1 - s²) / δ`, with `s = smoothedSign δ t`, and `C / δ` for a
  constant `C`. The lower bound follows from `8 ψ (1 - ψ) ≤ ψ'` for `ψ = Real.smoothTransition`
  (`Real.smoothTransition.eight_mul_mul_one_sub_le_deriv`). By the lower bound, where `T ≤ 2 / δ`
  the curvature makes up for an error `(1 - s²) / 2 · g T`
  (`SymplecticGeometry.one_sub_smoothedSign_sq_div_two_mul_le`).
* `SymplecticGeometry.convexOn_smoothedAbs`: convexity.
* `SymplecticGeometry.smoothedAbs_eq_abs`, `SymplecticGeometry.abs_le_smoothedAbs`,
  `SymplecticGeometry.smoothedAbs_le_abs_add`: comparison with `|t|`.
* `SymplecticGeometry.smoothedMax`: the smoothed maximum, with `contDiff_smoothedMax`,
  `hasDerivAt_smoothedMax_left`, `hasDerivAt_smoothedMax_right`, monotonicity in each argument
  (`monotone_smoothedMax_left`, `monotone_smoothedMax_right`, `smoothedMax_le_smoothedMax`), the
  first and second derivatives `hasDerivAt_smoothedMax`, `deriv_smoothedMax` and
  `iteratedDeriv_two_smoothedMax` of the smoothed maximum of two functions (the second one
  nonnegative where theirs are, `iteratedDeriv_two_smoothedMax_nonneg`, and at least the smaller
  of theirs, `min_iteratedDeriv_two_le_iteratedDeriv_two_smoothedMax`), the first one also
  as a weighted average (`hasDerivAt_smoothedMax_weighted`, `deriv_smoothedMax_weighted`, with
  the weight in `[0, 1]` by `one_add_smoothedSign_div_two_mem_Icc`), the bounds
  `min_deriv_le_deriv_smoothedMax` and `deriv_smoothedMax_le_max`, its positivity where the
  larger argument increases and the other does not decrease (`deriv_smoothedMax_pos_left`,
  `deriv_smoothedMax_pos_right`), `smoothedMax_eq_max`, `smoothedMax_eq_left`,
  `smoothedMax_eq_right`, their versions near a set (`smoothedMax_eventuallyEq_left`,
  `smoothedMax_eventuallyEq_right`) and near a point for arguments continuous there
  (`smoothedMax_eventuallyEq_left_of_continuousAt`,
  `smoothedMax_eventuallyEq_right_of_continuousAt`), near a point within a set for arguments
  continuous there within it (`smoothedMax_eventuallyEq_left_of_continuousWithinAt`,
  `smoothedMax_eventuallyEq_right_of_continuousWithinAt`), on an interval `[a, u)` for arguments
  continuous at `a` within `[a, ∞)` (`exists_eqOn_smoothedMax_right`), `max_le_smoothedMax`,
  `smoothedMax_le_max_add` and `one_div_smoothedMax_le`.
* `SymplecticGeometry.smoothedSign_eq_smoothedSign_one`,
  `SymplecticGeometry.smoothedAbs_eq_mul_smoothedAbs_one` and
  `SymplecticGeometry.smoothedMax_eq_mul_smoothedMax_one`: for `δ ≠ 0`, each is its width-`1`
  version rescaled by `δ`. Since `s ↦ smoothedAbs 1 s - s` is nonnegative and nonincreasing on
  `[0, ∞)`, the rescaling gives `SymplecticGeometry.monotoneOn_smoothedAbs_width` and
  `SymplecticGeometry.monotoneOn_smoothedMax_width`: both grow with the width `δ > 0`. It also
  makes the smoothed maximum smooth in a varying nonzero width
  (`SymplecticGeometry.contDiffAt_smoothedMax`).
* `SymplecticGeometry.smoothedMax_add_add_right`: a common shift of the two arguments shifts the
  smoothed maximum.
* The smoothed minimum `-smoothedMax δ (-a) (-b)` lies in `[min a b - δ / 2, min a b]`
  (`SymplecticGeometry.min_sub_le_neg_smoothedMax_neg`,
  `SymplecticGeometry.neg_smoothedMax_neg_le_min`). So it is at least `c / 2` for a common lower
  bound `c ≥ δ` of `a` and `b` (`SymplecticGeometry.div_two_le_neg_smoothedMax_neg`), and for
  `δ ≤ a, b` its reciprocal is at least `1 / a` and `1 / b`
  (`SymplecticGeometry.one_div_le_one_div_neg_smoothedMax_neg_left`,
  `SymplecticGeometry.one_div_le_one_div_neg_smoothedMax_neg_right`). Its first derivative is
  again a weighted average (`SymplecticGeometry.deriv_neg_smoothedMax_neg_weighted`), and its
  second derivative (`SymplecticGeometry.iteratedDeriv_two_neg_smoothedMax_neg_weighted`) is the
  same average of the second derivatives, minus the curvature term that the smoothed maximum
  gains.
* `SymplecticGeometry.smoothedMaxChain δ A`: the chain whose first member is `A 0` and whose
  `(i + 1)`-th member is the smoothed maximum of the `i`-th one and `A (i + 1)`. Its members are
  as smooth as the `A j`, globally or at a point (`contDiff_smoothedMaxChain`,
  `contDiffAt_smoothedMaxChain`), increase along the chain
  (`monotone_smoothedMaxChain`), lie above the `A j` they are built from
  (`le_smoothedMaxChain_of_le`) and at most `i δ / 2` above one of them
  (`exists_smoothedMaxChain_le_add`), keep the bounds of the slopes of the `A j`
  (`le_deriv_smoothedMaxChain`, `deriv_smoothedMaxChain_le`, `abs_deriv_smoothedMaxChain_le`),
  and are `A i` where the `A j` climb
  by at least `δ` from each to the next (`smoothedMaxChain_eq`,
  `smoothedMaxChain_eventuallyEq`). The chains of smoothed minima `-smoothedMaxChain δ (-A)`
  keep the bounds of the absolute slopes (`abs_deriv_neg_smoothedMaxChain_neg_le`) and are at
  least `c` where the `A j` are at least `c + i δ / 2` (`le_neg_smoothedMaxChain_neg`).
* `SymplecticGeometry.abs_smoothedMax_sub_le`, `SymplecticGeometry.abs_deriv_smoothedMax_sub_le`
  and `SymplecticGeometry.abs_iteratedDeriv_two_smoothedMax_sub_le`: the value and the first two
  derivatives of the smoothed maximum of two functions are as close to any target as the farther
  of the two functions is, up to `δ / 2` for the value and `C (f' - g')² / (2 δ)` for the second
  derivative, where `C / δ` bounds the curvature of `smoothedAbs δ`.

## References

* [K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Chapter 3, smoothing of maxima; the chains of smoothed maxima serve Proposition 3.25.
-/

public section

noncomputable section

open Set Filter Topology intervalIntegral

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

/-- For `δ > 0`, `smoothedSign δ` is nonpositive on `(-∞, 0]`. -/
theorem smoothedSign_nonpos (hδ : 0 < δ) {s : ℝ} (hs : s ≤ 0) : smoothedSign δ s ≤ 0 := by
  have := smoothedSign_nonneg hδ (neg_nonneg.2 hs)
  rw [smoothedSign_neg hδ] at this
  linarith

/-- For `δ ≠ 0`, `smoothedSign δ` is `smoothedSign 1` rescaled by `δ`. -/
theorem smoothedSign_eq_smoothedSign_one (hδ : δ ≠ 0) (s : ℝ) :
    smoothedSign δ s = smoothedSign 1 (s / δ) := by
  rw [smoothedSign_def, smoothedSign_def]
  congr 3
  field_simp

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

/-- The curvature of `smoothedAbs δ` is at least `2 (1 - s²) / δ`, where `s = smoothedSign δ t` is
its slope: a lower bound of order `1 / δ` that degrades only as fast as `1 - s²` where the slope
nears `±1`. -/
theorem two_mul_one_sub_smoothedSign_sq_div_le_iteratedDeriv_two_smoothedAbs (hδ : 0 < δ)
    (t : ℝ) : 2 * (1 - smoothedSign δ t ^ 2) / δ ≤ iteratedDeriv 2 (smoothedAbs δ) t := by
  rw [iteratedDeriv_two_smoothedAbs, smoothedSign_def]
  gcongr
  linarith [Real.smoothTransition.eight_mul_mul_one_sub_le_deriv ((t + δ) / (2 * δ))]

/-- Away from the ends `±1` of its slope, `smoothedAbs δ` curves at a rate of order `1 / δ`: for
each `ε > 0` there is `c > 0`, for instance `c = 2 min ε 1`, such that
`c / δ ≤ (smoothedAbs δ)''(t)` for all `δ > 0` and all `t` with `|smoothedSign δ t| ≤ 1 - ε`. -/
theorem exists_pos_div_le_iteratedDeriv_two_smoothedAbs {ε : ℝ} (hε : 0 < ε) :
    ∃ c > 0, ∀ δ > 0, ∀ t, |smoothedSign δ t| ≤ 1 - ε →
      c / δ ≤ iteratedDeriv 2 (smoothedAbs δ) t := by
  refine ⟨2 * min ε 1, by positivity, fun δ hδ t ht ↦ ?_⟩
  refine le_trans ?_ (two_mul_one_sub_smoothedSign_sq_div_le_iteratedDeriv_two_smoothedAbs hδ t)
  -- With `e = min ε 1 ∈ (0, 1]`, `|s| ≤ 1 - e` gives `1 - s² ≥ e (2 - e) ≥ e`.
  have he₀ : 0 < min ε 1 := lt_min hε one_pos
  have he₁ : min ε 1 ≤ 1 := min_le_right ε 1
  have hs : |smoothedSign δ t| ≤ 1 - min ε 1 := ht.trans (by linarith [min_le_left ε 1])
  have hsq : smoothedSign δ t ^ 2 ≤ (1 - min ε 1) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hs 2
  gcongr
  nlinarith

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

/-- For `δ > 0`, `g ≥ 0` and `T ≤ 2 / δ`, the curvature of `smoothedAbs δ` makes up for the error
`(1 - s²) / 2 · g T`, where `s = smoothedSign δ t`: it is at most `p g / 2`, where
`p = (smoothedAbs δ)'' t`. -/
theorem one_sub_smoothedSign_sq_div_two_mul_le (hδ : 0 < δ) {g T : ℝ} (hg : 0 ≤ g)
    (hT : T ≤ 2 / δ) (t : ℝ) :
    (1 - smoothedSign δ t ^ 2) / 2 * (g * T) ≤ iteratedDeriv 2 (smoothedAbs δ) t * g / 2 := by
  have hp := two_mul_one_sub_smoothedSign_sq_div_le_iteratedDeriv_two_smoothedAbs hδ t
  have hs := abs_le.1 (abs_smoothedSign_le_one δ t)
  have h1s : 0 ≤ 1 - smoothedSign δ t ^ 2 := by nlinarith
  calc (1 - smoothedSign δ t ^ 2) / 2 * (g * T)
      ≤ (1 - smoothedSign δ t ^ 2) / 2 * (g * (2 / δ)) := by gcongr
    _ = 2 * (1 - smoothedSign δ t ^ 2) / δ * g / 2 := by ring
    _ ≤ iteratedDeriv 2 (smoothedAbs δ) t * g / 2 := by gcongr

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

/-- For `δ ≠ 0`, `smoothedAbs δ` is `smoothedAbs 1` rescaled by `δ`. -/
theorem smoothedAbs_eq_mul_smoothedAbs_one (hδ : δ ≠ 0) (t : ℝ) :
    smoothedAbs δ t = δ * smoothedAbs 1 (t / δ) := by
  have h (b : ℝ) : (∫ s in (0 : ℝ)..b, smoothedSign δ s) =
      δ * ∫ s in (0 : ℝ)..b / δ, smoothedSign 1 s := by
    simp_rw [smoothedSign_eq_smoothedSign_one hδ]
    rw [integral_comp_div (smoothedSign 1) hδ, zero_div, smul_eq_mul]
  rw [smoothedAbs_def, smoothedAbs_def, h, h, div_self hδ]
  ring

/-- The value of `smoothedAbs δ` at a point does not decrease as the width `δ > 0` grows. -/
theorem monotoneOn_smoothedAbs_width (t : ℝ) : MonotoneOn (fun δ ↦ smoothedAbs δ t) (Ioi 0) := by
  have key {t : ℝ} (ht : 0 ≤ t) : MonotoneOn (fun δ ↦ smoothedAbs δ t) (Ioi 0) := by
    intro δ (hδ : 0 < δ) δ' (hδ' : 0 < δ') hle
    have h₁ : t / δ' ≤ t / δ := div_le_div_of_nonneg_left ht hδ hle
    have h₂ := antitone_smoothedAbs_sub_id 1 h₁
    have h₃ : 0 ≤ smoothedAbs 1 (t / δ) - t / δ := by
      linarith [abs_le_smoothedAbs one_pos (t / δ), le_abs_self (t / δ)]
    have h₄ := mul_le_mul hle h₂ h₃ hδ'.le
    rw [mul_sub, mul_sub, mul_div_cancel₀ _ hδ.ne', mul_div_cancel₀ _ hδ'.ne'] at h₄
    simp only [smoothedAbs_eq_mul_smoothedAbs_one hδ.ne',
      smoothedAbs_eq_mul_smoothedAbs_one hδ'.ne']
    linarith
  rcases le_total 0 t with ht | ht
  · exact key ht
  · intro δ hδ δ' hδ' hle
    simpa only [smoothedAbs_neg (mem_Ioi.1 hδ), smoothedAbs_neg (mem_Ioi.1 hδ')] using
      key (neg_nonneg.2 ht) hδ hδ' hle

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

/-- For `δ > 0`, if `g x ≤ f x`, `f' > 0` and `g' ≥ 0`, then the smoothed maximum of `f` and `g`
has positive derivative at `x`: the weight of `f'` in `hasDerivAt_smoothedMax_weighted` is at
least `1 / 2`. -/
theorem deriv_smoothedMax_pos_left {f g : ℝ → ℝ} {f' g' x : ℝ} (hδ : 0 < δ)
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) (hle : g x ≤ f x) (hf' : 0 < f')
    (hg' : 0 ≤ g') : 0 < deriv (fun x ↦ smoothedMax δ (f x) (g x)) x := by
  rw [(hasDerivAt_smoothedMax_weighted hf hg).deriv]
  have hs := smoothedSign_nonneg hδ (sub_nonneg.2 hle)
  have hw := one_add_smoothedSign_div_two_mem_Icc δ (f x - g x)
  exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) hf') (mul_nonneg (sub_nonneg.2 hw.2) hg')

/-- For `δ > 0`, if `f x ≤ g x`, `f' ≥ 0` and `g' > 0`, then the smoothed maximum of `f` and `g`
has positive derivative at `x`: the weight of `g'` in `hasDerivAt_smoothedMax_weighted` is at
least `1 / 2`. -/
theorem deriv_smoothedMax_pos_right {f g : ℝ → ℝ} {f' g' x : ℝ} (hδ : 0 < δ)
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) (hle : f x ≤ g x) (hf' : 0 ≤ f')
    (hg' : 0 < g') : 0 < deriv (fun x ↦ smoothedMax δ (f x) (g x)) x := by
  rw [(hasDerivAt_smoothedMax_weighted hf hg).deriv]
  have hs := smoothedSign_nonpos hδ (sub_nonpos.2 hle)
  have hw := one_add_smoothedSign_div_two_mem_Icc δ (f x - g x)
  exact add_pos_of_nonneg_of_pos (mul_nonneg hw.1 hf') (mul_pos (by linarith) hg')

/-- The second derivative at `x` of the smoothed maximum of two functions `f` and `g` that are
`C²` at `x`: with `s = smoothedSign δ (f x - g x)`, it is
`(f'' + g'' + s (f'' - g'') + (smoothedAbs δ)'' (f x - g x) (f' - g')²) / 2`. -/
theorem iteratedDeriv_two_smoothedMax {f g : ℝ → ℝ} {x : ℝ} (hf : ContDiffAt ℝ 2 f x)
    (hg : ContDiffAt ℝ 2 g x) :
    iteratedDeriv 2 (fun x ↦ smoothedMax δ (f x) (g x)) x =
      (iteratedDeriv 2 f x + iteratedDeriv 2 g x +
        smoothedSign δ (f x - g x) * (iteratedDeriv 2 f x - iteratedDeriv 2 g x) +
        iteratedDeriv 2 (smoothedAbs δ) (f x - g x) * (deriv f x - deriv g x) ^ 2) / 2 := by
  have h : (fun x ↦ smoothedMax δ (f x) (g x)) =
      fun x ↦ (f x + g x + (smoothedAbs δ ∘ (f - g)) x) / 2 := by
    funext y
    simp only [smoothedMax_def, Function.comp_apply, Pi.sub_apply]
  have hh := (contDiff_smoothedAbs (n := 2) δ).contDiffAt (x := (f - g) x)
  have hfg := hf.sub hg
  rw [h, iteratedDeriv_div_const, iteratedDeriv_fun_add (hf.add hg) (hh.comp x hfg),
    iteratedDeriv_fun_add hf hg, iteratedDeriv_comp_two hh hfg, iteratedDeriv_sub hf hg,
    deriv_smoothedAbs, deriv_sub (hf.differentiableAt two_ne_zero)
      (hg.differentiableAt two_ne_zero)]
  simp only [Pi.sub_apply]
  ring

/-- For `δ ≥ 0`, the second derivative at `x` of the smoothed maximum of two functions `f` and
`g` that are `C²` at `x` is at least the smaller of those of `f` and `g`. -/
theorem min_iteratedDeriv_two_le_iteratedDeriv_two_smoothedMax {f g : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) (hδ : 0 ≤ δ) :
    min (iteratedDeriv 2 f x) (iteratedDeriv 2 g x) ≤
      iteratedDeriv 2 (fun x ↦ smoothedMax δ (f x) (g x)) x := by
  rw [iteratedDeriv_two_smoothedMax hf hg]
  have hs := abs_le.1 (abs_smoothedSign_le_one δ (f x - g x))
  have h₁ := mul_le_mul_of_nonneg_left (min_le_left (iteratedDeriv 2 f x) (iteratedDeriv 2 g x))
    (by linarith : 0 ≤ 1 + smoothedSign δ (f x - g x))
  have h₂ := mul_le_mul_of_nonneg_left (min_le_right (iteratedDeriv 2 f x) (iteratedDeriv 2 g x))
    (by linarith : 0 ≤ 1 - smoothedSign δ (f x - g x))
  have h₃ := mul_nonneg (iteratedDeriv_two_smoothedAbs_nonneg hδ (f x - g x))
    (sq_nonneg (deriv f x - deriv g x))
  linarith

/-- For `δ ≥ 0`, the second derivative at `x` of the smoothed maximum of two functions `f` and
`g` that are `C²` at `x` is nonnegative if those of `f` and `g` are. -/
theorem iteratedDeriv_two_smoothedMax_nonneg {f g : ℝ → ℝ} {x : ℝ} (hf : ContDiffAt ℝ 2 f x)
    (hg : ContDiffAt ℝ 2 g x) (hδ : 0 ≤ δ) (hf₂ : 0 ≤ iteratedDeriv 2 f x)
    (hg₂ : 0 ≤ iteratedDeriv 2 g x) :
    0 ≤ iteratedDeriv 2 (fun x ↦ smoothedMax δ (f x) (g x)) x :=
  (le_min hf₂ hg₂).trans (min_iteratedDeriv_two_le_iteratedDeriv_two_smoothedMax hf hg hδ)

/-- For `δ ≠ 0`, `smoothedMax δ` is `smoothedMax 1` rescaled by `δ`. -/
theorem smoothedMax_eq_mul_smoothedMax_one (hδ : δ ≠ 0) (a b : ℝ) :
    smoothedMax δ a b = δ * smoothedMax 1 (a / δ) (b / δ) := by
  rw [smoothedMax_def, smoothedMax_def, smoothedAbs_eq_mul_smoothedAbs_one hδ, ← sub_div]
  field_simp

/-- The smoothed maximum is smooth jointly in its width and its two arguments where the width
does not vanish: if `η`, `f` and `g` are `Cⁿ` at `x` and `η x ≠ 0`, then
`y ↦ smoothedMax (η y) (f y) (g y)` is `Cⁿ` at `x`. -/
theorem contDiffAt_smoothedMax {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ∞}
    {η f g : E → ℝ} {x : E} (hη : ContDiffAt ℝ n η x) (hη₀ : η x ≠ 0)
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x) :
    ContDiffAt ℝ n (fun y ↦ smoothedMax (η y) (f y) (g y)) x := by
  -- Near `x` the width does not vanish, and the smoothed maximum is rescaled to width `1`.
  refine (hη.mul ((contDiff_smoothedMax 1).contDiffAt.comp x
    ((hf.div hη hη₀).prodMk (hg.div hη hη₀)))).congr_of_eventuallyEq ?_
  filter_upwards [hη.continuousAt.eventually_ne hη₀] with y hy
  exact smoothedMax_eq_mul_smoothedMax_one hy _ _

/-- Adding the same number to both arguments of the smoothed maximum adds it to the value. -/
theorem smoothedMax_add_add_right (δ a b c : ℝ) :
    smoothedMax δ (a + c) (b + c) = smoothedMax δ a b + c := by
  rw [smoothedMax_def, smoothedMax_def, add_sub_add_right_eq_sub]
  ring

/-- The smoothed maximum of two numbers does not decrease as the width `δ > 0` grows. -/
theorem monotoneOn_smoothedMax_width (a b : ℝ) :
    MonotoneOn (fun δ ↦ smoothedMax δ a b) (Ioi 0) := fun δ hδ δ' hδ' hle ↦ by
  simp only [smoothedMax_def]
  linarith [monotoneOn_smoothedAbs_width (a - b) hδ hδ' hle]

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

/-- For `δ > 0` and continuous `f` and `g` with `g + δ < f` on `s`, the smoothed maximum of `f`
and `g` equals `f` on a neighbourhood of `s`. -/
theorem smoothedMax_eventuallyEq_left {X : Type*} [TopologicalSpace X] {f g : X → ℝ}
    {s : Set X} (hδ : 0 < δ) (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x ∈ s, g x + δ < f x) : (fun x ↦ smoothedMax δ (f x) (g x)) =ᶠ[𝓝ˢ s] f := by
  filter_upwards [(isOpen_lt (hg.add continuous_const) hf).mem_nhdsSet.2 h] with x hx
  exact smoothedMax_eq_left hδ hx.le

/-- For `δ > 0` and continuous `f` and `g` with `f + δ < g` on `s`, the smoothed maximum of `f`
and `g` equals `g` on a neighbourhood of `s`. -/
theorem smoothedMax_eventuallyEq_right {X : Type*} [TopologicalSpace X] {f g : X → ℝ}
    {s : Set X} (hδ : 0 < δ) (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x ∈ s, f x + δ < g x) : (fun x ↦ smoothedMax δ (f x) (g x)) =ᶠ[𝓝ˢ s] g := by
  filter_upwards [(isOpen_lt (hf.add continuous_const) hg).mem_nhdsSet.2 h] with x hx
  exact smoothedMax_eq_right hδ hx.le

/-- For `δ > 0` and `f` and `g` continuous at `x` with `g x + δ < f x`, the smoothed maximum
of `f` and `g` equals `f` near `x`. -/
theorem smoothedMax_eventuallyEq_left_of_continuousAt {X : Type*} [TopologicalSpace X]
    {f g : X → ℝ} {x : X} (hδ : 0 < δ) (hf : ContinuousAt f x) (hg : ContinuousAt g x)
    (h : g x + δ < f x) : (fun y ↦ smoothedMax δ (f y) (g y)) =ᶠ[𝓝 x] f := by
  filter_upwards [(hg.add continuousAt_const).eventually_lt hf h] with y hy
  exact smoothedMax_eq_left hδ hy.le

/-- For `δ > 0` and `f` and `g` continuous at `x` with `f x + δ < g x`, the smoothed maximum
of `f` and `g` equals `g` near `x`. -/
theorem smoothedMax_eventuallyEq_right_of_continuousAt {X : Type*} [TopologicalSpace X]
    {f g : X → ℝ} {x : X} (hδ : 0 < δ) (hf : ContinuousAt f x) (hg : ContinuousAt g x)
    (h : f x + δ < g x) : (fun y ↦ smoothedMax δ (f y) (g y)) =ᶠ[𝓝 x] g := by
  filter_upwards [(hf.add continuousAt_const).eventually_lt hg h] with y hy
  exact smoothedMax_eq_right hδ hy.le

/-- For `δ > 0` and `f` and `g` continuous at `x` within `s` with `g x + δ < f x`, the
smoothed maximum of `f` and `g` equals `f` near `x` within `s`. -/
theorem smoothedMax_eventuallyEq_left_of_continuousWithinAt {X : Type*} [TopologicalSpace X]
    {f g : X → ℝ} {s : Set X} {x : X} (hδ : 0 < δ) (hf : ContinuousWithinAt f s x)
    (hg : ContinuousWithinAt g s x) (h : g x + δ < f x) :
    (fun y ↦ smoothedMax δ (f y) (g y)) =ᶠ[𝓝[s] x] f := by
  filter_upwards [(hg.add continuousWithinAt_const).eventually_lt hf h] with y hy
  exact smoothedMax_eq_left hδ hy.le

/-- For `δ > 0` and `f` and `g` continuous at `x` within `s` with `f x + δ < g x`, the
smoothed maximum of `f` and `g` equals `g` near `x` within `s`. -/
theorem smoothedMax_eventuallyEq_right_of_continuousWithinAt {X : Type*} [TopologicalSpace X]
    {f g : X → ℝ} {s : Set X} {x : X} (hδ : 0 < δ) (hf : ContinuousWithinAt f s x)
    (hg : ContinuousWithinAt g s x) (h : f x + δ < g x) :
    (fun y ↦ smoothedMax δ (f y) (g y)) =ᶠ[𝓝[s] x] g := by
  filter_upwards [(hf.add continuousWithinAt_const).eventually_lt hg h] with y hy
  exact smoothedMax_eq_right hδ hy.le

/-- For `δ > 0` and `f` and `g` continuous at `a` within `[a, ∞)` with `f a + δ < g a`, the
smoothed maximum of `f` and `g` equals `g` on some interval `[a, u)` with `a < u`. -/
theorem exists_eqOn_smoothedMax_right {a : ℝ} {f g : ℝ → ℝ} (hδ : 0 < δ)
    (hf : ContinuousWithinAt f (Ici a) a) (hg : ContinuousWithinAt g (Ici a) a)
    (h : f a + δ < g a) :
    ∃ u, a < u ∧ EqOn (fun r ↦ smoothedMax δ (f r) (g r)) g (Ico a u) :=
  mem_nhdsGE_iff_exists_Ico_subset.1
    (smoothedMax_eventuallyEq_right_of_continuousWithinAt hδ hf hg h)

/-- For `δ > 0`, the smoothed maximum lies above the maximum. -/
theorem max_le_smoothedMax (hδ : 0 < δ) (a b : ℝ) : max a b ≤ smoothedMax δ a b := by
  rw [smoothedMax_def]
  linarith [abs_le_smoothedAbs hδ (a - b), max_sub_min_eq_abs' a b, min_add_max a b]

/-- For `δ > 0`, the smoothed maximum lies below `max a b + δ / 2`. -/
theorem smoothedMax_le_max_add (hδ : 0 < δ) (a b : ℝ) :
    smoothedMax δ a b ≤ max a b + δ / 2 := by
  rw [smoothedMax_def]
  linarith [smoothedAbs_le_abs_add hδ (a - b), max_sub_min_eq_abs' a b, min_add_max a b]

/-- For `δ > 0`, the smoothed maximum of `a` and `b` is as close to any `c` as the farther of `a`
and `b`, up to `δ / 2`. -/
theorem abs_smoothedMax_sub_le (hδ : 0 < δ) (a b c : ℝ) :
    |smoothedMax δ a b - c| ≤ max |a - c| |b - c| + δ / 2 := by
  have h := abs_max_sub_max_le_max a b c c
  rw [max_self] at h
  rw [abs_le] at h ⊢
  constructor <;>
    linarith [max_le_smoothedMax hδ a b, smoothedMax_le_max_add hδ a b, h.1, h.2]

/-- The derivative of the smoothed maximum of two functions differentiable at `x` is as close to
any `φ` as the farther of their derivatives. -/
theorem abs_deriv_smoothedMax_sub_le {f g : ℝ → ℝ} {x : ℝ} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (φ : ℝ) :
    |deriv (fun x ↦ smoothedMax δ (f x) (g x)) x - φ| ≤
      max |deriv f x - φ| |deriv g x - φ| := by
  have hw := one_add_smoothedSign_div_two_mem_Icc δ (f x - g x)
  rw [deriv_smoothedMax_weighted hf hg]
  simpa [Real.dist_eq] using (convexOn_univ_dist φ).le_on_segment' (Set.mem_univ _)
    (Set.mem_univ _) hw.1 (sub_nonneg.2 hw.2) (add_sub_cancel _ _)

/-- The second derivative at `x` of the smoothed maximum of two functions `f` and `g` that are
`C²` at `x` is as close to any `φ` as the farther of their second derivatives, up to
`C (f' - g')² / (2 δ)` where `C / δ` bounds the curvature of `smoothedAbs δ` at `f x - g x`
(`exists_forall_iteratedDeriv_two_smoothedAbs_le` gives such a `C` for all `δ > 0`). -/
theorem abs_iteratedDeriv_two_smoothedMax_sub_le {f g : ℝ → ℝ} {C x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) (hδ : 0 ≤ δ)
    (hC : iteratedDeriv 2 (smoothedAbs δ) (f x - g x) ≤ C / δ) (φ : ℝ) :
    |iteratedDeriv 2 (fun x ↦ smoothedMax δ (f x) (g x)) x - φ| ≤
      max |iteratedDeriv 2 f x - φ| |iteratedDeriv 2 g x - φ| +
        C * (deriv f x - deriv g x) ^ 2 / (2 * δ) := by
  have hw := one_add_smoothedSign_div_two_mem_Icc δ (f x - g x)
  have h := (convexOn_univ_dist φ).le_on_segment' (Set.mem_univ (iteratedDeriv 2 f x))
    (Set.mem_univ (iteratedDeriv 2 g x)) hw.1 (sub_nonneg.2 hw.2) (add_sub_cancel _ _)
  simp only [smul_eq_mul, Real.dist_eq] at h
  replace h := abs_le.1 h
  have hp := iteratedDeriv_two_smoothedAbs_nonneg hδ (f x - g x)
  have hsq := sq_nonneg (deriv f x - deriv g x)
  have hB : iteratedDeriv 2 (smoothedAbs δ) (f x - g x) * (deriv f x - deriv g x) ^ 2 / 2 ≤
      C * (deriv f x - deriv g x) ^ 2 / (2 * δ) := by
    rw [mul_comm (2 : ℝ), ← div_div, mul_div_right_comm C]
    gcongr
  rw [iteratedDeriv_two_smoothedMax hf hg, abs_le]
  constructor <;> linarith [mul_nonneg hp hsq]

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

/-! ### The smoothed minimum -/

/-- For `δ > 0`, the smoothed minimum `-smoothedMax δ (-a) (-b)` is at most `min a b`. -/
theorem neg_smoothedMax_neg_le_min (hδ : 0 < δ) (a b : ℝ) :
    -smoothedMax δ (-a) (-b) ≤ min a b := by
  have h := max_le_smoothedMax hδ (-a) (-b)
  rw [max_neg_neg] at h
  linarith

/-- For `δ > 0`, the smoothed minimum `-smoothedMax δ (-a) (-b)` is at least `min a b - δ / 2`. -/
theorem min_sub_le_neg_smoothedMax_neg (hδ : 0 < δ) (a b : ℝ) :
    min a b - δ / 2 ≤ -smoothedMax δ (-a) (-b) := by
  have h := smoothedMax_le_max_add hδ (-a) (-b)
  rw [max_neg_neg] at h
  linarith

/-- For `δ > 0` and a common lower bound `c ≥ δ` of `a` and `b`, the smoothed minimum
`-smoothedMax δ (-a) (-b)` is at least `c / 2`. -/
theorem div_two_le_neg_smoothedMax_neg (hδ : 0 < δ) {a b c : ℝ} (hc : δ ≤ c) (ha : c ≤ a)
    (hb : c ≤ b) : c / 2 ≤ -smoothedMax δ (-a) (-b) := by
  linarith [min_sub_le_neg_smoothedMax_neg hδ a b, le_min ha hb]

/-- For `δ > 0` with `δ ≤ a` and `δ ≤ b`, the reciprocal of the smoothed minimum
`-smoothedMax δ (-a) (-b)` is at least `1 / a`. -/
theorem one_div_le_one_div_neg_smoothedMax_neg_left (hδ : 0 < δ) {a b : ℝ} (ha : δ ≤ a)
    (hb : δ ≤ b) : 1 / a ≤ 1 / -smoothedMax δ (-a) (-b) :=
  one_div_le_one_div_of_le (by linarith [div_two_le_neg_smoothedMax_neg hδ le_rfl ha hb])
    ((neg_smoothedMax_neg_le_min hδ a b).trans (min_le_left _ _))

/-- For `δ > 0` with `δ ≤ a` and `δ ≤ b`, the reciprocal of the smoothed minimum
`-smoothedMax δ (-a) (-b)` is at least `1 / b`. -/
theorem one_div_le_one_div_neg_smoothedMax_neg_right (hδ : 0 < δ) {a b : ℝ} (ha : δ ≤ a)
    (hb : δ ≤ b) : 1 / b ≤ 1 / -smoothedMax δ (-a) (-b) :=
  one_div_le_one_div_of_le (by linarith [div_two_le_neg_smoothedMax_neg hδ le_rfl ha hb])
    ((neg_smoothedMax_neg_le_min hδ a b).trans (min_le_right _ _))

/-- The derivative of the smoothed minimum `x ↦ -smoothedMax δ (-f x) (-g x)` of two functions
differentiable at `x`, as a weighted average: with `w = (1 + smoothedSign δ (g x - f x)) / 2`,
which lies in `[0, 1]` (`one_add_smoothedSign_div_two_mem_Icc`), it is
`w * f'(x) + (1 - w) * g'(x)`. -/
theorem deriv_neg_smoothedMax_neg_weighted {f g : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    deriv (fun x ↦ -smoothedMax δ (-f x) (-g x)) x =
      (1 + smoothedSign δ (g x - f x)) / 2 * deriv f x +
        (1 - (1 + smoothedSign δ (g x - f x)) / 2) * deriv g x := by
  rw [deriv.fun_neg, deriv_smoothedMax (f := fun x ↦ -f x) (g := fun x ↦ -g x) hf.neg hg.neg]
  simp only [deriv.fun_neg, neg_sub_neg]
  ring

/-- The second derivative of the smoothed minimum `x ↦ -smoothedMax δ (-f x) (-g x)` of two
functions `C²` at `x`: with the weight `w = (1 + smoothedSign δ (g x - f x)) / 2` of
`deriv_neg_smoothedMax_neg_weighted`, it is `w * f''(x) + (1 - w) * g''(x)` minus the term
`(smoothedAbs δ)'' (g x - f x) * (f'(x) - g'(x))² / 2`, which `iteratedDeriv_two_smoothedMax`
adds for the smoothed maximum. -/
theorem iteratedDeriv_two_neg_smoothedMax_neg_weighted {f g : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    iteratedDeriv 2 (fun x ↦ -smoothedMax δ (-f x) (-g x)) x =
      (1 + smoothedSign δ (g x - f x)) / 2 * iteratedDeriv 2 f x +
        (1 - (1 + smoothedSign δ (g x - f x)) / 2) * iteratedDeriv 2 g x -
        iteratedDeriv 2 (smoothedAbs δ) (g x - f x) * (deriv f x - deriv g x) ^ 2 / 2 := by
  rw [iteratedDeriv_fun_neg, iteratedDeriv_two_smoothedMax hf.neg hg.neg, iteratedDeriv_fun_neg,
    iteratedDeriv_fun_neg]
  simp only [deriv.fun_neg, neg_sub_neg]
  ring

/-! ### Chains of smoothed maxima -/

/-- The **chain of smoothed maxima** of a sequence of functions `A : ℕ → ℝ → ℝ`: its first member
is `A 0`, and each next one is the smoothed maximum, of width `δ`, of the previous member and the
next function of the sequence. -/
def smoothedMaxChain (δ : ℝ) (A : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => A 0
  | i + 1 => fun r ↦ smoothedMax δ (smoothedMaxChain δ A i r) (A (i + 1) r)

section smoothedMaxChain

variable {A : ℕ → ℝ → ℝ} {i : ℕ} {r : ℝ}

@[simp]
theorem smoothedMaxChain_zero (δ : ℝ) (A : ℕ → ℝ → ℝ) : smoothedMaxChain δ A 0 = A 0 :=
  (rfl)

theorem smoothedMaxChain_succ (δ : ℝ) (A : ℕ → ℝ → ℝ) (i : ℕ) :
    smoothedMaxChain δ A (i + 1) =
      fun r ↦ smoothedMax δ (smoothedMaxChain δ A i r) (A (i + 1) r) :=
  (rfl)

@[simp]
theorem smoothedMaxChain_succ_apply (δ : ℝ) (A : ℕ → ℝ → ℝ) (i : ℕ) (r : ℝ) :
    smoothedMaxChain δ A (i + 1) r = smoothedMax δ (smoothedMaxChain δ A i r) (A (i + 1) r) :=
  (rfl)

/-- A member of the chain of smoothed maxima is `Cⁿ` at `r` if the functions it is built from
are. -/
theorem contDiffAt_smoothedMaxChain {n : ℕ∞} (δ : ℝ) (hA : ∀ j ≤ i, ContDiffAt ℝ n (A j) r) :
    ContDiffAt ℝ n (smoothedMaxChain δ A i) r := by
  induction i with
  | zero => rw [smoothedMaxChain_zero]; exact hA 0 le_rfl
  | succ i ih =>
    rw [smoothedMaxChain_succ]
    exact (contDiff_smoothedMax δ).contDiffAt.comp r
      ((ih fun j hj ↦ hA j (Nat.le_succ_of_le hj)).prodMk (hA (i + 1) le_rfl))

/-- A member of the chain of smoothed maxima is as smooth as the functions it is built from. -/
theorem contDiff_smoothedMaxChain {n : ℕ∞} (δ : ℝ) (hA : ∀ j ≤ i, ContDiff ℝ n (A j)) :
    ContDiff ℝ n (smoothedMaxChain δ A i) :=
  contDiff_iff_contDiffAt.2 fun _ ↦
    contDiffAt_smoothedMaxChain δ fun j hj ↦ (hA j hj).contDiffAt

/-- A member of the chain of smoothed maxima is differentiable at `r` if the functions it is
built from are. -/
theorem differentiableAt_smoothedMaxChain (δ : ℝ)
    (hA : ∀ j ≤ i, DifferentiableAt ℝ (A j) r) :
    DifferentiableAt ℝ (smoothedMaxChain δ A i) r := by
  induction i with
  | zero => rw [smoothedMaxChain_zero]; exact hA 0 le_rfl
  | succ i ih =>
    rw [smoothedMaxChain_succ]
    exact (hasDerivAt_smoothedMax (ih fun j hj ↦ hA j (Nat.le_succ_of_le hj)).hasDerivAt
      (hA (i + 1) le_rfl).hasDerivAt).differentiableAt

/-- For `δ > 0`, each member of the chain of smoothed maxima lies below the next one. -/
theorem smoothedMaxChain_le_succ (hδ : 0 < δ) (A : ℕ → ℝ → ℝ) (i : ℕ) (r : ℝ) :
    smoothedMaxChain δ A i r ≤ smoothedMaxChain δ A (i + 1) r := by
  rw [smoothedMaxChain_succ_apply]
  exact (le_max_left _ _).trans (max_le_smoothedMax hδ _ _)

/-- For `δ > 0`, the chain of smoothed maxima increases at each point. -/
theorem monotone_smoothedMaxChain (hδ : 0 < δ) (A : ℕ → ℝ → ℝ) (r : ℝ) :
    Monotone fun i ↦ smoothedMaxChain δ A i r :=
  monotone_nat_of_le_succ fun i ↦ smoothedMaxChain_le_succ hδ A i r

/-- For `δ > 0`, the `i`-th member of the chain of smoothed maxima lies above `A i`. -/
theorem le_smoothedMaxChain (hδ : 0 < δ) (A : ℕ → ℝ → ℝ) (i : ℕ) (r : ℝ) :
    A i r ≤ smoothedMaxChain δ A i r := by
  cases i with
  | zero => rw [smoothedMaxChain_zero]
  | succ i =>
    rw [smoothedMaxChain_succ_apply]
    exact (le_max_right _ _).trans (max_le_smoothedMax hδ _ _)

/-- For `δ > 0`, the `i`-th member of the chain of smoothed maxima lies above every `A j` with
`j ≤ i`. -/
theorem le_smoothedMaxChain_of_le (hδ : 0 < δ) (A : ℕ → ℝ → ℝ) {j : ℕ} (hj : j ≤ i) (r : ℝ) :
    A j r ≤ smoothedMaxChain δ A i r :=
  (le_smoothedMaxChain hδ A j r).trans (monotone_smoothedMaxChain hδ A r hj)

/-- For `δ > 0`, the `i`-th member of the chain of smoothed maxima exceeds one of the functions
`A j`, `j ≤ i`, by at most `i δ / 2`. -/
theorem exists_smoothedMaxChain_le_add (hδ : 0 < δ) (A : ℕ → ℝ → ℝ) (i : ℕ) (r : ℝ) :
    ∃ j ≤ i, smoothedMaxChain δ A i r ≤ A j r + i * δ / 2 := by
  induction i with
  | zero => exact ⟨0, le_rfl, by simp⟩
  | succ i ih =>
    obtain ⟨j, hj, h⟩ := ih
    have h₁ := smoothedMax_le_max_add hδ (smoothedMaxChain δ A i r) (A (i + 1) r)
    rw [smoothedMaxChain_succ_apply]
    push_cast
    rcases le_total (smoothedMaxChain δ A i r) (A (i + 1) r) with h₂ | h₂
    · rw [max_eq_right h₂] at h₁
      have : 0 ≤ (i : ℝ) * δ := by positivity
      exact ⟨i + 1, le_rfl, by linarith⟩
    · rw [max_eq_left h₂] at h₁
      exact ⟨j, Nat.le_succ_of_le hj, by linarith⟩

/-- The derivative at `r` of a member of the chain of smoothed maxima is at least `m` if those
of the functions it is built from are. -/
theorem le_deriv_smoothedMaxChain (δ : ℝ) {m : ℝ} (hA : ∀ j ≤ i, DifferentiableAt ℝ (A j) r)
    (hm : ∀ j ≤ i, m ≤ deriv (A j) r) : m ≤ deriv (smoothedMaxChain δ A i) r := by
  induction i with
  | zero => rw [smoothedMaxChain_zero]; exact hm 0 le_rfl
  | succ i ih =>
    have hA' : ∀ j ≤ i, DifferentiableAt ℝ (A j) r := fun j hj ↦ hA j (Nat.le_succ_of_le hj)
    rw [smoothedMaxChain_succ]
    exact (le_min (ih hA' fun j hj ↦ hm j (Nat.le_succ_of_le hj)) (hm (i + 1) le_rfl)).trans
      (min_deriv_le_deriv_smoothedMax (differentiableAt_smoothedMaxChain δ hA')
        (hA (i + 1) le_rfl))

/-- The derivative at `r` of a member of the chain of smoothed maxima is at most `G` if those
of the functions it is built from are. -/
theorem deriv_smoothedMaxChain_le (δ : ℝ) {G : ℝ} (hA : ∀ j ≤ i, DifferentiableAt ℝ (A j) r)
    (hG : ∀ j ≤ i, deriv (A j) r ≤ G) : deriv (smoothedMaxChain δ A i) r ≤ G := by
  induction i with
  | zero => rw [smoothedMaxChain_zero]; exact hG 0 le_rfl
  | succ i ih =>
    have hA' : ∀ j ≤ i, DifferentiableAt ℝ (A j) r := fun j hj ↦ hA j (Nat.le_succ_of_le hj)
    rw [smoothedMaxChain_succ]
    exact (deriv_smoothedMax_le_max (differentiableAt_smoothedMaxChain δ hA')
      (hA (i + 1) le_rfl)).trans
        (max_le (ih hA' fun j hj ↦ hG j (Nat.le_succ_of_le hj)) (hG (i + 1) le_rfl))

/-- The derivative at `r` of a member of the chain of smoothed maxima is at most `G` in absolute
value if those of the functions it is built from are. -/
theorem abs_deriv_smoothedMaxChain_le (δ : ℝ) {G : ℝ}
    (hA : ∀ j ≤ i, DifferentiableAt ℝ (A j) r) (hG : ∀ j ≤ i, |deriv (A j) r| ≤ G) :
    |deriv (smoothedMaxChain δ A i) r| ≤ G :=
  abs_le.2 ⟨le_deriv_smoothedMaxChain δ hA fun j hj ↦ (abs_le.1 (hG j hj)).1,
    deriv_smoothedMaxChain_le δ hA fun j hj ↦ (abs_le.1 (hG j hj)).2⟩

/-- The derivative at `r` of a member of the chain of smoothed minima
`-smoothedMaxChain δ (-A)` is at most `G` in absolute value if those of `A 0, …, A i` are. -/
theorem abs_deriv_neg_smoothedMaxChain_neg_le (δ : ℝ) {G : ℝ}
    (hA : ∀ j ≤ i, DifferentiableAt ℝ (A j) r) (hG : ∀ j ≤ i, |deriv (A j) r| ≤ G) :
    |deriv (fun r ↦ -smoothedMaxChain δ (fun j r ↦ -A j r) i r) r| ≤ G := by
  rw [deriv.fun_neg, abs_neg]
  exact abs_deriv_smoothedMaxChain_le δ (fun j hj ↦ (hA j hj).neg) fun j hj ↦ by
    rw [deriv.fun_neg, abs_neg]
    exact hG j hj

/-- For `δ > 0`, the `i`-th member of the chain of smoothed minima `-smoothedMaxChain δ (-A)` is
at least `c` at `r` if `A 0, …, A i` are at least `c + i δ / 2` there. -/
theorem le_neg_smoothedMaxChain_neg (hδ : 0 < δ) {c : ℝ} (h : ∀ j ≤ i, c + i * δ / 2 ≤ A j r) :
    c ≤ -smoothedMaxChain δ (fun j r ↦ -A j r) i r := by
  obtain ⟨j, hj, hle⟩ := exists_smoothedMaxChain_le_add hδ (fun j r ↦ -A j r) i r
  linarith [h j hj]

/-- For `δ > 0`, if at `r` each of `A 0, …, A i` lies at least `δ` below the next, then the
`i`-th member of the chain of smoothed maxima is `A i` at `r`. -/
theorem smoothedMaxChain_eq (hδ : 0 < δ) (h : ∀ j < i, A j r + δ ≤ A (j + 1) r) :
    smoothedMaxChain δ A i r = A i r := by
  induction i with
  | zero => rw [smoothedMaxChain_zero]
  | succ i ih =>
    rw [smoothedMaxChain_succ_apply, ih fun j hj ↦ h j (Nat.lt_succ_of_lt hj)]
    exact smoothedMax_eq_right hδ (h i (Nat.lt_succ_self i))

/-- For `δ > 0`, if eventually along `l` each of `A 0, …, A i` lies at least `δ` below the next,
then the `i`-th member of the chain of smoothed maxima is eventually `A i` along `l`. -/
theorem smoothedMaxChain_eventuallyEq {l : Filter ℝ} (hδ : 0 < δ)
    (h : ∀ᶠ r in l, ∀ j < i, A j r + δ ≤ A (j + 1) r) :
    smoothedMaxChain δ A i =ᶠ[l] A i :=
  h.mono fun _ ↦ smoothedMaxChain_eq hδ

end smoothedMaxChain

end SymplecticGeometry
