/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.ConvexShape.Basic

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import SymplecticGeometry.Analysis.Polynomial.RealCubic
import SymplecticGeometry.Analysis.SpecialFunctions.Log.Bounds
import SymplecticGeometry.Analysis.SpecialFunctions.Sqrt
import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.ConvexShape.SmoothedMax
import SymplecticGeometry.Order.Interval.Set.Piecewise
import SymplecticGeometry.Topology.Order.Piecewise
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Calculus.Deriv.Second
import TauCeti.Analysis.Real.Sqrt

/-!
# Special `i`-convex shapes

Explicit `i`-convex shapes (`SymplecticGeometry.IsConvexShapeAt`) from Cieliebak and Eliashberg's
§4.5, from which their model handle is put together.

* `SymplecticGeometry.struweShape δ K c`: the function
  `r ↦ c + ∫ u in K * δ..r, 1 / √(log (u / δ))`. For `r > δ` its slope is `1 / √(log (r / δ))`
  (`SymplecticGeometry.deriv_struweShape`), and its second derivative is `-χ'³ / (2 r)`
  (`SymplecticGeometry.iteratedDeriv_two_struweShape`), so that it solves Struwe's equation
  `χ'' + χ'³ / (2 r) = 0`, with an infinite slope at `δ` and the value `c` and the slope
  `1 / √(log K)` at `K δ` (`SymplecticGeometry.deriv_struweShape_mul`). It is
  smooth on `(δ, ∞)` and continuous and strictly increasing on `[δ, ∞)`
  (`SymplecticGeometry.contDiffOn_struweShape`, `SymplecticGeometry.continuousOn_struweShape`,
  `SymplecticGeometry.strictMonoOn_struweShape`), and smooth jointly in its value at `K δ` and
  in `r` (`SymplecticGeometry.contDiffOn_uncurry_struweShape`). For `δ ≠ 0` it is the shape of
  width `1` rescaled by `δ` (`SymplecticGeometry.struweShape_eq_mul_struweShape_one`). The shape
  of width `1` rises by at most `√2 * √(r ^ 2 - 1)` from `1` to `r ≥ 1`
  (`SymplecticGeometry.struweShape_sub_struweShape_one_mem_Icc`).
* `SymplecticGeometry.isConvexShapeAt_struweShape_of_lt`: at `r > δ`, Struwe's shape is an
  `i`-convex shape once its value at `r` exceeds `r √L` and `2 r √L³`, with `L = log (r / δ)`.
  On a whole interval `(δ, R]` it suffices that its value at `δ` bounds both quantities at `R`
  (`SymplecticGeometry.isConvexShapeAt_struweShape_of_le_of_mem_Ioc`).
* `SymplecticGeometry.isConvexShapeAt_struweShape`: for `0 < d`, `0 < δ`, `exp (4 / d²) ≤ K`
  and `4 K δ ≤ (log K) ^ (-3 / 2)`, the solution with `c = 1 + d K δ` is an `i`-convex shape on
  `(δ, K δ]`, has slope at most `d` at `K δ`, takes at `δ` a value in `[1 + d δ, 1 + d K δ)`,
  and has slope tending to `+∞` at `δ`.
* `SymplecticGeometry.isConvexShapeAt_sqrt_sub`: the shape `√(a r² - c)` for `a > 1`, at each
  `r > 0` with `c < a r²`; `√(ℓ² + a r²)` is its case `c = -ℓ²`. Its derivative
  `a r / √(a r² - c)` is `Real.deriv_sqrt_sub` (with `Real.hasDerivAt_sqrt_sub`), and its
  second derivative,
  `-a c / √(a r² - c)³`, is `Real.iteratedDeriv_two_sqrt_sub`.
* `SymplecticGeometry.isConvexShapeAt_sqrt`, `SymplecticGeometry.isConvexShapeAt_quadratic` and
  `SymplecticGeometry.isConvexShapeAt_linear`: the shapes `√(ℓ² + a r²)` for `a > 1`,
  `ℓ + b r + c r² / (2 ℓ)` for `c > 1`, and `ℓ + d r` for `r < ℓ d³`.
  Their second derivatives, `a ℓ² / √(ℓ² + a r²)³`, `c / ℓ` and `0`, are
  `Real.iteratedDeriv_two_sqrt_quadratic`,
  `SymplecticGeometry.iteratedDeriv_two_quadratic` and
  `SymplecticGeometry.iteratedDeriv_two_linear`.

* The crossings of these three shapes on `(0, ∞)`. `√(ℓ² + a r²)` and `ℓ + d r` meet only at
  `2 ℓ d / (a - d²)` (`SymplecticGeometry.sqrt_eq_linear_iff`), and `ℓ + b r + c r² / (2 ℓ)` and
  `ℓ + d r` only at `2 ℓ (d - b) / c` (`SymplecticGeometry.quadratic_eq_linear_iff`), with the
  order on either side given by `SymplecticGeometry.sqrt_lt_linear_iff`,
  `SymplecticGeometry.linear_lt_sqrt_iff`, `SymplecticGeometry.quadratic_lt_linear_iff` and
  `SymplecticGeometry.linear_lt_quadratic_iff`. If the quadratic shape with `b, c > 0` is below
  `√(ℓ² + a r²)` somewhere, the two meet at exactly two points, with the quadratic shape below
  between them and above outside (`SymplecticGeometry.exists_crossings_quadratic_sqrt`):
  there `(ℓ + b r + c r² / (2 ℓ))² - ℓ² - a r²` is `r` times a cubic whose coefficients of `1`
  and `r³` are positive, whose sign `SymplecticGeometry.exists_two_roots_cubic_of_neg` gives.
* `SymplecticGeometry.exists_isConvexShapeAt_eq_linear_eq_sqrt`: for `1 < a` and `0 < γ`, a
  smooth `i`-convex shape on `(0, ∞)` that is `1 + d r`, for some `d ∈ (0, 1)`, near `0` and
  `√(1 + a r²)` on `[γ, ∞)`, and whose tangents at `r ≥ 0` meet the vertical axis above `0`.
  It comes from
  `SymplecticGeometry.exists_isConvexShapeAt_eq_linear_eq_sqrt_of_quadratic_lt`, which passes
  from the linear to the quadratic shape and from there to the square-root one, given a point
  `r₀` where the quadratic shape is below the square-root one, and from the constants
  `b = γ (a - 1) / 16`, `c = (1 + a) / 2` of `SymplecticGeometry.quadratic_lt_sqrt_of_mul_sq_le`,
  for which `r₀ = γ` is such a point once `γ (a + 1)² ≤ a - 1`. The three shapes are convex, and
  so is each smoothed maximum that joins them, so the shape is convex; hence its tangents meet
  the axis no lower than those of `√(1 + a r²)` far out, at `1 / √(1 + a r²) > 0`.
* `SymplecticGeometry.exists_isConvexShapeAt_eq_struweShape_eq_linear`: for `ℓ` large compared
  with `K δ`, Struwe's shape with value `ℓ + d K δ` at `K δ` joined to the line `ℓ + d r`, an
  `i`-convex shape on `(δ, 2 K δ]` that is the former up to `3 K δ / 4` and the latter from
  `3 K δ / 2` on. Struwe's shape is strictly concave
  (`SymplecticGeometry.strictConcaveOn_struweShape`), and its secant from `δ` to `K δ` has slope
  at most `d` (`SymplecticGeometry.struweShape_secant_le`), so by Mathlib's
  `StrictConcaveOn.secant_strict_mono` it crosses the line only at `K δ`
  (`SymplecticGeometry.linear_lt_struweShape`, `SymplecticGeometry.struweShape_lt_linear`);
  there the two are joined by `SymplecticGeometry.exists_isConvexShapeAt_eqOn_Iic_Ici`, applied
  to a smooth function on `ℝ` that is Struwe's shape near `[K δ / 4, 2 K δ]` (Tau Ceti's
  `ContDiffOn.exists_contDiff_eventuallyEq_on_isCompact`).
* `SymplecticGeometry.exists_convexShape_surround`: for `1 < a` and `0 < γ`, some `δ ∈ (0, γ)` and
  an `i`-convex shape on `(δ, ∞)`, smooth there and continuous on `[δ, ∞)`, that is `√(1 + a r²)`
  on `[γ, ∞)`, has infinite slope at `δ` and a value in `(1, 1 + γ)` at `δ`: the previous shape
  for `ℓ = 1`, followed from `2 K δ` on by the shape of Lemma 4.19, whose linear part has
  slope `d`.

The shapes are checked with `SymplecticGeometry.isConvexShapeAt_iff`. For Struwe's shape the two
inequalities read `r √L < χ` and `2 r √L³ < χ`, with `L = log (r / δ)`; the second follows from
`4 K δ √(log K)³ ≤ 1`, and the first also uses the lower bound `1 + d δ` of `χ`. That bound
amounts to `∫ u in δ..K δ, 1 / √(log (u / δ)) ≤ d (K - 1) δ`
(`SymplecticGeometry.integral_one_div_sqrt_log_div_le`, and in terms of the value at `δ`,
`SymplecticGeometry.sub_le_struweShape`), which is proved by comparing
the integrand minus `d` with its product by `u₀ / u`, where `u₀ = δ exp (1 / d²)` is the point
where the integrand equals `d`, and integrating the latter exactly.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  §4.5: Lemma 4.15, Remark 4.16, Lemma 4.17 (a), (b), (e), Lemma 4.18, Lemma 4.19,
  Remark 4.20 and Proposition 4.21.
-/

public section

noncomputable section

namespace SymplecticGeometry

open Real Set Filter Topology MeasureTheory intervalIntegral TauCeti
open scoped ContDiff Interval

/-- **Struwe's shape**: `r ↦ c + ∫ u in K δ..r, 1 / √(log (u / δ))`. It takes the value `c` at
`K δ`, and for `δ > 0` and `K ≥ 1` it solves Struwe's equation `χ'' + χ'³ / (2 r) = 0` on
`(δ, ∞)`, with slope tending to `+∞` at `δ`. -/
def struweShape (δ K c r : ℝ) : ℝ :=
  c + ∫ u in K * δ..r, 1 / √(log (u / δ))

theorem struweShape_def (δ K c r : ℝ) :
    struweShape δ K c r = c + ∫ u in K * δ..r, 1 / √(log (u / δ)) := (rfl)

/-- Raising the value of Struwe's shape at `K δ` by `a` raises the whole shape by `a`. -/
theorem struweShape_add (δ K a c r : ℝ) :
    struweShape δ K (a + c) r = a + struweShape δ K c r := by
  rw [struweShape_def, struweShape_def, add_assoc]

@[simp]
theorem struweShape_apply_mul (δ K c : ℝ) : struweShape δ K c (K * δ) = c := by
  simp [struweShape_def]

/-- For `K = 1`, Struwe's shape takes the value `c` at `δ`. -/
@[simp]
theorem struweShape_one_apply_self (δ c : ℝ) : struweShape δ 1 c δ = c := by
  simpa using struweShape_apply_mul δ 1 c

/-- For `δ ≠ 0`, Struwe's shape of width `δ` is the one of width `1` rescaled by `δ`. -/
theorem struweShape_eq_mul_struweShape_one {δ : ℝ} (hδ : δ ≠ 0) (K c : ℝ) :
    struweShape δ K c = fun r ↦ δ * struweShape 1 K (c / δ) (r / δ) := by
  ext r
  have h := integral_comp_div (fun u ↦ 1 / √(log u)) hδ (a := K * δ) (b := r)
  simp only [struweShape_def, mul_one, div_one]
  rw [h, mul_div_cancel_right₀ _ hδ, smul_eq_mul, mul_add, mul_div_cancel₀ _ hδ]

section Struwe

variable {δ K : ℝ}

/-- The derivative of `u ↦ √(log (u / δ))` for `u > δ > 0`. -/
private theorem hasDerivAt_sqrt_log (hδ : 0 < δ) {u : ℝ} (hu : δ < u) :
    HasDerivAt (fun u ↦ √(log (u / δ))) (1 / (2 * u * √(log (u / δ)))) u := by
  have hu₀ : 0 < u := hδ.trans hu
  have hL : 0 < log (u / δ) := log_pos ((one_lt_div hδ).2 hu)
  have h := (((hasDerivAt_id' u).div_const δ).log (div_pos hu₀ hδ).ne').sqrt hL.ne'
  convert h using 1
  field_simp

private theorem continuousOn_sqrt_log (hδ : 0 < δ) (b : ℝ) :
    ContinuousOn (fun u ↦ √(log (u / δ))) (Icc δ b) := by
  refine (ContinuousOn.log (continuousOn_id.div_const δ) fun u hu ↦ ?_).sqrt
  have : 0 < u / δ := div_pos (hδ.trans_le hu.1) hδ
  exact this.ne'

private theorem measurable_struwe (δ : ℝ) : Measurable fun u ↦ 1 / √(log (u / δ)) := by
  fun_prop

/-- The integrand of `struweShape` is integrable on `[δ, b]`, although it is unbounded near
`δ`: on `(δ, b]` it is at most `b` times `1 / (u √(log (u / δ)))`, twice the derivative of
`√(log (u / δ))`. -/
private theorem intervalIntegrable_deriv_sqrt_log (hδ : 0 < δ) {b : ℝ} (hb : δ ≤ b) :
    IntervalIntegrable (fun u ↦ 1 / (2 * u * √(log (u / δ)))) volume δ b :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hb).2 <|
    integrableOn_deriv_of_nonneg (continuousOn_sqrt_log hδ b)
      (fun u hu ↦ hasDerivAt_sqrt_log hδ hu.1) fun u hu ↦ by
        have := hδ.trans hu.1
        positivity

private theorem intervalIntegrable_struwe (hδ : 0 < δ) {b : ℝ} (hb : δ ≤ b) :
    IntervalIntegrable (fun u ↦ 1 / √(log (u / δ))) volume δ b := by
  have hg := ((intervalIntegrable_iff_integrableOn_Ioc_of_le hb).1
    (intervalIntegrable_deriv_sqrt_log hδ hb))
  refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hb).2 ?_
  refine (hg.const_mul (2 * b)).mono' (measurable_struwe δ).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioc fun u hu ↦ ?_
  have hu₀ : 0 < u := hδ.trans hu.1
  have hS : 0 < √(log (u / δ)) := sqrt_pos.2 (log_pos ((one_lt_div hδ).2 hu.1))
  rw [norm_of_nonneg (by positivity), show 2 * b * (1 / (2 * u * √(log (u / δ)))) =
    b / u * (1 / √(log (u / δ))) by field_simp]
  exact le_mul_of_one_le_left (by positivity) ((one_le_div hu₀).2 hu.2)

private theorem intervalIntegrable_struwe_of_lt (hδ : 0 < δ) (hK : 1 ≤ K) {r : ℝ}
    (hr : δ ≤ r) : IntervalIntegrable (fun u ↦ 1 / √(log (u / δ))) volume (K * δ) r :=
  (intervalIntegrable_struwe hδ (le_mul_of_one_le_left hδ.le hK)).symm.trans
    (intervalIntegrable_struwe hδ hr)

/-- The slope of Struwe's shape at `r > δ` is `1 / √(log (r / δ))`. -/
theorem hasDerivAt_struweShape (hδ : 0 < δ) (hK : 1 ≤ K) (c : ℝ) {r : ℝ} (hr : δ < r) :
    HasDerivAt (struweShape δ K c) (1 / √(log (r / δ))) r := by
  have hc : ContinuousAt (fun u ↦ 1 / √(log (u / δ))) r := by
    have hr₀ : 0 < r := hδ.trans hr
    have hS : 0 < √(log (r / δ)) := sqrt_pos.2 (log_pos ((one_lt_div hδ).2 hr))
    exact continuousAt_const.div
      ((continuousAt_id.div_const δ).log (div_pos hr₀ hδ).ne').sqrt hS.ne'
  have h := integral_hasDerivAt_right (intervalIntegrable_struwe_of_lt hδ hK hr.le)
    (measurable_struwe δ).stronglyMeasurable.stronglyMeasurableAtFilter hc
  exact h.const_add c

/-- The slope of Struwe's shape at `r > δ` is `1 / √(log (r / δ))`. -/
theorem deriv_struweShape (hδ : 0 < δ) (hK : 1 ≤ K) (c : ℝ) {r : ℝ} (hr : δ < r) :
    deriv (struweShape δ K c) r = 1 / √(log (r / δ)) :=
  (hasDerivAt_struweShape hδ hK c hr).deriv

/-- The slope of Struwe's shape at `K δ`, where it takes the value `c`, is `1 / √(log K)`. -/
theorem deriv_struweShape_mul (hδ : 0 < δ) (hK : 1 < K) (c : ℝ) :
    deriv (struweShape δ K c) (K * δ) = 1 / √(log K) := by
  rw [deriv_struweShape hδ hK.le c (lt_mul_of_one_lt_left hδ hK), mul_div_cancel_right₀ _ hδ.ne']

/-- Struwe's equation: the second derivative of Struwe's shape at `r > δ` is `-χ'³ / (2 r)`,
with `χ' = 1 / √(log (r / δ))`. -/
theorem iteratedDeriv_two_struweShape (hδ : 0 < δ) (hK : 1 ≤ K) (c : ℝ) {r : ℝ} (hr : δ < r) :
    iteratedDeriv 2 (struweShape δ K c) r = -(1 / √(log (r / δ))) ^ 3 / (2 * r) := by
  have heq : deriv (struweShape δ K c) =ᶠ[𝓝 r] (fun u ↦ √(log (u / δ)))⁻¹ :=
    (lt_mem_nhds hr).mono fun u hu ↦ by rw [deriv_struweShape hδ hK c hu, one_div, Pi.inv_apply]
  have hS : 0 < √(log (r / δ)) := sqrt_pos.2 (log_pos ((one_lt_div hδ).2 hr))
  have hr₀ : 0 < r := hδ.trans hr
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  have h := (hasDerivAt_sqrt_log hδ hr).inv hS.ne'
  rw [heq.deriv_eq, h.deriv]
  field_simp

/-- The slope of Struwe's shape tends to `+∞` at `δ`. -/
theorem tendsto_deriv_struweShape (hδ : 0 < δ) (hK : 1 ≤ K) (c : ℝ) :
    Tendsto (deriv (struweShape δ K c)) (𝓝[>] δ) atTop := by
  have hc : ContinuousAt (fun u ↦ log (u / δ)) δ :=
    (continuousAt_id.div_const δ).log (by simp [hδ.ne'])
  have h₀ : Tendsto (fun u ↦ √(log (u / δ))) (𝓝[>] δ) (𝓝[>] 0) := by
    refine tendsto_sqrt_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩)
    · simpa [hδ.ne'] using hc.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with u (hu : δ < u)
      exact log_pos ((one_lt_div hδ).2 hu)
  refine (tendsto_inv_nhdsGT_zero.comp h₀).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u (hu : δ < u)
  rw [deriv_struweShape hδ hK c hu, one_div]
  rfl

/-- Struwe's shape is smooth on `(δ, ∞)`. -/
theorem contDiffOn_struweShape (hδ : 0 < δ) (hK : 1 ≤ K) (c : ℝ) :
    ContDiffOn ℝ ∞ (struweShape δ K c) (Ioi δ) := by
  have hL : ∀ u ∈ Ioi δ, 0 < log (u / δ) := fun u hu ↦ log_pos ((one_lt_div hδ).2 hu)
  refine (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).2
    ⟨fun r hr ↦ (hasDerivAt_struweShape hδ hK c hr).differentiableAt.differentiableWithinAt, ?_⟩
  have hf : ContDiffOn ℝ ∞ (fun u ↦ 1 / √(log (u / δ))) (Ioi δ) :=
    contDiffOn_const.div (((contDiffOn_id.div_const δ).log fun u hu ↦
      (div_pos (hδ.trans hu) hδ).ne').sqrt fun u hu ↦ (hL u hu).ne')
      fun u hu ↦ (sqrt_pos.2 (hL u hu)).ne'
  exact hf.congr fun r hr ↦ deriv_struweShape hδ hK c hr

/-- Struwe's shape is smooth jointly in its value `c` at `K δ` and in `r`, on `ℝ × (δ, ∞)`:
it is `c` plus the shape with value `0` at `K δ`. -/
theorem contDiffOn_uncurry_struweShape (hδ : 0 < δ) (hK : 1 ≤ K) :
    ContDiffOn ℝ ∞ (Function.uncurry (struweShape δ K)) (univ ×ˢ Ioi δ) := by
  have e : Function.uncurry (struweShape δ K) = fun p ↦ p.1 + struweShape δ K 0 p.2 := by
    ext p
    rw [Function.uncurry_apply_pair, ← struweShape_add, add_zero]
  rw [e]
  exact contDiffOn_fst.add ((contDiffOn_struweShape hδ hK 0).comp contDiffOn_snd
    fun p hp ↦ hp.2)

/-- **Changing the base point of Struwe's shape.** For `δ > 0`, `1 ≤ K`, `1 ≤ K'` and `δ ≤ r`,
Struwe's shape with value `c` at `K δ` is the one based at `K' δ` with the same value there: all
Struwe shapes for the radius `δ` differ by constants on `[δ, ∞)`. -/
theorem struweShape_eq_struweShape_apply_mul (hδ : 0 < δ) (hK : 1 ≤ K) {K' : ℝ} (hK' : 1 ≤ K')
    (c : ℝ) {r : ℝ} (hr : δ ≤ r) :
    struweShape δ K c r = struweShape δ K' (struweShape δ K c (K' * δ)) r := by
  rw [struweShape_def, struweShape_def, struweShape_def, add_assoc,
    integral_add_adjacent_intervals
      (intervalIntegrable_struwe_of_lt hδ hK (le_mul_of_one_le_left hδ.le hK'))
      (intervalIntegrable_struwe_of_lt hδ hK' hr)]

/-- Struwe's shape is continuous on `[δ, ∞)`: its integrand is integrable near `δ`. -/
theorem continuousOn_struweShape (hδ : 0 < δ) (hK : 1 ≤ K) (c : ℝ) :
    ContinuousOn (struweShape δ K c) (Ici δ) := by
  intro r (hr : δ ≤ r)
  set b := max r (K * δ) + 1
  have hrb : r < b := by linarith [le_max_left r (K * δ)]
  have hb : δ ≤ b := hr.trans hrb.le
  have hKδ : K * δ ∈ [[δ, b]] := by
    rw [uIcc_of_le hb]
    exact ⟨le_mul_of_one_le_left hδ.le hK, by linarith [le_max_right r (K * δ)]⟩
  have h := (continuousOn_primitive_interval' (intervalIntegrable_struwe hδ hb) hKδ).const_add c
  rw [uIcc_of_le hb, ← funext (struweShape_def δ K c)] at h
  refine (h r ⟨hr, hrb.le⟩).mono_of_mem_nhdsWithin ?_
  rw [← Ici_inter_Iic]
  exact inter_mem_nhdsWithin _ (Iic_mem_nhds hrb)

/-- Struwe's shape is strictly increasing on `[δ, ∞)`. -/
theorem strictMonoOn_struweShape (hδ : 0 < δ) (hK : 1 ≤ K) (c : ℝ) :
    StrictMonoOn (struweShape δ K c) (Ici δ) :=
  strictMonoOn_of_deriv_pos (convex_Ici δ) (continuousOn_struweShape hδ hK c) fun r hr ↦ by
    rw [interior_Ici] at hr
    rw [deriv_struweShape hδ hK c hr]
    exact one_div_pos.2 (sqrt_pos.2 (log_pos ((one_lt_div hδ).2 hr)))

/-- Struwe's shape is strictly concave on `[δ, ∞)`: its slope `1 / √(log (r / δ))` is strictly
decreasing on `(δ, ∞)`. -/
theorem strictConcaveOn_struweShape (hδ : 0 < δ) (hK : 1 ≤ K) (c : ℝ) :
    StrictConcaveOn ℝ (Ici δ) (struweShape δ K c) := by
  refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Ici δ) (continuousOn_struweShape hδ hK c)
    ?_
  rw [interior_Ici]
  intro x (hx : δ < x) y (hy : δ < y) hxy
  rw [deriv_struweShape hδ hK c hx, deriv_struweShape hδ hK c hy]
  have hLx : 0 < log (x / δ) := log_pos ((one_lt_div hδ).2 hx)
  exact one_div_lt_one_div_of_lt (sqrt_pos.2 hLx) (sqrt_lt_sqrt hLx.le
    (log_lt_log (div_pos (hδ.trans hx) hδ) (div_lt_div_of_pos_right hxy hδ)))

/-- Near `r = 1`, Struwe's shape of width `1` rises by at most `√2 * √(r ^ 2 - 1)`: for
`1 ≤ K` and `1 ≤ r`, `0 ≤ struweShape 1 K c r - struweShape 1 K c 1 ≤ √2 * √(r ^ 2 - 1)`.
Its slope `1 / √(log r)` is at most `√2 * r / √(r ^ 2 - 1)` (`Real.one_div_sqrt_log_le`), the
slope of `√2 * √(r ^ 2 - 1)`. -/
theorem struweShape_sub_struweShape_one_mem_Icc (hK : 1 ≤ K) (c : ℝ) {r : ℝ} (hr : 1 ≤ r) :
    struweShape 1 K c r - struweShape 1 K c 1 ∈ Icc 0 (√2 * √(r ^ 2 - 1)) := by
  refine ⟨sub_nonneg.2 ((strictMonoOn_struweShape one_pos hK c).monotoneOn
    self_mem_Ici hr hr), ?_⟩
  set f : ℝ → ℝ := fun u ↦ struweShape 1 K c u - √2 * √(u ^ 2 - 1)
  have hd : ∀ u : ℝ, 1 < u → HasDerivAt f (1 / √(log u) - √2 * (u / √(u ^ 2 - 1))) u := by
    intro u hu
    have h := (hasDerivAt_sqrt_sub (a := 1) (c := 1) (r := u) (by nlinarith)).const_mul √2
    simp only [one_mul] at h
    have hT := hasDerivAt_struweShape one_pos hK c hu
    rw [div_one] at hT
    exact hT.sub h
  have hf : AntitoneOn f (Ici 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 1) ?_ ?_ ?_
    · exact (continuousOn_struweShape one_pos hK c).sub (by fun_prop)
    · rw [interior_Ici]
      exact fun u hu ↦ (hd u hu).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro u (hu : 1 < u)
      rw [(hd u hu).deriv, sub_nonpos, ← mul_div_assoc]
      exact one_div_sqrt_log_le hu
  have h := hf self_mem_Ici hr hr
  simp only [f, one_pow, sub_self, sqrt_zero, mul_zero, sub_zero] at h
  linarith

/-- From a point `a > δ` on, Struwe's shape rises by at most its slope `1 / √(log (a / δ))` at `a`
times the distance, by concavity. -/
theorem struweShape_sub_struweShape_le (hδ : 0 < δ) (hK : 1 ≤ K) (c : ℝ) {a r : ℝ}
    (ha : δ < a) (hr : a ≤ r) :
    struweShape δ K c r - struweShape δ K c a ≤ (r - a) / √(log (a / δ)) := by
  rcases hr.eq_or_lt with rfl | hr
  · simp
  have h := (strictConcaveOn_struweShape hδ hK c).concaveOn.slope_le_of_hasDerivAt
    (mem_Ici.2 ha.le) (mem_Ici.2 (ha.trans hr).le) hr (hasDerivAt_struweShape hδ hK c ha)
  rw [slope_def_field, div_le_iff₀ (sub_pos.2 hr)] at h
  rw [div_eq_mul_one_div, mul_comm]
  exact h

/-- If Struwe's shape with value `ℓ + d K δ` at `K δ` is at least `ℓ + d δ` at `δ`, its secant
between `δ` and `K δ` has slope at most `d`. -/
theorem struweShape_secant_le (hδ : 0 < δ) (hK : 1 < K) {ℓ d : ℝ}
    (h : ℓ + d * δ ≤ struweShape δ K (ℓ + d * K * δ) δ) :
    (struweShape δ K (ℓ + d * K * δ) δ - (ℓ + d * K * δ)) / (δ - K * δ) ≤ d :=
  (div_le_iff_of_neg (sub_neg.2 (lt_mul_of_one_lt_left hδ hK))).2 (by linarith)

/-- Struwe's shape with value `ℓ + d K δ` at `K δ`, if it is at least `ℓ + d δ` at `δ`, lies above
the line `ℓ + d r` on `(δ, K δ)`, by strict concavity. -/
theorem linear_lt_struweShape (hδ : 0 < δ) (hK : 1 < K) {ℓ d r : ℝ}
    (h : ℓ + d * δ ≤ struweShape δ K (ℓ + d * K * δ) δ) (hr : r ∈ Ioo δ (K * δ)) :
    ℓ + d * r < struweShape δ K (ℓ + d * K * δ) r := by
  have hδK : δ < K * δ := lt_mul_of_one_lt_left hδ hK
  have hs := (strictConcaveOn_struweShape hδ hK.le (ℓ + d * K * δ)).secant_strict_mono
    (mem_Ici.2 hδK.le) (mem_Ici.2 le_rfl) (mem_Ici.2 hr.1.le) hδK.ne hr.2.ne hr.1
  rw [struweShape_apply_mul] at hs
  linarith [(div_lt_iff_of_neg (sub_neg.2 hr.2)).1 (hs.trans_le (struweShape_secant_le hδ hK h))]

/-- Struwe's shape with value `ℓ + d K δ` at `K δ`, if it is at least `ℓ + d δ` at `δ`, lies below
the line `ℓ + d r` on `(K δ, ∞)`, by strict concavity. -/
theorem struweShape_lt_linear (hδ : 0 < δ) (hK : 1 < K) {ℓ d r : ℝ}
    (h : ℓ + d * δ ≤ struweShape δ K (ℓ + d * K * δ) δ) (hr : K * δ < r) :
    struweShape δ K (ℓ + d * K * δ) r < ℓ + d * r := by
  have hδK : δ < K * δ := lt_mul_of_one_lt_left hδ hK
  have hs := (strictConcaveOn_struweShape hδ hK.le (ℓ + d * K * δ)).secant_strict_mono
    (mem_Ici.2 hδK.le) (mem_Ici.2 le_rfl) (mem_Ici.2 (hδK.trans hr).le) hδK.ne hr.ne'
    (hδK.trans hr)
  rw [struweShape_apply_mul] at hs
  linarith [(div_lt_iff₀ (sub_pos.2 hr)).1 (hs.trans_le (struweShape_secant_le hδ hK h))]

/-- At `r > δ`, Struwe's shape is an `i`-convex shape if its value at `r` exceeds both
`r √L` and `2 r √L³`, where `L = log (r / δ)`. -/
theorem isConvexShapeAt_struweShape_of_lt (hδ : 0 < δ) (hK : 1 ≤ K) {c r : ℝ} (hr : δ < r)
    (h₁ : r * √(log (r / δ)) < struweShape δ K c r)
    (h₂ : 2 * r * √(log (r / δ)) ^ 3 < struweShape δ K c r) :
    IsConvexShapeAt (struweShape δ K c) r := by
  have hr₀ : 0 < r := hδ.trans hr
  set t := √(log (r / δ))
  have ht₀ : 0 < t := sqrt_pos.2 (log_pos ((one_lt_div hδ).2 hr))
  have hχ₀ : 0 < struweShape δ K c r := (by positivity : 0 < r * t).trans h₁
  refine isConvexShapeAt_iff.2 ⟨hr₀, hχ₀, ?_, ?_⟩
  · rw [deriv_struweShape hδ hK _ hr, div_div, div_lt_div_iff₀ hχ₀ (by positivity)]
    linarith
  · rw [deriv_struweShape hδ hK _ hr, iteratedDeriv_two_struweShape hδ hK _ hr]
    have e : -(1 / t) ^ 3 / (2 * r) + (1 / t) ^ 3 / r = 1 / (2 * r * t ^ 3) := by
      field_simp
      ring
    rw [e, div_lt_div_iff₀ hχ₀ (by positivity)]
    linarith

/-- Struwe's shape is an `i`-convex shape at every point of `(δ, R]` if its value at `δ` is at
least `m`, `R √(log (R / δ)) ≤ m` and `2 R √(log (R / δ))³ ≤ m`. -/
theorem isConvexShapeAt_struweShape_of_le_of_mem_Ioc {c m R r : ℝ} (hδ : 0 < δ)
    (hK : 1 ≤ K) (h : m ≤ struweShape δ K c δ) (h₁ : R * √(log (R / δ)) ≤ m)
    (h₂ : 2 * R * √(log (R / δ)) ^ 3 ≤ m) (hr : r ∈ Ioc δ R) :
    IsConvexShapeAt (struweShape δ K c) r := by
  have hS : m < struweShape δ K c r := h.trans_lt (strictMonoOn_struweShape hδ hK _
    (mem_Ici.2 le_rfl) (mem_Ici.2 hr.1.le) hr.1)
  have hr₀ : 0 < r := hδ.trans hr.1
  have hR : 0 ≤ R := hr₀.le.trans hr.2
  have ht₀ : 0 ≤ √(log (r / δ)) := sqrt_nonneg _
  have ht : √(log (r / δ)) ≤ √(log (R / δ)) :=
    sqrt_le_sqrt (log_le_log (div_pos hr₀ hδ) (div_le_div_of_nonneg_right hr.2 hδ.le))
  refine isConvexShapeAt_struweShape_of_lt hδ hK hr.1 ?_ ?_
  · nlinarith [mul_le_mul hr.2 ht ht₀ hR]
  · nlinarith [mul_le_mul hr.2 (pow_le_pow_left₀ ht₀ ht 3) (by positivity) hR]

/-- The bounds on `K` that the hypothesis `exp (4 / d²) ≤ K` gives: `1 < K`, `0 < log K` and
`2 ≤ d √(log K)`. -/
private theorem struwe_log_bounds {d : ℝ} (hd : 0 < d) (hK : exp (4 / d ^ 2) ≤ K) :
    1 < K ∧ 0 < log K ∧ 2 ≤ d * √(log K) := by
  have hlog : 4 / d ^ 2 ≤ log K := by simpa using log_le_log (exp_pos _) hK
  have hlog₀ : 0 < log K := (by positivity : (0 : ℝ) < 4 / d ^ 2).trans_le hlog
  refine ⟨(one_lt_exp_iff.2 (by positivity : (0 : ℝ) < 4 / d ^ 2)).trans_le hK, hlog₀, ?_⟩
  have h4 : √(4 / d ^ 2) = 2 / d := by
    rw [sqrt_div' _ (by positivity), show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num),
      sqrt_sq hd.le]
  have := sqrt_le_sqrt hlog
  rw [h4, div_le_iff₀ hd] at this
  linarith

/-- The integral of the integrand of Struwe's shape over `[δ, K δ]` is at most `d (K - 1) δ`
when `exp (4 / d²) ≤ K`. -/
theorem integral_one_div_sqrt_log_div_le {d : ℝ} (hd : 0 < d) (hδ : 0 < δ)
    (hK : exp (4 / d ^ 2) ≤ K) :
    ∫ u in δ..K * δ, 1 / √(log (u / δ)) ≤ d * (K - 1) * δ := by
  -- The integrand minus `d` is at most its product by `u₀ / u`, where `u₀ = δ exp (1 / d²)` is
  -- the point where the integrand equals `d`, and that product integrates to
  -- `u₀ (2 √(log K) - d log K) ≤ 0`.
  set f : ℝ → ℝ := fun u ↦ 1 / √(log (u / δ)) with hf
  set u₀ := δ * exp (1 / d ^ 2)
  obtain ⟨hK₁, hlog₀, hs⟩ := struwe_log_bounds hd hK
  have hδK : δ ≤ K * δ := le_mul_of_one_le_left hδ.le hK₁.le
  set g : ℝ → ℝ := fun u ↦ 2 * u₀ * (1 / (2 * u * √(log (u / δ)))) - u₀ * d * u⁻¹
  have hint₁ := intervalIntegrable_deriv_sqrt_log hδ hδK
  have hint₂ : IntervalIntegrable (fun u : ℝ ↦ u⁻¹) volume δ (K * δ) :=
    intervalIntegral.intervalIntegrable_inv (fun u hu ↦ by
      have : 0 < u := hδ.trans_le (by simpa [hδK] using hu.1)
      exact this.ne') (continuousOn_id)
  have hfi := intervalIntegrable_struwe hδ hδK
  -- The pointwise comparison.
  have hpt : ∀ u ∈ Ioo δ (K * δ), f u - d ≤ g u := by
    intro u hu
    have hu₀ : 0 < u := hδ.trans hu.1
    have hL : 0 < log (u / δ) := log_pos ((one_lt_div hδ).2 hu.1)
    have hS : 0 < √(log (u / δ)) := sqrt_pos.2 hL
    have hu : u = δ * exp (log (u / δ)) := by
      rw [exp_log (div_pos hu₀ hδ)]
      field_simp
    have hg : g u = u₀ / u * (f u - d) := by
      simp only [g, hf]
      field_simp
    rw [hg]
    -- `(f u - d) (1 - u₀ / u) ≤ 0`: the two factors have opposite signs.
    have key : (f u - d) * (u - u₀) ≤ 0 := by
      rcases le_total (log (u / δ)) (1 / d ^ 2) with h | h
      · have h₁ : u ≤ u₀ := by
          rw [hu]
          exact mul_le_mul_of_nonneg_left (exp_le_exp.2 h) hδ.le
        have h₂ : d ≤ f u := by
          have : √(log (u / δ)) ≤ 1 / d := by
            calc √(log (u / δ)) ≤ √(1 / d ^ 2) := sqrt_le_sqrt h
              _ = 1 / d := by rw [sqrt_div' _ (by positivity), sqrt_one, sqrt_sq hd.le]
          simp only [hf]
          rw [le_div_iff₀ hS]
          rwa [le_div_iff₀ hd, mul_comm] at this
        nlinarith
      · have h₁ : u₀ ≤ u := by
          rw [hu]
          exact mul_le_mul_of_nonneg_left (exp_le_exp.2 h) hδ.le
        have h₂ : f u ≤ d := by
          have : 1 / d ≤ √(log (u / δ)) := by
            calc 1 / d = √(1 / d ^ 2) := by
                  rw [sqrt_div' _ (by positivity), sqrt_one, sqrt_sq hd.le]
              _ ≤ √(log (u / δ)) := sqrt_le_sqrt h
          simp only [hf]
          rw [div_le_iff₀ hS]
          rwa [div_le_iff₀ hd, mul_comm] at this
        nlinarith
    have : f u - d - u₀ / u * (f u - d) = (f u - d) * (u - u₀) / u := by
      field_simp
    have : (f u - d) * (u - u₀) / u ≤ 0 := div_nonpos_of_nonpos_of_nonneg key hu₀.le
    linarith
  have hmono := integral_mono_on_of_le_Ioo hδK (hfi.sub intervalIntegrable_const)
    ((hint₁.const_mul _).sub (hint₂.const_mul _)) hpt
  -- The two sides.
  have hlhs : ∫ u in δ..K * δ, (f u - d) = (∫ u in δ..K * δ, f u) - (K * δ - δ) * d := by
    rw [integral_sub hfi intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul]
  have hftc : ∫ u in δ..K * δ, 1 / (2 * u * √(log (u / δ))) = √(log K) := by
    rw [integral_eq_sub_of_hasDerivAt_of_le hδK (continuousOn_sqrt_log hδ (K * δ))
      (fun u hu ↦ hasDerivAt_sqrt_log hδ hu.1) hint₁]
    simp [hδ.ne']
  have hrhs : ∫ u in δ..K * δ, g u = u₀ * (2 * √(log K) - d * log K) := by
    simp only [g]
    rw [integral_sub (hint₁.const_mul _) (hint₂.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, hftc, integral_inv_of_pos hδ (by positivity),
      mul_div_cancel_right₀ _ hδ.ne']
    ring
  have hneg : u₀ * (2 * √(log K) - d * log K) ≤ 0 := by
    have hsq : log K = √(log K) * √(log K) := (mul_self_sqrt hlog₀.le).symm
    have : 0 ≤ √(log K) := sqrt_nonneg _
    have hu₀ : 0 < u₀ := by positivity
    refine mul_nonpos_of_nonneg_of_nonpos hu₀.le ?_
    nlinarith [mul_nonneg (sub_nonneg.2 hs) this]
  rw [hlhs, hrhs] at hmono
  nlinarith

/-- Struwe's shape with value `c` at `K δ` takes at `δ` a value at least `c - d (K - 1) δ` when
`exp (4 / d²) ≤ K`. -/
theorem sub_le_struweShape {d : ℝ} (hd : 0 < d) (hδ : 0 < δ) (hK : exp (4 / d ^ 2) ≤ K)
    (c : ℝ) : c - d * (K - 1) * δ ≤ struweShape δ K c δ := by
  have h := integral_one_div_sqrt_log_div_le hd hδ hK
  rw [struweShape_def, intervalIntegral.integral_symm]
  linarith

/-- **Struwe's solutions as `i`-convex shapes.** Let `0 < d`, `0 < δ`, `exp (4 / d²) ≤ K` and
`4 K δ ≤ (log K) ^ (-3 / 2)`. Struwe's shape with value `1 + d K δ` at `K δ` is an `i`-convex
shape at every point of `(δ, K δ]`, has slope at most `d` at `K δ`, takes at `δ` a value at least
`1 + d δ` and less than `1 + d K δ`, and its slope tends to `+∞` at `δ`. -/
theorem isConvexShapeAt_struweShape {d : ℝ} (hd : 0 < d) (hδ : 0 < δ)
    (hK : exp (4 / d ^ 2) ≤ K) (hKδ : 4 * K * δ ≤ log K ^ (-3 / 2 : ℝ)) :
    (∀ r ∈ Ioc δ (K * δ), IsConvexShapeAt (struweShape δ K (1 + d * K * δ)) r) ∧
      deriv (struweShape δ K (1 + d * K * δ)) (K * δ) ≤ d ∧
      (1 + d * δ ≤ struweShape δ K (1 + d * K * δ) δ ∧
        struweShape δ K (1 + d * K * δ) δ < 1 + d * K * δ) ∧
      Tendsto (deriv (struweShape δ K (1 + d * K * δ))) (𝓝[>] δ) atTop := by
  set χ := struweShape δ K (1 + d * K * δ)
  set f : ℝ → ℝ := fun u ↦ 1 / √(log (u / δ)) with hf
  obtain ⟨hK₁', hlog₀, hds⟩ := struwe_log_bounds hd hK
  have hK₀ : 0 < K := one_pos.trans hK₁'
  have hK₁ := hK₁'.le
  have hδK : δ < K * δ := lt_mul_of_one_lt_left hδ hK₁'
  set s := √(log K) with hs_def
  have hs₀ : 0 < s := sqrt_pos.2 hlog₀
  have hss : s ^ 2 = log K := sq_sqrt hlog₀.le
  -- `4 K δ s³ ≤ 1`.
  have hA : 4 * K * δ * s ^ 3 ≤ 1 := by
    have e : log K ^ (-3 / 2 : ℝ) = (s ^ 3)⁻¹ := by
      rw [show (-3 / 2 : ℝ) = -(3 / 2) by norm_num, rpow_neg hlog₀.le, hs_def, sqrt_eq_rpow,
        ← rpow_natCast, ← rpow_mul hlog₀.le]
      norm_num
    rw [e] at hKδ
    have := mul_le_mul_of_nonneg_right hKδ (by positivity : (0 : ℝ) ≤ s ^ 3)
    rwa [inv_mul_cancel₀ (by positivity)] at this
  -- The value at `δ`.
  have hfi := intervalIntegrable_struwe hδ hδK.le
  have hχδ : χ δ = 1 + d * K * δ - ∫ u in δ..K * δ, f u := by
    simp only [χ, struweShape_def, hf]
    rw [integral_symm]
    ring
  have hpos : 0 < ∫ u in δ..K * δ, f u :=
    intervalIntegral_pos_of_pos_on hfi (fun u hu ↦
      one_div_pos.2 (sqrt_pos.2 (log_pos ((one_lt_div hδ).2 hu.1)))) hδK
  have hval : 1 + d * δ ≤ χ δ := by
    have := sub_le_struweShape hd hδ hK (1 + d * K * δ)
    linarith
  have hKδ' : K * δ / δ = K := mul_div_cancel_right₀ K hδ.ne'
  -- `K δ s ≤ 1 + d δ`.
  have hB : K * δ * s ≤ 1 + d * δ := by
    -- `2 δ s ≤ d δ s²`, from `2 ≤ d s`.
    have hdδ : 2 * δ * s ≤ d * δ * s ^ 2 := by
      have := mul_le_mul_of_nonneg_left hds (by positivity : (0 : ℝ) ≤ δ * s)
      nlinarith
    rcases le_total (1 / 4) (s ^ 2) with h | h
    · nlinarith
    · -- `K (1 - log K) ≤ 1`, so `K ≤ 4 / 3` and `K s² ≤ 1 / 3`.
      have he := add_one_le_exp (-log K)
      rw [exp_neg, exp_log hK₀] at he
      have hK3 := mul_le_mul_of_nonneg_left he hK₀.le
      rw [mul_inv_cancel₀ hK₀.ne'] at hK3
      have hK43 : K ≤ 4 / 3 := by nlinarith
      have hKs : K * s ^ 2 ≤ 1 / 3 := by
        nlinarith [mul_le_mul hK43 h (sq_nonneg s) (by norm_num : (0 : ℝ) ≤ 4 / 3)]
      have : K * δ * s ^ 3 ≤ 1 / 3 * δ * s := by
        have := mul_le_mul_of_nonneg_right hKs (by positivity : (0 : ℝ) ≤ δ * s)
        linear_combination this
      nlinarith
  refine ⟨fun r hr ↦ isConvexShapeAt_struweShape_of_le_of_mem_Ioc hδ hK₁ hval ?_ ?_ hr, ?_,
    ⟨hval, by linarith⟩, tendsto_deriv_struweShape hδ hK₁ _⟩
  · rwa [hKδ']
  · rw [hKδ']
    nlinarith [mul_pos hd hδ]
  · rw [deriv_struweShape_mul hδ hK₁' _, div_le_iff₀ hs₀]
    linarith

end Struwe

/-- The second derivative of the linear shape `r ↦ ℓ + d r` is `0`. -/
theorem iteratedDeriv_two_linear (ℓ d r : ℝ) : iteratedDeriv 2 (fun r ↦ ℓ + d * r) r = 0 := by
  simpa [smul_eq_mul, mul_comm] using congrFun (iteratedDeriv_two_const_add_smul (𝕜 := ℝ) ℓ d) r

/-- The second derivative of the quadratic shape `r ↦ ℓ + b r + c r² / (2 ℓ)` is `c / ℓ`. -/
theorem iteratedDeriv_two_quadratic (ℓ b c r : ℝ) :
    iteratedDeriv 2 (fun r ↦ ℓ + b * r + c * r ^ 2 / (2 * ℓ)) r = c / ℓ := by
  have e : (fun r ↦ ℓ + b * r + c * r ^ 2 / (2 * ℓ)) =
      fun r ↦ ℓ + b * r + c / (2 * ℓ) * r ^ 2 := by
    ext r
    ring
  simp only [e, iteratedDeriv_succ, iteratedDeriv_zero, deriv_deriv_quadratic]
  ring

/-- **The shape `√(a r² - c)`.** For `1 < a`, `0 < r` and `c < a r²`, `r ↦ √(a r² - c)` is an
`i`-convex shape at `r`. -/
theorem isConvexShapeAt_sqrt_sub {a c r : ℝ} (ha : 1 < a) (hr : 0 < r) (hc : c < a * r ^ 2) :
    IsConvexShapeAt (fun r ↦ √(a * r ^ 2 - c)) r := by
  have hQ : 0 < a * r ^ 2 - c := by linarith
  have h₁ := deriv_sqrt_sub hQ.ne'
  have h₂ := iteratedDeriv_two_sqrt_sub hQ
  set S := √(a * r ^ 2 - c)
  have hS : 0 < S := sqrt_pos.2 hQ
  have hSS : S ^ 2 = a * r ^ 2 - c := sq_sqrt hQ.le
  refine isConvexShapeAt_iff.2 ⟨hr, hS, ?_, ?_⟩
  · rw [h₁, show a * r / S / r = a / S by field_simp]
    exact div_lt_div_of_pos_right ha hS
  · rw [h₁, h₂]
    have e' : -a * c / S ^ 3 + (a * r / S) ^ 3 / r = (a ^ 3 * r ^ 2 - a * c) / S ^ 3 := by
      field_simp
      ring
    rw [e', div_lt_div_iff₀ hS (by positivity), show S ^ 3 = S * S ^ 2 by ring, hSS]
    -- `(a - 1) c < (a - 1) a r² < (a³ - a) r²`.
    have h₃ : (a - 1) * c < (a - 1) * (a * r ^ 2) := mul_lt_mul_of_pos_left hc (by linarith)
    have h₄ : 0 < (a - 1) * a * a * r ^ 2 := by
      have : 0 < a - 1 := by linarith
      have : 0 < a := by linarith
      positivity
    have : a * r ^ 2 - c < a ^ 3 * r ^ 2 - a * c := by nlinarith
    nlinarith

/-- **The shape `√(ℓ² + a r²)`.** For `1 < a` and any `ℓ`, `r ↦ √(ℓ² + a r²)` is an `i`-convex
shape at every `r > 0`. -/
theorem isConvexShapeAt_sqrt {a ℓ r : ℝ} (ha : 1 < a) (hr : 0 < r) :
    IsConvexShapeAt (fun r ↦ √(ℓ ^ 2 + a * r ^ 2)) r := by
  have e : (fun r ↦ √(ℓ ^ 2 + a * r ^ 2)) = fun r ↦ √(a * r ^ 2 - -ℓ ^ 2) := by
    ext r
    ring_nf
  rw [e]
  exact isConvexShapeAt_sqrt_sub ha hr (by nlinarith [sq_nonneg ℓ])

/-- **The shape `ℓ + b r + c r² / (2 ℓ)`.** For `0 < ℓ`, `0 ≤ b` and `1 < c`,
`r ↦ ℓ + b r + c r² / (2 ℓ)` is an `i`-convex shape at every `r > 0`. -/
theorem isConvexShapeAt_quadratic {ℓ b c r : ℝ} (hℓ : 0 < ℓ) (hb : 0 ≤ b) (hc : 1 < c)
    (hr : 0 < r) : IsConvexShapeAt (fun r ↦ ℓ + b * r + c * r ^ 2 / (2 * ℓ)) r := by
  have e : (fun r ↦ ℓ + b * r + c * r ^ 2 / (2 * ℓ)) =
      fun r ↦ ℓ + b * r + c / (2 * ℓ) * r ^ 2 := by
    ext r
    ring
  have h₁ : deriv (fun r ↦ ℓ + b * r + c / (2 * ℓ) * r ^ 2) r = b + c * r / ℓ := by
    rw [(hasDerivAt_quadratic _ _ _ r).deriv]
    field_simp
  have h₂ : iteratedDeriv 2 (fun r ↦ ℓ + b * r + c / (2 * ℓ) * r ^ 2) r = c / ℓ := by
    rw [← e, iteratedDeriv_two_quadratic]
  have hχ : ℓ < ℓ + b * r + c / (2 * ℓ) * r ^ 2 := by
    have : 0 < c / (2 * ℓ) * r ^ 2 := by positivity
    nlinarith
  have hinv : 1 / (ℓ + b * r + c / (2 * ℓ) * r ^ 2) < c / ℓ :=
    (one_div_lt_one_div_of_lt hℓ hχ).trans (div_lt_div_of_pos_right hc hℓ)
  rw [e]
  refine isConvexShapeAt_iff.2 ⟨hr, hℓ.trans hχ, ?_, ?_⟩
  · rw [h₁, add_div, mul_div_right_comm, mul_div_assoc, div_self hr.ne', mul_one]
    have : 0 ≤ b / r := by positivity
    linarith
  · rw [h₁, h₂]
    have : 0 < (b + c * r / ℓ) ^ 3 / r := by positivity
    linarith

/-- **The linear shape `ℓ + d r`.** For `0 < ℓ` and `0 < d`, `r ↦ ℓ + d r` is an `i`-convex shape
at every `r ∈ (0, ℓ d³)`. -/
theorem isConvexShapeAt_linear {ℓ d r : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hr : r ∈ Ioo 0 (ℓ * d ^ 3)) :
    IsConvexShapeAt (fun r ↦ ℓ + d * r) r := by
  obtain ⟨hr₀, hr₁⟩ := hr
  have h₁ : deriv (fun r ↦ ℓ + d * r) r = d := by simp
  have h₂ : iteratedDeriv 2 (fun r ↦ ℓ + d * r) r = 0 := iteratedDeriv_two_linear ℓ d r
  have hχ : 0 < ℓ + d * r := by positivity
  refine isConvexShapeAt_iff.2 ⟨hr₀, hχ, ?_, ?_⟩
  · -- `r (1 - d²) < ℓ d`: for `d ≤ 1` this follows from `r < ℓ d³ ≤ ℓ d`.
    rw [h₁, div_lt_div_iff₀ hχ hr₀]
    rcases le_total 1 d with h | h
    · nlinarith
    · have : d ^ 3 ≤ d := by nlinarith [pow_le_one₀ hd.le h (n := 2)]
      have : ℓ * d ^ 3 ≤ ℓ * d := mul_le_mul_of_nonneg_left this hℓ.le
      nlinarith [mul_pos hd hr₀]
  · rw [h₁, h₂, zero_add, div_lt_div_iff₀ hχ hr₀]
    nlinarith [pow_pos hd 4]

/-! ### Crossings of the special shapes

Where the shapes `√(ℓ² + a r²)`, `ℓ + b r + c r² / (2 ℓ)` and `ℓ + d r` meet on `(0, ∞)`, and
which one is above on each side. Each comparison comes down to the sign of a polynomial in `r`:
the difference of the two shapes, or of their squares. -/

/-- **The square-root shape below the linear one.** For `0 ≤ ℓ` and `d² < a`, at `r > 0`,
`√(ℓ² + a r²) < ℓ + d r` exactly when `r < 2 ℓ d / (a - d²)`. -/
theorem sqrt_lt_linear_iff {ℓ a d r : ℝ} (hℓ : 0 ≤ ℓ) (hda : d ^ 2 < a)
    (hr : 0 < r) : √(ℓ ^ 2 + a * r ^ 2) < ℓ + d * r ↔ r < 2 * ℓ * d / (a - d ^ 2) := by
  have ha : 0 < a := (sq_nonneg d).trans_lt hda
  rw [lt_div_iff₀ (sub_pos.2 hda)]
  rcases le_or_gt 0 d with hd | hd
  · rw [sqrt_lt (by positivity) (by positivity)]
    constructor <;> intro h <;> nlinarith
  · -- For `d < 0` both sides fail: `ℓ + d r < ℓ ≤ √(ℓ² + a r²)` and `2 ℓ d ≤ 0`.
    have : ℓ ≤ √(ℓ ^ 2 + a * r ^ 2) := le_sqrt_of_sq_le (by nlinarith)
    constructor <;> intro h <;> nlinarith

/-- **The linear shape below the square-root one.** For `0 ≤ ℓ` and `d² < a`, at `r > 0`,
`ℓ + d r < √(ℓ² + a r²)` exactly when `2 ℓ d / (a - d²) < r`. -/
theorem linear_lt_sqrt_iff {ℓ a d r : ℝ} (hℓ : 0 ≤ ℓ) (hda : d ^ 2 < a)
    (hr : 0 < r) : ℓ + d * r < √(ℓ ^ 2 + a * r ^ 2) ↔ 2 * ℓ * d / (a - d ^ 2) < r := by
  rw [div_lt_iff₀ (sub_pos.2 hda)]
  rcases le_or_gt 0 d with hd | hd
  · rw [lt_sqrt (by positivity)]
    constructor <;> intro h <;> nlinarith
  · -- For `d < 0` both sides hold: `ℓ + d r < ℓ ≤ √(ℓ² + a r²)` and `2 ℓ d ≤ 0`.
    have : ℓ ≤ √(ℓ ^ 2 + a * r ^ 2) := le_sqrt_of_sq_le (by nlinarith)
    exact ⟨fun _ ↦ by nlinarith, fun _ ↦ by nlinarith⟩

/-- **The crossing of the square-root and linear shapes** (Cieliebak–Eliashberg, Lemma 4.18).
For `0 ≤ ℓ` and `d² < a`, the only `r > 0` where `√(ℓ² + a r²) = ℓ + d r` is
`r = 2 ℓ d / (a - d²)`. -/
theorem sqrt_eq_linear_iff {ℓ a d r : ℝ} (hℓ : 0 ≤ ℓ) (hda : d ^ 2 < a)
    (hr : 0 < r) : √(ℓ ^ 2 + a * r ^ 2) = ℓ + d * r ↔ r = 2 * ℓ * d / (a - d ^ 2) :=
  eq_iff_eq_of_lt_iff_lt_of_gt_iff_gt (sqrt_lt_linear_iff hℓ hda hr)
    (linear_lt_sqrt_iff hℓ hda hr)

/-- **The quadratic shape below the linear one.** For `0 < ℓ` and `0 < c`, at `r > 0`,
`ℓ + b r + c r² / (2 ℓ) < ℓ + d r` exactly when `r < 2 ℓ (d - b) / c`. -/
theorem quadratic_lt_linear_iff {ℓ b c d r : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c) (hr : 0 < r) :
    ℓ + b * r + c * r ^ 2 / (2 * ℓ) < ℓ + d * r ↔ r < 2 * ℓ * (d - b) / c := by
  rw [lt_div_iff₀ hc, ← sub_pos, ← sub_pos (b := r * c)]
  have : ℓ + d * r - (ℓ + b * r + c * r ^ 2 / (2 * ℓ)) =
      r / (2 * ℓ) * (2 * ℓ * (d - b) - r * c) := by
    field_simp
    ring
  rw [this]
  exact mul_pos_iff_of_pos_left (by positivity)

/-- **The linear shape below the quadratic one.** For `0 < ℓ` and `0 < c`, at `r > 0`,
`ℓ + d r < ℓ + b r + c r² / (2 ℓ)` exactly when `2 ℓ (d - b) / c < r`. -/
theorem linear_lt_quadratic_iff {ℓ b c d r : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c) (hr : 0 < r) :
    ℓ + d * r < ℓ + b * r + c * r ^ 2 / (2 * ℓ) ↔ 2 * ℓ * (d - b) / c < r := by
  rw [div_lt_iff₀ hc, ← sub_pos, ← sub_pos (a := r * c)]
  have : ℓ + b * r + c * r ^ 2 / (2 * ℓ) - (ℓ + d * r) =
      r / (2 * ℓ) * (r * c - 2 * ℓ * (d - b)) := by
    field_simp
    ring
  rw [this]
  exact mul_pos_iff_of_pos_left (by positivity)

/-- **The crossing of the quadratic and linear shapes** (Cieliebak–Eliashberg, Lemma 4.18).
For `0 < ℓ` and `0 < c`, the only `r > 0` where `ℓ + b r + c r² / (2 ℓ) = ℓ + d r` is
`r = 2 ℓ (d - b) / c`, which is positive when `b < d`. -/
theorem quadratic_eq_linear_iff {ℓ b c d r : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c) (hr : 0 < r) :
    ℓ + b * r + c * r ^ 2 / (2 * ℓ) = ℓ + d * r ↔ r = 2 * ℓ * (d - b) / c :=
  eq_iff_eq_of_lt_iff_lt_of_gt_iff_gt (quadratic_lt_linear_iff hℓ hc hr)
    (linear_lt_quadratic_iff hℓ hc hr)

/-- **The crossings of the quadratic and square-root shapes** (Cieliebak–Eliashberg,
Lemma 4.18). Let `0 < ℓ`, `0 < b` and `0 < c`, and suppose that the quadratic shape
`ℓ + b r + c r² / (2 ℓ)` is below `√(ℓ² + a r²)` at some `r₀ > 0`. Then on `(0, ∞)` the two
meet at exactly two points `r₁ ∈ (0, r₀)` and `r₂ > r₀`: the quadratic shape is below the other
on `(r₁, r₂)` and above it on `(0, r₁)` and on `(r₂, ∞)`. -/
theorem exists_crossings_quadratic_sqrt {ℓ a b c r₀ : ℝ} (hℓ : 0 < ℓ) (hb : 0 < b) (hc : 0 < c)
    (hr₀ : 0 < r₀) (h : ℓ + b * r₀ + c * r₀ ^ 2 / (2 * ℓ) < √(ℓ ^ 2 + a * r₀ ^ 2)) :
    ∃ r₁ ∈ Ioo 0 r₀, ∃ r₂ ∈ Ioi r₀, ∀ r, 0 < r →
      (ℓ + b * r + c * r ^ 2 / (2 * ℓ) < √(ℓ ^ 2 + a * r ^ 2) ↔ r ∈ Ioo r₁ r₂) ∧
      (√(ℓ ^ 2 + a * r ^ 2) < ℓ + b * r + c * r ^ 2 / (2 * ℓ) ↔ r < r₁ ∨ r₂ < r) ∧
      (ℓ + b * r + c * r ^ 2 / (2 * ℓ) = √(ℓ ^ 2 + a * r ^ 2) ↔ r = r₁ ∨ r = r₂) := by
  -- For `r > 0`, the square of the quadratic minus `ℓ² + a r²` is `r p(r)`, `p` a cubic whose
  -- coefficients of `1` and `r³` are positive.
  set p : ℝ → ℝ := fun r ↦
    2 * ℓ * b + (b ^ 2 + c - a) * r + b * c / ℓ * r ^ 2 + c ^ 2 / (4 * ℓ ^ 2) * r ^ 3 with hp
  have hsq : ∀ r, (ℓ + b * r + c * r ^ 2 / (2 * ℓ)) ^ 2 - (ℓ ^ 2 + a * r ^ 2) = r * p r := by
    intro r
    simp only [hp]
    field_simp
    ring
  have hlt : ∀ r, 0 < r → (ℓ + b * r + c * r ^ 2 / (2 * ℓ) < √(ℓ ^ 2 + a * r ^ 2) ↔ p r < 0) :=
    fun r hr ↦ by
      rw [lt_sqrt (by positivity), ← sub_neg, hsq]
      exact ⟨fun h ↦ by nlinarith, fun h ↦ by nlinarith⟩
  have hgt : ∀ r, 0 < r → (√(ℓ ^ 2 + a * r ^ 2) < ℓ + b * r + c * r ^ 2 / (2 * ℓ) ↔ 0 < p r) :=
    fun r hr ↦ by
      rw [sqrt_lt' (by positivity), ← sub_pos, hsq, mul_pos_iff_of_pos_left hr]
  obtain ⟨r₁, hr₁, r₂, hr₂, hsign⟩ := exists_two_roots_cubic_of_neg (by positivity : 0 < 2 * ℓ * b)
    (by positivity) hr₀ ((hlt r₀ hr₀).1 h)
  refine ⟨r₁, hr₁, r₂, hr₂, fun r hr ↦ ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ := hsign r hr
  exact ⟨(hlt r hr).trans h₁, (hgt r hr).trans h₂,
    (eq_iff_eq_of_lt_iff_lt_of_gt_iff_gt (hlt r hr) (hgt r hr)).trans h₃⟩

/-! ### From the linear to the square-root shape

Cieliebak and Eliashberg's Lemma 4.19 and Remark 4.20: a smooth `i`-convex shape that is linear
near `0` and equal to `√(1 + a r²)` beyond a given `γ`. The linear shape gives way to a quadratic
one where the two cross, and the quadratic shape to the square-root one where those cross, each
time by `exists_isConvexShapeAt_eqOn_Iic_Ici`. -/

/-- The slope of the linear shape in
`exists_isConvexShapeAt_eq_linear_eq_sqrt_of_quadratic_lt`: some `d ∈ (b, 1)` so close to `b`
that twice the crossing `x = 2 ℓ (d - b) / c` of the linear and quadratic shapes is below `ℓ d³`,
where the linear shape stops being convex, and at most a given `r₁ > 0`. -/
private theorem exists_slope_linear {ℓ b c r₁ : ℝ} (hℓ : 0 < ℓ) (hb : 0 < b) (hb₁ : b < 1)
    (hc : 0 < c) (hr₁ : 0 < r₁) :
    ∃ d ∈ Ioo b 1, 2 * (2 * ℓ * (d - b) / c) < ℓ * d ^ 3 ∧ 2 * (2 * ℓ * (d - b) / c) ≤ r₁ := by
  set ρ := min (ℓ * b ^ 3) r₁
  set ε := min (c * ρ / (4 * ℓ)) ((1 - b) / 2)
  have hε₀ : 0 < ε := lt_min (by positivity) (by linarith)
  have hd₁ : b + ε < 1 := by linarith [min_le_right (c * ρ / (4 * ℓ)) ((1 - b) / 2)]
  have hx : 2 * (2 * ℓ * (b + ε - b) / c) ≤ ρ := by
    rw [show b + ε - b = ε by ring, ← mul_div_assoc, div_le_iff₀ hc]
    have : ε ≤ c * ρ / (4 * ℓ) := min_le_left _ _
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith
  refine ⟨b + ε, ⟨by linarith, hd₁⟩, hx.trans_lt ((min_le_left _ _).trans_lt ?_),
    hx.trans (min_le_right _ _)⟩
  exact mul_lt_mul_of_pos_left (pow_lt_pow_left₀ (by linarith) hb.le (by norm_num)) hℓ

/-- **From a linear to a square-root shape, through a quadratic one.** Let `0 < ℓ`, `1 < a`,
`0 < b < 1` and `1 < c`, and suppose that the quadratic shape `ℓ + b r + c r² / (2 ℓ)` is below
`√(ℓ² + a r²)` at some `r₀ > 0`. Then there are a slope `d ∈ (b, 1)`, some `β ∈ (0, r₀)` and a
smooth `ψ`, an `i`-convex shape at every `r > 0`, with `ψ r = √(ℓ² + a r²)` for `r ≥ r₀` and
`ψ r = ℓ + d r` for `r ≤ β`, and `ψ` is convex: its second derivative is nonnegative. -/
theorem exists_isConvexShapeAt_eq_linear_eq_sqrt_of_quadratic_lt {ℓ a b c r₀ : ℝ}
    (hℓ : 0 < ℓ) (ha : 1 < a) (hb : 0 < b) (hb₁ : b < 1) (hc : 1 < c) (hr₀ : 0 < r₀)
    (h : ℓ + b * r₀ + c * r₀ ^ 2 / (2 * ℓ) < √(ℓ ^ 2 + a * r₀ ^ 2)) :
    ∃ d ∈ Ioo b 1, ∃ β ∈ Ioo 0 r₀, ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧
      (∀ r, 0 < r → IsConvexShapeAt ψ r) ∧ (∀ r, r₀ ≤ r → ψ r = √(ℓ ^ 2 + a * r ^ 2)) ∧
      (∀ r ≤ β, ψ r = ℓ + d * r) ∧ ∀ r, 0 ≤ iteratedDeriv 2 ψ r := by
  have hc₀ : 0 < c := by linarith
  obtain ⟨r₁, ⟨hr₁₀, hr₁r₀⟩, r₂, hr₂, hQS⟩ := exists_crossings_quadratic_sqrt hℓ hb hc₀ hr₀ h
  have hr₂ : r₀ < r₂ := hr₂
  obtain ⟨d, ⟨hbd, hd₁⟩, hxd, hxr₁⟩ := exists_slope_linear hℓ hb hb₁ hc₀ hr₁₀
  set x := 2 * ℓ * (d - b) / c with hx
  have hx₀ : 0 < x := by rw [hx]; have := sub_pos.2 hbd; positivity
  set L : ℝ → ℝ := fun r ↦ ℓ + d * r
  set Q : ℝ → ℝ := fun r ↦ ℓ + b * r + c * r ^ 2 / (2 * ℓ)
  set S : ℝ → ℝ := fun r ↦ √(ℓ ^ 2 + a * r ^ 2)
  have hLs : ContDiff ℝ ∞ L := by fun_prop
  have hQs : ContDiff ℝ ∞ Q := by fun_prop
  have hSs : ContDiff ℝ ∞ S :=
    ContDiff.sqrt (by fun_prop) fun r ↦ (by positivity : 0 < ℓ ^ 2 + a * r ^ 2).ne'
  have hLc : ∀ r ∈ Ioo 0 (2 * x), IsConvexShapeAt L r := fun r hr ↦
    isConvexShapeAt_linear hℓ (hb.trans hbd) ⟨hr.1, hr.2.trans hxd⟩
  have hQc : ∀ r, 0 < r → IsConvexShapeAt Q r := fun r hr ↦
    isConvexShapeAt_quadratic hℓ hb.le hc hr
  have hSc : ∀ r, 0 < r → IsConvexShapeAt S r := fun r hr ↦ isConvexShapeAt_sqrt ha hr
  -- The three shapes are convex, and so are the functions that join them.
  have hL₂ (r : ℝ) : 0 ≤ iteratedDeriv 2 L r := (iteratedDeriv_two_linear ℓ d r).ge
  have hQ₂ (r : ℝ) : 0 ≤ iteratedDeriv 2 Q r := by
    rw [iteratedDeriv_two_quadratic]
    positivity
  have hS₂ (r : ℝ) : 0 ≤ iteratedDeriv 2 S r := by
    rw [iteratedDeriv_two_sqrt_quadratic (by positivity)]
    exact div_nonneg (by nlinarith [sq_nonneg ℓ]) (by positivity)
  -- From the linear to the quadratic shape, across `x`, on `[x / 4, 3 x / 2]`.
  obtain ⟨φ, hφs, hφc, hφL, hφQ, hφ₁, hφ₂, hφcv⟩ := exists_isConvexShapeAt_eqOn_Iic_Ici
    (r₁ := x / 4) (u := x / 2) (v := 5 * x / 4) (r₂ := 3 * x / 2) le_top hLs hQs (by linarith)
    (by linarith) (by linarith) (fun r hr ↦ hLc r ⟨by linarith [hr.1], by linarith [hr.2]⟩)
    (fun r hr ↦ hQc r (by linarith [hr.1]))
    (fun r hr ↦ ((quadratic_lt_linear_iff hℓ hc₀ (by linarith [hr.1])).2
      (by linarith [hr.2])).le)
    (fun r hr ↦ ((linear_lt_quadratic_iff hℓ hc₀ (by linarith [hr.1])).2
      (by linarith [hr.1])).le)
    (fun r hr he ↦ by
      have := (quadratic_eq_linear_iff hℓ hc₀ (by linarith [hr.1]) (b := b) (d := d)).1 he.symm
      exact ⟨by linarith, by linarith⟩)
  have hφc' : ∀ r, 0 < r → IsConvexShapeAt φ r := fun r hr ↦ by
    rcases lt_or_ge r (x / 4) with h₁ | h₁
    · exact hφ₁ r (by linarith) (hLc r ⟨hr, by linarith⟩)
    rcases le_or_gt r (3 * x / 2) with h₂ | h₂
    · exact hφc r ⟨h₁, h₂⟩
    · exact hφ₂ r (by linarith) (hQc r hr)
  -- From the quadratic to the square-root shape, across `r₁`, on `[5 x / 4, r₀]`.
  obtain ⟨ψ, hψs, hψc, hψφ, hψS, hψ₁, hψ₂, hψcv⟩ := exists_isConvexShapeAt_eqOn_Iic_Ici
    (r₁ := 5 * x / 4) (u := (3 * x / 2 + r₁) / 2) (v := (r₁ + r₀) / 2) (r₂ := r₀) le_top hφs hSs
    (by linarith) (by linarith) (by linarith) (fun r hr ↦ hφc' r (by linarith [hr.1]))
    (fun r hr ↦ hSc r (by linarith [hr.1]))
    (fun r hr ↦ by
      rw [hφQ (show 5 * x / 4 ≤ r from hr.1)]
      exact ((hQS r (by linarith [hr.1])).2.1.2 (Or.inl (by linarith [hr.2]))).le)
    (fun r hr ↦ by
      rw [hφQ (show 5 * x / 4 ≤ r by linarith [hr.1])]
      exact ((hQS r (by linarith [hr.1])).1.2 ⟨by linarith [hr.1], by linarith [hr.2]⟩).le)
    (fun r hr he ↦ by
      rw [hφQ (show 5 * x / 4 ≤ r from hr.1)] at he
      rcases (hQS r (by linarith [hr.1])).2.2.1 he with rfl | rfl
      · exact ⟨by linarith, by linarith⟩
      · linarith [hr.2])
  refine ⟨d, ⟨hbd, hd₁⟩, x / 2, ⟨by positivity, by linarith⟩, ψ, hψs, fun r hr ↦ ?_,
    fun r hr ↦ hψS (show (r₁ + r₀) / 2 ≤ r by linarith),
    fun r hr ↦ (hψφ (show r ≤ (3 * x / 2 + r₁) / 2 by linarith)).trans (hφL hr),
    fun r ↦ hψcv r (hφcv r (hL₂ r) (hQ₂ r)) (hS₂ r)⟩
  rcases lt_or_ge r ((3 * x / 2 + r₁) / 2) with h₁ | h₁
  · exact hψ₁ r h₁ (hφc' r hr)
  rcases le_or_gt r r₀ with h₂ | h₂
  · exact hψc r ⟨by linarith, h₂⟩
  · exact hψ₂ r (by linarith) (hSc r hr)

/-- **Admissible constants for the quadratic shape** (Cieliebak–Eliashberg, Remark 4.20). For
`0 < γ` and `γ (a + 1)² ≤ a - 1`, which force `1 < a`, the quadratic shape with `ℓ = 1`,
`b = γ (a - 1) / 16` and `c = (1 + a) / 2` is below `√(1 + a r²)` at `r = γ`. -/
theorem quadratic_lt_sqrt_of_mul_sq_le {a γ : ℝ} (hγ : 0 < γ) (h : γ * (a + 1) ^ 2 ≤ a - 1) :
    1 + γ * (a - 1) / 16 * γ + (1 + a) / 2 * γ ^ 2 / 2 < √(1 + a * γ ^ 2) := by
  have ha : 1 < a := by nlinarith [sq_nonneg (a - 1), mul_pos hγ hγ]
  rw [lt_sqrt (by positivity), ← sub_neg]
  have e : (1 + γ * (a - 1) / 16 * γ + (1 + a) / 2 * γ ^ 2 / 2) ^ 2 - (1 + a * γ ^ 2) =
      γ ^ 2 * (γ ^ 2 * ((a - 1) ^ 2 / 256 + (a + 1) * (3 * a + 1) / 32) - 3 * (a - 1) / 8) := by
    ring
  rw [e]
  refine mul_neg_of_pos_of_neg (by positivity) (sub_neg.2 ?_)
  have hγ₁ : γ < 1 := by nlinarith
  have h₁ : γ ^ 2 * (a + 1) ^ 2 ≤ γ * (a - 1) := by nlinarith [mul_le_mul_of_nonneg_left h hγ.le]
  have h₂ : (a - 1) ^ 2 / 256 + (a + 1) * (3 * a + 1) / 32 < (a + 1) ^ 2 / 8 := by nlinarith
  calc γ ^ 2 * ((a - 1) ^ 2 / 256 + (a + 1) * (3 * a + 1) / 32)
      ≤ γ ^ 2 * ((a + 1) ^ 2 / 8) := by gcongr
    _ ≤ γ * (a - 1) / 8 := by linarith
    _ < 3 * (a - 1) / 8 := by nlinarith

/-- The hypothesis `γ (a + 1)² ≤ a - 1` of `quadratic_lt_sqrt_of_mul_sq_le` cannot be dropped:
for `a = 100` and `γ = 1 / 2`, Remark 4.20's quadratic shape is above `√(1 + a γ²)` at `γ`. -/
example : ¬ ((1 : ℝ) + 1 / 2 * (100 - 1) / 16 * (1 / 2) + (1 + 100) / 2 * (1 / 2) ^ 2 / 2 <
    √(1 + 100 * (1 / 2) ^ 2)) := by
  rw [not_lt, Real.sqrt_le_left (by norm_num)]
  norm_num

/-- **From a linear to a square-root shape** (Cieliebak–Eliashberg, Lemma 4.19). For `1 < a` and
`0 < γ` there are `d ∈ (0, 1)`, `β ∈ (0, γ)` and a smooth `ψ`, an `i`-convex shape at every
`r > 0`, with `ψ r = √(1 + a r²)` for `r ≥ γ` and `ψ r = 1 + d r` for `r ≤ β`. Every tangent
of `ψ` at a point `r ≥ 0` meets the vertical axis above `0`: `r ψ' r < ψ r`. -/
theorem exists_isConvexShapeAt_eq_linear_eq_sqrt {a γ : ℝ} (ha : 1 < a) (hγ : 0 < γ) :
    ∃ d ∈ Ioo 0 1, ∃ β ∈ Ioo 0 γ, ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧
      (∀ r, 0 < r → IsConvexShapeAt ψ r) ∧ (∀ r, γ ≤ r → ψ r = √(1 + a * r ^ 2)) ∧
      (∀ r ≤ β, ψ r = 1 + d * r) ∧ ∀ r, 0 ≤ r → r * deriv ψ r < ψ r := by
  set γ' := min γ ((a - 1) / (a + 1) ^ 2)
  have hγ'₀ : 0 < γ' := lt_min hγ (div_pos (by linarith) (by positivity))
  have h : γ' * (a + 1) ^ 2 ≤ a - 1 := (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
  have hb : γ' * (a - 1) / 16 < 1 := by nlinarith [mul_le_mul_of_nonneg_left h hγ'₀.le]
  obtain ⟨d, hd, β, hβ, ψ, hψs, hψc, hψS, hψL, hψ₂⟩ :=
    exists_isConvexShapeAt_eq_linear_eq_sqrt_of_quadratic_lt (ℓ := 1) (b := γ' * (a - 1) / 16)
      (c := (1 + a) / 2) one_pos ha (by have := sub_pos.2 ha; positivity) hb (by linarith) hγ'₀
      (by simpa using quadratic_lt_sqrt_of_mul_sq_le hγ'₀ h)
  have hγγ' : γ' ≤ γ := min_le_left _ _
  have hψS' (r : ℝ) (hr : γ ≤ r) : ψ r = √(1 + a * r ^ 2) := by simpa using hψS r (hγγ'.trans hr)
  refine ⟨d, ⟨lt_trans (by have := sub_pos.2 ha; positivity) hd.1, hd.2⟩, β,
    ⟨hβ.1, hβ.2.trans_le hγγ'⟩, ψ, hψs, hψc, hψS', hψL, fun r hr₀ ↦ ?_⟩
  -- Since `ψ` is convex, `r ↦ ψ r - r ψ' r`, whose derivative is `-r ψ'' r`, is antitone
  -- on `[0, ∞)`.
  have hψ' : Differentiable ℝ (deriv ψ) := by
    simpa using hψs.differentiable_iteratedDeriv 1 (by simp)
  have hanti : AntitoneOn (fun r ↦ ψ r - r * deriv ψ r) (Ici 0) := by
    have hg (r : ℝ) : HasDerivAt (fun r ↦ ψ r - r * deriv ψ r)
        (-(r * iteratedDeriv 2 ψ r)) r := by
      have h := ((hψs.differentiable (by simp)) r).hasDerivAt.fun_sub
        ((hasDerivAt_id' r).fun_mul (hψ' r).hasDerivAt)
      convert h using 1
      simp only [iteratedDeriv_succ, iteratedDeriv_zero]
      ring
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) (HasDerivAt.continuousOn fun r _ ↦ hg r)
      (fun r _ ↦ (hg r).differentiableAt.differentiableWithinAt) fun r hr ↦ ?_
    rw [interior_Ici, mem_Ioi] at hr
    rw [(hg r).deriv]
    nlinarith [hψ₂ r]
  -- Beyond `γ`, `ψ - r ψ'` is `1 / √(1 + a r²) > 0`.
  set t := max r γ + 1
  have hrt : r ≤ t := by linarith [le_max_left r γ]
  have ht : γ < t := by linarith [le_max_right r γ]
  have hQ : 0 < a * t ^ 2 - -1 := by nlinarith
  have hS : ψ =ᶠ[𝓝 t] fun r ↦ √(a * r ^ 2 - -1) := by
    filter_upwards [lt_mem_nhds ht] with r hr
    rw [hψS' r hr.le, sub_neg_eq_add, add_comm]
  have hd : deriv ψ t = a * t / √(a * t ^ 2 - -1) := by
    rw [hS.deriv_eq, deriv_sqrt_sub hQ.ne']
  have hpos : 0 < ψ t - t * deriv ψ t := by
    have hRR := sq_sqrt hQ.le
    rw [hd, hS.eq_of_nhds, sub_pos, mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  linarith [hanti hr₀ (show (0 : ℝ) ≤ t from hr₀.trans hrt) hrt]

/-- **A Struwe shape joined to a line.** Let `0 < d`, `0 < δ`, `exp (4 / d²) ≤ K`, `4 < K`, and
let `ℓ` be at least `2 K δ √(log (2 K))` and `4 K δ √(log (2 K))³`, with `2 K δ < ℓ d³`. Then
there is a function, smooth on `(δ, ∞)` and an `i`-convex shape at every point of `(δ, 2 K δ]`,
that is Struwe's shape with value `ℓ + d K δ` at `K δ` up to `3 K δ / 4` and the line `ℓ + d r`
from `3 K δ / 2` on. -/
theorem exists_isConvexShapeAt_eq_struweShape_eq_linear {δ K d ℓ : ℝ} (hd : 0 < d) (hδ : 0 < δ)
    (hK : exp (4 / d ^ 2) ≤ K) (hK₄ : 4 < K) (hℓ₁ : 2 * K * δ * √(log (2 * K)) ≤ ℓ)
    (hℓ₂ : 4 * K * δ * √(log (2 * K)) ^ 3 ≤ ℓ) (hℓd : 2 * K * δ < ℓ * d ^ 3) :
    ∃ G : ℝ → ℝ, ContDiffOn ℝ ∞ G (Ioi δ) ∧ (∀ r ∈ Ioc δ (2 * K * δ), IsConvexShapeAt G r) ∧
      (∀ r ≤ 3 * K * δ / 4, G r = struweShape δ K (ℓ + d * K * δ) r) ∧
      ∀ r, 3 * K * δ / 2 ≤ r → G r = ℓ + d * r := by
  have hK₁ : 1 < K := by linarith
  have hKδ : 4 * δ < K * δ := by nlinarith
  have hℓ : 0 < ℓ := by
    by_contra h
    nlinarith [pow_pos hd 3]
  set S := struweShape δ K (ℓ + d * K * δ)
  have hlow : ℓ + d * δ ≤ S δ := by
    have := sub_le_struweShape hd hδ hK (ℓ + d * K * δ)
    linarith
  have hSc : ∀ r ∈ Ioc δ (2 * K * δ), IsConvexShapeAt S r := by
    have e : 2 * K * δ / δ = 2 * K := mul_div_cancel_right₀ _ hδ.ne'
    exact fun r hr ↦ isConvexShapeAt_struweShape_of_le_of_mem_Ioc hδ hK₁.le
      (by nlinarith [mul_pos hd hδ] : ℓ ≤ S δ) (by rw [e]; linarith) (by rw [e]; linarith) hr
  -- Extend `S` from near `[K δ / 4, 2 K δ]` to a smooth function on `ℝ`, and join it to the line
  -- on `[K δ / 2, 2 K δ]`, where the two cross only at `K δ`.
  obtain ⟨S', hS's, -, -, -, hS'e⟩ :=
    (contDiffOn_struweShape hδ hK₁.le (ℓ + d * K * δ)).exists_contDiff_eventuallyEq_on_isCompact
      isCompact_Icc isOpen_Ioi fun r (hr : r ∈ Icc (K * δ / 4) (2 * K * δ)) ↦
        (show δ < r by linarith [hr.1])
  have hS'S : ∀ r ∈ Icc (K * δ / 4) (2 * K * δ), S' r = S r := fun r hr ↦ (hS'e r hr).eq_of_nhds
  have hS' : ∀ r ∈ Icc (K * δ / 2) (2 * K * δ), S' r = S r := fun r hr ↦
    hS'S r ⟨by linarith [hr.1], hr.2⟩
  obtain ⟨J, hJs, hJc, hJ₁, hJ₂, -⟩ := exists_isConvexShapeAt_eqOn_Iic_Ici (n := ⊤)
    (χ₂ := fun r ↦ ℓ + d * r) (r₁ := K * δ / 2) (u := 3 * K * δ / 4) (v := 3 * K * δ / 2)
    (r₂ := 2 * K * δ) le_top hS's (by fun_prop) (by linarith) (by linarith) (by linarith)
    (fun r hr ↦ (hSc r ⟨by linarith [hr.1], hr.2⟩).congr_of_eventuallyEq
      (hS'e r ⟨by linarith [hr.1], hr.2⟩))
    (fun r hr ↦ isConvexShapeAt_linear hℓ hd ⟨by linarith [hr.1], by linarith [hr.2]⟩)
    (fun r hr ↦ by
      rw [hS' r ⟨hr.1, by linarith [hr.2]⟩]
      exact (linear_lt_struweShape hδ hK₁ hlow ⟨by linarith [hr.1], by linarith [hr.2]⟩).le)
    (fun r hr ↦ by
      rw [hS' r ⟨by linarith [hr.1], hr.2⟩]
      exact (struweShape_lt_linear hδ hK₁ hlow (by linarith [hr.1])).le)
    (fun r hr hr' ↦ by
      rw [hS' r hr] at hr'
      rcases lt_trichotomy r (K * δ) with h | rfl | h
      · exact absurd hr' (linear_lt_struweShape hδ hK₁ hlow ⟨by linarith [hr.1], h⟩).ne'
      · exact ⟨by linarith, by linarith⟩
      · exact absurd hr' (struweShape_lt_linear hδ hK₁ hlow h).ne)
  -- `G` is `S` up to `3 K δ / 4` and `J` from `K δ / 2` on.
  have hSJ : EqOn S J (Icc (K * δ / 4) (3 * K * δ / 4)) := fun r hr ↦ by
    rw [hJ₁ hr.2, hS'S r ⟨hr.1, by linarith [hr.2]⟩]
  set G : ℝ → ℝ := fun r ↦ if r ≤ K * δ / 2 then S r else J r
  have hGS : ∀ r ≤ 3 * K * δ / 4, G r = S r := fun r hr ↦
    EqOn.eqOn_ite_le_left (s := Iic (3 * K * δ / 4))
      (hSJ.mono fun y hy ↦ mem_Icc.2 ⟨by linarith [mem_Ioi.1 hy.2], hy.1⟩) hr
  have hGS' : ∀ x, x < 3 * K * δ / 4 → G =ᶠ[𝓝 x] S := fun x hx ↦
    (hSJ.mono Ioo_subset_Icc_self).eventuallyEq_ite_le_left (by linarith) hx
  have hGJ : ∀ x, K * δ / 4 < x → G =ᶠ[𝓝 x] J := fun x hx ↦
    (hSJ.mono Ioo_subset_Icc_self).eventuallyEq_ite_le_right (by linarith) hx
  refine ⟨G, fun x (hx : δ < x) ↦ ?_, fun r hr ↦ ?_, hGS, fun r hr ↦ ?_⟩
  · refine ContDiffAt.contDiffWithinAt ?_
    rcases lt_or_ge x (3 * K * δ / 4) with h | h
    · exact ((contDiffOn_struweShape hδ hK₁.le _).contDiffAt
        (Ioi_mem_nhds hx)).congr_of_eventuallyEq (hGS' x h)
    · exact hJs.contDiffAt.congr_of_eventuallyEq (hGJ x (by linarith))
  · rcases lt_or_ge r (3 * K * δ / 4) with h | h
    · exact (hSc r hr).congr_of_eventuallyEq (hGS' r h)
    · exact (hJc r ⟨by linarith, hr.2⟩).congr_of_eventuallyEq (hGJ r (by linarith))
  · rw [(hGJ r (by linarith)).eq_of_nhds, hJ₂ (mem_Ici.2 hr)]

/-- **The surrounding shape** (Cieliebak–Eliashberg, Proposition 4.21, the part about the shape).
For `1 < a` and `0 < γ` there are `δ ∈ (0, γ)` and a function `χ`, smooth on `(δ, ∞)` and
continuous on `[δ, ∞)`, that is an `i`-convex shape at every `r > δ`, equals `√(1 + a r²)` on
`[γ, ∞)`, has slope tending to `+∞` at `δ`, and takes at `δ` a value in `(1, 1 + γ)`. -/
theorem exists_convexShape_surround {a γ : ℝ} (ha : 1 < a) (hγ : 0 < γ) :
    ∃ δ ∈ Ioo 0 γ, ∃ χ : ℝ → ℝ, ContDiffOn ℝ ∞ χ (Ioi δ) ∧ ContinuousOn χ (Ici δ) ∧
      (∀ r, δ < r → IsConvexShapeAt χ r) ∧ (∀ r, γ ≤ r → χ r = √(1 + a * r ^ 2)) ∧
      Tendsto (deriv χ) (𝓝[>] δ) atTop ∧ 1 < χ δ ∧ χ δ < 1 + γ := by
  obtain ⟨d, hd, β, hβ, ψ, hψs, hψc, hψS, hψL, -⟩ :=
    exists_isConvexShapeAt_eq_linear_eq_sqrt ha hγ
  obtain ⟨K, hKd⟩ : ∃ K, K = exp (4 / d ^ 2) := ⟨_, rfl⟩
  have hK₄ : 4 < K := by
    have h4 : 4 ≤ 4 / d ^ 2 := by
      rw [le_div_iff₀ (by have := hd.1; positivity)]
      nlinarith [hd.1, hd.2]
    linarith [add_one_le_exp (4 / d ^ 2)]
  have hK : 1 < K := by linarith
  -- A small `δ`.
  have ev : ∀ c e : ℝ, 0 < e → ∀ᶠ δ in 𝓝[>] (0 : ℝ), c * δ < e := fun c e he ↦
    (((continuous_const_mul c).tendsto' 0 0 (mul_zero c)).mono_left
      nhdsWithin_le_nhds).eventually (gt_mem_nhds he)
  obtain ⟨δ, hδ, hδβ, hδd, hδK, hδ₁, hδ₂⟩ := (eventually_mem_nhdsWithin.and
    ((ev (2 * K) β hβ.1).and ((ev (2 * K) (d ^ 3) (pow_pos hd.1 3)).and
    ((ev (4 * K) (log K ^ (-3 / 2 : ℝ)) (rpow_pos_of_pos (log_pos hK) _)).and
    ((ev (2 * K * √(log (2 * K))) 1 one_pos).and
    (ev (4 * K * √(log (2 * K)) ^ 3) 1 one_pos)))))).exists
  have hδ : 0 < δ := hδ
  have hKδ : 0 < K * δ := by positivity
  set S := struweShape δ K (1 + d * K * δ)
  obtain ⟨-, -, ⟨hlow, hup⟩, htend⟩ := isConvexShapeAt_struweShape hd.1 hδ hKd.ge hδK.le
  obtain ⟨G, hGs, hGc, hGS, hGL⟩ := exists_isConvexShapeAt_eq_struweShape_eq_linear (ℓ := 1)
    hd.1 hδ hKd.ge hK₄ (by linarith) (by linarith) (by linarith)
  -- `χ` is `G` below `β` and `ψ` beyond `3 K δ / 2`.
  have hGψ : EqOn G ψ (Ioo (3 * K * δ / 2) β) := fun r hr ↦ by
    rw [hψL r hr.2.le, hGL r hr.1.le]
  set χ : ℝ → ℝ := fun r ↦ if r ≤ 2 * K * δ then G r else ψ r
  have hχG : ∀ x, x < β → χ =ᶠ[𝓝 x] G := fun x hx ↦
    hGψ.eventuallyEq_ite_le_left (by linarith) hx
  have hχψ : ∀ x, 3 * K * δ / 2 < x → χ =ᶠ[𝓝 x] ψ := fun x hx ↦
    hGψ.eventuallyEq_ite_le_right hδβ hx
  have hχS : ∀ x, x < 3 * K * δ / 4 → χ =ᶠ[𝓝 x] S := fun x hx ↦ by
    filter_upwards [hχG x (by nlinarith), Iio_mem_nhds hx] with y hy (hy' : y < 3 * K * δ / 4)
    rw [hy, hGS y hy'.le]
  have hχs : ContDiffOn ℝ ∞ χ (Ioi δ) := fun x (hx : δ < x) ↦ by
    refine ContDiffAt.contDiffWithinAt ?_
    rcases lt_or_ge x β with h | h
    · exact (hGs.contDiffAt (Ioi_mem_nhds hx)).congr_of_eventuallyEq (hχG x h)
    · exact hψs.contDiffAt.congr_of_eventuallyEq (hχψ x (by linarith))
  have hχδ : χ δ = S δ := (hχS δ (by nlinarith)).eq_of_nhds
  refine ⟨δ, ⟨hδ, by nlinarith [hβ.2]⟩, χ, hχs, fun x (hx : δ ≤ x) ↦ ?_, fun r hr ↦ ?_,
    fun r hr ↦ ?_, htend.congr' ?_, ?_, ?_⟩
  · rcases hx.eq_or_lt with rfl | hx
    · exact (continuousOn_struweShape hδ hK.le _ δ le_rfl).congr_of_eventuallyEq
        (nhdsWithin_le_nhds (hχS δ (by nlinarith))) hχδ
    · exact (hχs.continuousOn.continuousAt (Ioi_mem_nhds hx)).continuousWithinAt
  · rcases le_or_gt r (2 * K * δ) with h | h
    · exact (hGc r ⟨hr, h⟩).congr_of_eventuallyEq (hχG r (by linarith))
    · exact (hψc r (by linarith)).congr_of_eventuallyEq (hχψ r (by linarith))
  · rw [(hχψ r (by linarith [hβ.2])).eq_of_nhds, hψS r hr]
  · filter_upwards [Ioo_mem_nhdsGT (show δ < 3 * K * δ / 4 by nlinarith)] with x hx
    exact (hχS x hx.2).deriv_eq.symm
  · rw [hχδ]
    nlinarith [hd.1]
  · rw [hχδ]
    nlinarith [mul_lt_mul_of_pos_right hd.2 (mul_pos (by linarith) hδ : 0 < K * δ), hβ.2]

end SymplecticGeometry

end
