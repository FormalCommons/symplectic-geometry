/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import SymplecticGeometry.Analysis.SpecialFunctions.SmoothedMax
public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.SpecialShape

import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Complex.ExponentialBounds
import SymplecticGeometry.Analysis.Calculus.Deriv.CompMul
import SymplecticGeometry.Analysis.SpecialFunctions.Sqrt
import SymplecticGeometry.Analysis.SpecialFunctions.SmoothTransition.Deriv
import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.ConvexShape.SmoothedMax
import TauCeti.Analysis.Calculus.ContDiff.Prod
import TauCeti.Analysis.Real.Sqrt
import TauCeti.Analysis.SpecialFunctions.SmoothTransition

/-!
# Cutoff leaves over the cylinder

Leaves over the cylinder of radius `δ` of the form `b (1 - h r) + √(64 (r² - δ²) + c h r)`, where
`h r = smoothTransition ((r - 2 δ) / (L δ))` is a cutoff of width `L δ` starting at `2 δ`. Such a
leaf is the bottom leaf `√(64 r² - 64 δ²)` raised by `b` up to `2 δ`, and `√(64 r² - 64 δ² + c)`
from `(2 + L) δ` on. They serve the part of Cieliebak and Eliashberg's family of §4.6 that sweeps
out the neighbourhood of the corner of the surrounding shape.

## The shared estimate

For `δ = 1` and `r ≥ 2`, with `H` the cutoff, `p` and `q` its first two derivatives at `r`, and
`S` the square root, `SymplecticGeometry.isConvexShapeAt_of_cutoff_bounds` shows that the leaf is
an `i`-convex shape at `r` for `0 ≤ b ≤ 8`, `0 ≤ c ≤ 128`, `|p| ≤ 1 / 1024` and
`|r q| ≤ 1 / 1024`: then `6 r ≤ S ≤ 9 r`, `|c p| ≤ 1 / 8` and `|b p| ≤ 1 / 128`, so the slope is at
least `7` and the second derivative at least `-(20 + 1 / 128) / r`, against `343 / r` and
`1 / χ ≤ 1 / (6 r)`. Also the slope is at most `11`
(`SymplecticGeometry.deriv_le_of_cutoff_bounds`). The predicate
`SymplecticGeometry.IsCutoffScale L` says that `L ≥ 1` and that the bounds on `p` and `q` hold
at every point; every large enough `L` is such a cutoff scale
(`SymplecticGeometry.eventually_isCutoffScale`), by bounds on `smoothTransition'`,
`smoothTransition''` and `x smoothTransition'' x` (`Real.smoothTransition.abs_deriv_sub_div_le`).
The first two derivatives of the leaf `cutoffLeaf L 1 b c` are
`SymplecticGeometry.deriv_cutoffLeaf_one` and `SymplecticGeometry.iteratedDeriv_two_cutoffLeaf_one`;
with the bounds on `p` and `q` they give the case `r ≥ 2` of
`SymplecticGeometry.isConvexShapeAt_cutoffLeaf` and `SymplecticGeometry.deriv_cutoffLeaf_le`
below, for `δ = 1`. These estimates, and those of `Surround/BridgeLeaf.lean` and
`Surround/ShapeFamily.lean` built on them, take the one hypothesis `IsCutoffScale L`.

## The cutoff leaf

* `SymplecticGeometry.cutoffLeaf L δ b c`: the leaf above. The leaf for `δ` is the one for
  `δ = 1` with coefficients `b / δ` and `c / δ²`, rescaled
  (`SymplecticGeometry.cutoffLeaf_eq_mul_cutoffLeaf_one`); it is the bottom leaf raised by `b`
  up to `2 δ` (`SymplecticGeometry.cutoffLeaf_of_le`), so that its slope there is that of the
  bottom leaf (`SymplecticGeometry.deriv_cutoffLeaf_of_lt`) and tends to `+∞` at `δ`
  (`SymplecticGeometry.tendsto_deriv_cutoffLeaf`), and `√(64 r² - 64 δ² + c)` from `(2 + L) δ` on
  (`SymplecticGeometry.cutoffLeaf_of_ge`).
* Where its radicand does not vanish, for instance where `δ² < r²` and `0 < 64 (r² - δ²) + c`
  (`SymplecticGeometry.cutoffLeaf_radicand_pos`), the cutoff leaf is smooth in `b`, `c` and `r`
  (`ContDiffAt.cutoffLeaf`); at each `r` with `δ² ≤ r²` it increases strictly with `b` and
  `c ≥ 0` (`SymplecticGeometry.cutoffLeaf_lt_cutoffLeaf`).
* `SymplecticGeometry.exists_isConvexShapeAt_cutoffLeaf`: for `L` large enough, every cutoff leaf
  with `0 ≤ b ≤ 8 δ` and `0 ≤ c ≤ 128 δ²` is an `i`-convex shape at every `r > δ`. For `δ = 1` and
  `r < 2` the leaf is, near `r`, the shape `√(64 r² - 64)` of
  `SymplecticGeometry.isConvexShapeAt_sqrt_sub` plus the constant `b ≥ 0`; for `r ≥ 2` the shared
  estimate applies; `IsConvexShapeAt.rescale` passes to `δ`. For large `L` its slope is at most
  `11` from `2 δ` on (`SymplecticGeometry.deriv_cutoffLeaf_le`).

Both `SymplecticGeometry.sqrtAddLeaf` below and `SymplecticGeometry.sqrtSubLeaf`, in
`Surround/ShapeFamily.lean`, are cutoff leaves, and their API follows from that of `cutoffLeaf`.

## The leaves `sqrtAddLeaf`

* `SymplecticGeometry.sqrtAddLeaf L δ ℓ`: the cutoff leaf with `b = δ / 8 + ℓ` and
  `c = 64 δ² + ℓ²`. It is `√(64 r² - 64 δ²) + δ / 8 + ℓ` up to `2 δ`
  (`SymplecticGeometry.sqrtAddLeaf_of_le`), that is `8 √(r² - δ²) + δ / 8 + ℓ`
  (`SymplecticGeometry.sqrtAddLeaf_eq_eight_mul_sqrt_add_of_le`; for `δ = 1`,
  `SymplecticGeometry.sqrtAddLeaf_one_of_le`), and the standard shape `√(64 r² + ℓ²)` from
  `(2 + L) δ` on (`SymplecticGeometry.sqrtAddLeaf_of_ge`); the leaves for `δ` are those for
  `δ = 1` rescaled (`SymplecticGeometry.sqrtAddLeaf_eq_mul_sqrtAddLeaf_one`).
* `SymplecticGeometry.exists_isConvexShapeAt_sqrtAddLeaf`: for `L` large enough, every leaf with
  `ℓ ∈ [0, 15 δ / 2]` is an `i`-convex shape at every `r > δ`, as then `b ≤ 61 δ / 8` and
  `c ≤ 121 δ²`.
* The family is smooth in `(ℓ, r)` on `r > δ` (`SymplecticGeometry.contDiffOn_uncurry_sqrtAddLeaf`,
  and each leaf by itself, `SymplecticGeometry.contDiffOn_sqrtAddLeaf`),
  below `2 δ` the slope of each leaf is that of the bottom leaf
  (`SymplecticGeometry.deriv_sqrtAddLeaf_of_lt`) and tends to `+∞` at `δ`
  (`SymplecticGeometry.tendsto_deriv_sqrtAddLeaf`),
  and at each `r > δ` the leaves increase strictly with `ℓ ≥ 0`
  (`SymplecticGeometry.strictMonoOn_sqrtAddLeaf`). The bounds
  `8 √(r² - δ²) ≤ sqrtAddLeaf L δ ℓ r ≤ δ / 8 + ℓ + (8 r + ℓ)` and, for large `L`, the slope bound
  `11` from `2 δ` on are `SymplecticGeometry.eight_mul_sqrt_le_sqrtAddLeaf`,
  `SymplecticGeometry.sqrtAddLeaf_le` and `SymplecticGeometry.deriv_sqrtAddLeaf_le`.

## The Struwe switch leaves

* `SymplecticGeometry.struweSwitchLeaf L δ ℓ`: for `ℓ ≤ 6 δ` the leaf `sqrtAddLeaf L δ ℓ`
  (`SymplecticGeometry.struweSwitchLeaf_of_le`), and for `ℓ > 6 δ` the smoothed maximum, of width
  `(ℓ - 6 δ) / 200`, of that leaf and of Struwe's shape `T` with value `2 ℓ - 47 δ / 8` at `δ`
  (`SymplecticGeometry.struweSwitchLeaf_of_lt`). At `δ` the value of `T` exceeds that of
  `sqrtAddLeaf L δ ℓ` by `ℓ - 6 δ`, so that the width is proportional to that gap. The leaves for
  `δ` are those for `δ = 1` rescaled
  (`SymplecticGeometry.struweSwitchLeaf_eq_mul_struweSwitchLeaf_one`).
* For `δ = 1`, `w = √(r² - 1)` and `0 ≤ L`, the difference `sqrtAddLeaf L 1 ℓ r - T r` lies
  between `-(ℓ - 6) + (8 - √2) w` and `-(ℓ - 6) + 8 w` for `r ∈ [1, 2]`
  (`SymplecticGeometry.sqrtAddLeaf_sub_struweShape_mem_Icc`), and is at least `2` for `r ≥ 2`
  and `ℓ ∈ [0, 7]` (`SymplecticGeometry.two_le_sqrtAddLeaf_sub_struweShape`). These comparisons
  say where each of the two pieces of the smoothed maximum is the larger one.
* Consequences for `ℓ ∈ [0, 7 δ]`: from `2 δ` on the leaf is `sqrtAddLeaf L δ ℓ`
  (`SymplecticGeometry.struweSwitchLeaf_of_two_mul_le`), hence standard from `(2 + L) δ` on
  (`SymplecticGeometry.struweSwitchLeaf_of_ge`), and on `(δ, 257 δ / 256]` the leaf `7 δ` is
  Struwe's shape with value `65 δ / 8` at `δ`
  (`SymplecticGeometry.struweSwitchLeaf_seven_mul_of_mem_Ioc`).
* Near the cylinder, for `ℓ > 6 δ`, the leaf is Struwe's shape on some `[δ, δ + ε)`
  (`SymplecticGeometry.exists_eqOn_struweSwitchLeaf_struweShape`), since the gap `ℓ - 6 δ` at `δ`
  exceeds the width. So every leaf is continuous on `[δ, ∞)`
  (`SymplecticGeometry.continuousOn_struweSwitchLeaf`; the cutoff leaves are continuous,
  `SymplecticGeometry.continuous_cutoffLeaf`), and its slope tends to `+∞` at `δ`
  (`SymplecticGeometry.tendsto_deriv_struweSwitchLeaf`).
* `SymplecticGeometry.isConvexShapeAt_struweSwitchLeaf` and
  `SymplecticGeometry.exists_forall_isConvexShapeAt_struweSwitchLeaf`: for `L` large enough,
  every leaf with `ℓ ∈ [0, 7 δ]` is an `i`-convex shape at every `r > δ`. For `ℓ ≤ 6 δ` the leaf
  is `sqrtAddLeaf L δ ℓ`. Otherwise, for `δ = 1`, the leaf near `r` is `sqrtAddLeaf L 1 ℓ` where
  it exceeds Struwe's shape by more than the width, and Struwe's shape where the reverse holds,
  which by the comparisons happens only below `2`, where Struwe's shape is an `i`-convex shape.
  Where the two differ by at most the width, again below `2`, the comparison forces
  `√(r² - 1)` to be at least a fixed multiple of the width, so that the width times the sum of
  the two slopes, which are at most `8 r / √(r² - 1)` and `√2 r / √(r² - 1)`
  (`SymplecticGeometry.deriv_struweShape_le_sqrt_two_mul_div`), is at most `2 r`, and
  `SymplecticGeometry.isConvexShapeAt_smoothedMax` applies. `IsConvexShapeAt.rescale` passes
  to `δ`.
* For `0 ≤ L` and `0 < δ` the family is smooth in `(ℓ, r)` at every point with `δ < r`
  (`SymplecticGeometry.contDiffAt_uncurry_struweSwitchLeaf`): near `ℓ = 6 δ` the comparisons
  show that it is `sqrtAddLeaf`, and for `ℓ > 6 δ` it is a smoothed maximum of positive width
  (`SymplecticGeometry.contDiffAt_smoothedMax`). For `0 ≤ δ`, at each `r > δ`, the
  leaves `ℓ ≥ 0` increase strictly with `ℓ`
  (`SymplecticGeometry.strictMonoOn_struweSwitchLeaf`), since both pieces do and the width grows
  with `ℓ`.
* `SymplecticGeometry.exists_isConvexShapeAt_struweSwitchLeaf` collects these properties of the
  leaves `ℓ ∈ [0, 7 δ]`, for one `L` large enough, in the form in which the family over the
  cylinder uses them. Its leaf `0` is `sqrtAddLeaf L δ 0`, which `Surround/ShapeFamily.lean`
  identifies with the leaf `0` of `sqrtSubLeaf L δ` (`SymplecticGeometry.sqrtAddLeaf_zero`).

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  §4.6: Proposition 4.27.
-/

public section

namespace SymplecticGeometry

open Real Set Filter Topology
open scoped ContDiff

variable {δ : ℝ}

/-! ### The cutoff leaf -/

/-- The cutoff leaf over the cylinder of radius `δ` with coefficients `b` and `c`: with the
cutoff `h r = smoothTransition ((r - 2 δ) / (L δ))` of width `L δ` starting at `2 δ`,
`r ↦ b (1 - h r) + √(64 (r² - δ²) + c h r)`. It is the bottom leaf `√(64 r² - 64 δ²)` raised by
`b` for `r ≤ 2 δ` (when `L, δ ≥ 0`), and `√(64 r² - 64 δ² + c)` for `r ≥ (2 + L) δ` (when
`L, δ > 0`). -/
noncomputable def cutoffLeaf (L δ b c r : ℝ) : ℝ :=
  b * (1 - smoothTransition ((r - 2 * δ) / (L * δ))) +
    √(64 * (r ^ 2 - δ ^ 2) + c * smoothTransition ((r - 2 * δ) / (L * δ)))

theorem cutoffLeaf_def (L δ b c r : ℝ) : cutoffLeaf L δ b c r =
    b * (1 - smoothTransition ((r - 2 * δ) / (L * δ))) +
      √(64 * (r ^ 2 - δ ^ 2) + c * smoothTransition ((r - 2 * δ) / (L * δ))) :=
  (rfl)

/-- For `δ = 1`, the cutoff leaf written out, with the cutoff `smoothTransition ((x - 2) / L)`. -/
theorem cutoffLeaf_one (L b c : ℝ) : cutoffLeaf L 1 b c = fun x ↦
    b * (1 - smoothTransition ((x - 2) / L)) +
      √(64 * x ^ 2 - 64 + c * smoothTransition ((x - 2) / L)) := by
  ext x
  simp only [cutoffLeaf_def, one_pow, mul_one]
  ring_nf

/-! ### The shared estimate -/

/-- **The estimate for cutoff leaves.** Let `χ` be a function whose value and first two
derivatives at `r ≥ 2` are those of `b (1 - H) + S`, where `S ^ 2 = 64 r² - 64 + c H`, `H ∈ [0, 1]`
is the value of a cutoff at `r` and `p` and `q` are its first two derivatives at `r`. If
`0 ≤ b ≤ 8`, `0 ≤ c ≤ 128`, `|p| ≤ 1 / 1024` and `|r q| ≤ 1 / 1024`, then `χ` is an `i`-convex
shape at `r`. -/
theorem isConvexShapeAt_of_cutoff_bounds {χ : ℝ → ℝ} {b c r H p q S : ℝ} (hb₀ : 0 ≤ b)
    (hb : b ≤ 8) (hc₀ : 0 ≤ c) (hc : c ≤ 128) (hH₀ : 0 ≤ H) (hH : H ≤ 1)
    (hp : |p| ≤ 1 / 1024) (hq : |r * q| ≤ 1 / 1024) (hr : 2 ≤ r) (hS₀ : 0 ≤ S)
    (hS : S ^ 2 = 64 * r ^ 2 - 64 + c * H) (h₀ : χ r = b * (1 - H) + S)
    (h₁ : deriv χ r = -b * p + (128 * r + c * p) / (2 * S))
    (h₂ : iteratedDeriv 2 χ r =
      -b * q + (128 + c * q) / (2 * S) - (128 * r + c * p) ^ 2 / (4 * S ^ 3)) :
    IsConvexShapeAt χ r := by
  have hr₀ : 0 < r := by linarith
  have hq₂ : r * |q| ≤ 1 / 1024 := by rwa [abs_mul, abs_of_pos hr₀] at hq
  have hcH₀ : 0 ≤ c * H := mul_nonneg hc₀ hH₀
  -- `S ^ 2` lies between `36 r ^ 2` and `81 r ^ 2`, as `64 ≤ 16 r ^ 2`.
  have hS6 : 6 * r ≤ S := by nlinarith
  have hS9 : S ≤ 9 * r := by nlinarith
  have hSpos : 0 < S := by linarith
  have hcp : |c * p| ≤ 1 / 8 := by
    rw [abs_mul, abs_of_nonneg hc₀]; nlinarith [abs_nonneg p]
  have hcp' := abs_le.1 hcp
  have hbp : |b * p| ≤ 1 / 128 := by
    rw [abs_mul, abs_of_nonneg hb₀]; nlinarith [abs_nonneg p]
  have hbp' := abs_le.1 hbp
  have hχ : S ≤ χ r := by rw [h₀]; nlinarith
  have hinv : 1 / χ r ≤ 1 / 6 * (1 / r) := by
    rw [one_div_mul_one_div]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  -- The slope is at least `7`: with `S ≤ 9 r` and `c p ≥ -1 / 8`, the second term is at least
  -- `(128 r - 1 / 8) / (18 r) ≥ 7 + 1 / 128`, and the first is at least `-1 / 128`.
  have hF₁ : 0 < 128 * r + c * p := by linarith
  have hd : 7 ≤ deriv χ r := by
    have h18 : (128 * r + c * p) / (18 * r) ≤ (128 * r + c * p) / (2 * S) :=
      div_le_div_of_nonneg_left hF₁.le (by positivity) (by linarith)
    have h7 : 7 + 1 / 128 ≤ (128 * r + c * p) / (18 * r) := by
      rw [le_div_iff₀ (by positivity)]
      -- `(7 + 1 / 128) * 18 r = 126 r + 9 r / 64 ≤ 128 r - 1 / 8`, as `r ≥ 2`.
      linarith
    rw [h₁]
    linarith
  -- The negative terms of the second derivative are at most `(20 + 1 / 128) / r`.
  have hq' : |b * q| ≤ 1 / 128 * (1 / r) := by
    rw [abs_mul, abs_of_nonneg hb₀, mul_one_div, le_div_iff₀ hr₀]
    nlinarith [abs_nonneg q]
  have hT : (128 * r + c * p) ^ 2 / (4 * S ^ 3) ≤ 20 * (1 / r) := by
    rw [div_le_iff₀ (by positivity)]
    have : (128 * r + c * p) ^ 2 ≤ (129 * r) ^ 2 := by nlinarith
    have : (6 * r) ^ 3 ≤ S ^ 3 := by gcongr
    field_simp
    nlinarith
  have hF₂ : 0 ≤ (128 + c * q) / (2 * S) := by
    have : |c * q| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg hc₀]; nlinarith [abs_nonneg q]
    exact div_nonneg (by linarith [(abs_le.1 this).1]) (by positivity)
  have hd3 : 343 * (1 / r) ≤ deriv χ r ^ 3 / r := by
    rw [mul_one_div]
    gcongr
    have := pow_le_pow_left₀ (by norm_num) hd 3
    norm_num at this ⊢
    linarith
  refine isConvexShapeAt_iff.2 ⟨hr₀, by linarith, ?_, ?_⟩
  · have : 7 * (1 / r) ≤ deriv χ r / r := by rw [mul_one_div]; gcongr
    have : 0 < 1 / r := by positivity
    linarith
  · have : 0 < 1 / r := by positivity
    have := (abs_le.1 hq').2
    rw [h₂]
    linarith

/-- Under the hypotheses on the first derivative of `isConvexShapeAt_of_cutoff_bounds`, the slope
of the cutoff leaf at `r ≥ 2` is at most `11`: `S ≥ 6 r`, so the second term is at most
`(128 r + 1 / 8) / (12 r)`. -/
theorem deriv_le_of_cutoff_bounds {χ : ℝ → ℝ} {b c r H p S : ℝ} (hb₀ : 0 ≤ b) (hb : b ≤ 8)
    (hc₀ : 0 ≤ c) (hc : c ≤ 128) (hH₀ : 0 ≤ H) (hp : |p| ≤ 1 / 1024) (hr : 2 ≤ r)
    (hS₀ : 0 ≤ S) (hS : S ^ 2 = 64 * r ^ 2 - 64 + c * H)
    (h₁ : deriv χ r = -b * p + (128 * r + c * p) / (2 * S)) :
    deriv χ r ≤ 11 := by
  have hcH₀ : 0 ≤ c * H := mul_nonneg hc₀ hH₀
  have hS6 : 6 * r ≤ S := by nlinarith
  have hcp' : |c * p| ≤ 1 / 8 := by
    rw [abs_mul, abs_of_nonneg hc₀]; nlinarith [abs_nonneg p]
  have hbp' : |b * p| ≤ 1 / 128 := by
    rw [abs_mul, abs_of_nonneg hb₀]; nlinarith [abs_nonneg p]
  have hcp := abs_le.1 hcp'
  have hbp := abs_le.1 hbp'
  have hF₁ : 0 ≤ 128 * r + c * p := by linarith
  have h12 : (128 * r + c * p) / (2 * S) ≤ (128 * r + c * p) / (12 * r) :=
    div_le_div_of_nonneg_left hF₁ (by positivity) (by linarith)
  have h11 : (128 * r + c * p) / (12 * r) ≤ 11 - 1 / 128 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  rw [h₁]
  linarith

/-- The slope at `x > 1` of the cutoff leaf `b (1 - H x) + √(64 x² - 64 + c H x)` for `δ = 1`,
with the cutoff `H x = smoothTransition ((x - 2) / L)`, for `0 ≤ c`. -/
theorem deriv_cutoffLeaf_one {L b c x : ℝ} (hc : 0 ≤ c) (hx : 1 < x) :
    deriv (cutoffLeaf L 1 b c) x =
      -b * (deriv smoothTransition ((x - 2) / L) / L) +
        (128 * x + c * (deriv smoothTransition ((x - 2) / L) / L)) /
          (2 * √(64 * x ^ 2 - 64 + c * smoothTransition ((x - 2) / L))) := by
  have hpos : 0 < 64 * x ^ 2 - 64 + c * smoothTransition ((x - 2) / L) := by
    nlinarith [mul_nonneg hc (smoothTransition.nonneg ((x - 2) / L))]
  have hH := (((hasDerivAt_id' x).sub_const 2).div_const L).smoothTransition
  have hF := (((hasDerivAt_pow 2 x).const_mul 64).sub_const 64).add (hH.const_mul c)
  rw [cutoffLeaf_one]
  refine HasDerivAt.deriv ?_
  refine (((hH.const_sub 1).const_mul b).add (hF.sqrt hpos.ne')).congr_deriv ?_
  simp only [Pi.add_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  ring

/-- The second derivative at `x > 1` of the cutoff leaf
`b (1 - H x) + √(64 x² - 64 + c H x)` for `δ = 1`, with the cutoff
`H x = smoothTransition ((x - 2) / L)`, for `0 ≤ c`. -/
theorem iteratedDeriv_two_cutoffLeaf_one {L b c x : ℝ} (hc : 0 ≤ c) (hx : 1 < x) :
    iteratedDeriv 2 (cutoffLeaf L 1 b c) x =
      -b * (deriv (deriv smoothTransition) ((x - 2) / L) / L ^ 2) +
        (128 + c * (deriv (deriv smoothTransition) ((x - 2) / L) / L ^ 2)) /
          (2 * √(64 * x ^ 2 - 64 + c * smoothTransition ((x - 2) / L))) -
        (128 * x + c * (deriv smoothTransition ((x - 2) / L) / L)) ^ 2 /
          (4 * √(64 * x ^ 2 - 64 + c * smoothTransition ((x - 2) / L)) ^ 3) := by
  have hpos : 0 < 64 * x ^ 2 - 64 + c * smoothTransition ((x - 2) / L) := by
    nlinarith [mul_nonneg hc (smoothTransition.nonneg ((x - 2) / L))]
  have hev : deriv (cutoffLeaf L 1 b c) =ᶠ[𝓝 x] fun y ↦
      -b * (deriv smoothTransition ((y - 2) / L) / L) +
        (128 * y + c * (deriv smoothTransition ((y - 2) / L) / L)) /
          (2 * √(64 * y ^ 2 - 64 + c * smoothTransition ((y - 2) / L))) := by
    filter_upwards [lt_mem_nhds hx] with y hy using deriv_cutoffLeaf_one hc hy
  have hu := ((hasDerivAt_id' x).sub_const 2).div_const L
  have hH₁ := hu.deriv_smoothTransition.div_const L
  have hF := (((hasDerivAt_pow 2 x).const_mul 64).sub_const 64).add
    (hu.smoothTransition.const_mul c)
  have hS := sqrt_pos.2 hpos
  have hd := (hH₁.const_mul (-b)).add
    ((((hasDerivAt_id' x).const_mul 128).add (hH₁.const_mul c)).div
      ((hF.sqrt hpos.ne').const_mul 2) (mul_pos two_pos hS).ne')
  rw [iteratedDeriv_succ, iteratedDeriv_one, hev.deriv_eq]
  refine HasDerivAt.deriv ?_
  refine hd.congr_deriv ?_
  simp only [Pi.add_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  generalize √(64 * x ^ 2 - 64 + c * smoothTransition ((x - 2) / L)) = S at hS ⊢
  have hS₀ := hS.ne'
  field_simp
  ring

/-! ### Properties of the cutoff leaf -/

/-- The cutoff leaves for the radius `δ` are those for the radius `1`, rescaled by `δ`, with the
coefficients `b / δ` and `c / δ²`. -/
theorem cutoffLeaf_eq_mul_cutoffLeaf_one (hδ : 0 < δ) (L b c : ℝ) :
    cutoffLeaf L δ b c = fun r ↦ δ * cutoffLeaf L 1 (b / δ) (c / δ ^ 2) (r / δ) := by
  ext r
  have e : (r / δ - 2 * 1) / (L * 1) = (r - 2 * δ) / (L * δ) := by
    rcases eq_or_ne L 0 with rfl | hL
    · simp
    · field_simp
  have hm (X : ℝ) : δ * √X = √(δ ^ 2 * X) := by rw [sqrt_mul (sq_nonneg _), sqrt_sq hδ.le]
  rw [cutoffLeaf_def, cutoffLeaf_def, e, mul_add, hm]
  congr 1
  · field_simp
  · congr 1
    field_simp

/-- Up to `2 δ`, the cutoff leaf is the bottom leaf `√(64 r² - 64 δ²)` raised by `b`. -/
theorem cutoffLeaf_of_le {L b c r : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ) (hr : r ≤ 2 * δ) :
    cutoffLeaf L δ b c r = √(64 * r ^ 2 - 64 * δ ^ 2) + b := by
  rw [cutoffLeaf_def, smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))]
  ring_nf

/-- From `(2 + L) δ` on, the cutoff leaf is `√(64 r² - 64 δ² + c)`. -/
theorem cutoffLeaf_of_ge {L b c r : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hr : (2 + L) * δ ≤ r) :
    cutoffLeaf L δ b c r = √(64 * r ^ 2 - 64 * δ ^ 2 + c) := by
  rw [cutoffLeaf_def,
    smoothTransition.one_of_one_le ((one_le_div (by positivity)).2 (by linarith))]
  ring_nf

/-- Between `δ` and `2 δ`, the slope of the cutoff leaf is that of the bottom leaf,
`64 r / √(64 r² - 64 δ²)`. -/
theorem deriv_cutoffLeaf_of_lt {L b c r : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ) (hr : δ < r)
    (hr₂ : r < 2 * δ) :
    deriv (cutoffLeaf L δ b c) r = 64 * r / √(64 * r ^ 2 - 64 * δ ^ 2) := by
  have he : cutoffLeaf L δ b c =ᶠ[𝓝 r] fun x ↦ √(64 * x ^ 2 - 64 * δ ^ 2) + b := by
    filter_upwards [gt_mem_nhds hr₂] with x hx using cutoffLeaf_of_le hL hδ hx.le
  rw [he.deriv_eq, deriv_add_const, deriv_sqrt_sub (by nlinarith)]

/-- The slope of every cutoff leaf tends to `+∞` at `δ`, where it meets the cylinder. -/
theorem tendsto_deriv_cutoffLeaf {L : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ) (b c : ℝ) :
    Tendsto (deriv (cutoffLeaf L δ b c)) (𝓝[>] δ) atTop := by
  refine (tendsto_deriv_sqrt_sub (a := 64) (by norm_num) hδ).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (by linarith : δ < 2 * δ)] with r hr
  rw [deriv_cutoffLeaf_of_lt hL hδ.le hr.1 hr.2, deriv_sqrt_sub (by nlinarith [hr.1])]

/-- The cutoff leaf is continuous in `r`, for all `L`, `δ`, `b` and `c`. -/
theorem continuous_cutoffLeaf (L δ b c : ℝ) : Continuous (cutoffLeaf L δ b c) := by
  have h : Continuous fun r : ℝ ↦ smoothTransition ((r - 2 * δ) / (L * δ)) :=
    smoothTransition.continuous.comp ((continuous_id.sub continuous_const).div_const _)
  rw [show cutoffLeaf L δ b c = _ from funext (cutoffLeaf_def L δ b c)]
  exact (continuous_const.mul (continuous_const.sub h)).add
    ((continuous_const.mul ((continuous_id.pow 2).sub continuous_const)).add
      (continuous_const.mul h)).sqrt

/-- The radicand `64 (r² - δ²) + c h r` of the cutoff leaf is positive where `δ² < r²` and
`0 < 64 (r² - δ²) + c`: it lies between these two values, the cutoff `h r` being in `[0, 1]`. -/
theorem cutoffLeaf_radicand_pos (L : ℝ) {c r : ℝ} (hr : δ ^ 2 < r ^ 2)
    (hc : 0 < 64 * (r ^ 2 - δ ^ 2) + c) :
    0 < 64 * (r ^ 2 - δ ^ 2) + c * smoothTransition ((r - 2 * δ) / (L * δ)) := by
  have hH₀ := smoothTransition.nonneg ((r - 2 * δ) / (L * δ))
  have hH₁ := smoothTransition.le_one ((r - 2 * δ) / (L * δ))
  rcases le_total 0 c with h | h
  · nlinarith [mul_nonneg h hH₀]
  · nlinarith [mul_le_mul_of_nonpos_left hH₁ h]

/-- The cutoff leaf is smooth in its coefficients and its argument where its radicand does not
vanish: if `b`, `c` and `r` are smooth at `x` and `64 (r x² - δ²) + c x h (r x) ≠ 0`, then so is
`y ↦ cutoffLeaf L δ (b y) (c y) (r y)`. -/
theorem _root_.ContDiffAt.cutoffLeaf {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L : ℝ} {b c r : E → ℝ} {x : E} (hb : ContDiffAt ℝ ∞ b x) (hc : ContDiffAt ℝ ∞ c x)
    (hr : ContDiffAt ℝ ∞ r x)
    (hrad : 64 * (r x ^ 2 - δ ^ 2) + c x * smoothTransition ((r x - 2 * δ) / (L * δ)) ≠ 0) :
    ContDiffAt ℝ ∞ (fun y ↦ cutoffLeaf L δ (b y) (c y) (r y)) x := by
  have hH : ContDiffAt ℝ ∞ (fun y ↦ smoothTransition ((r y - 2 * δ) / (L * δ))) x :=
    smoothTransition.contDiff.contDiffAt.comp x ((hr.sub contDiffAt_const).div_const _)
  simp only [cutoffLeaf_def]
  exact (hb.mul (contDiffAt_const.sub hH)).add
    (((contDiffAt_const.mul ((hr.pow 2).sub contDiffAt_const)).add (hc.mul hH)).sqrt hrad)

/-- At each `r` with `δ² ≤ r²`, the cutoff leaf is strictly increasing in its coefficients
`b` and `c`, for `c ≥ 0`: the first term increases strictly where the cutoff is below `1`, and
the square root where it is positive. -/
theorem cutoffLeaf_lt_cutoffLeaf {L b₁ b₂ c₁ c₂ r : ℝ} (hb : b₁ < b₂) (hc : c₁ < c₂)
    (hc₁ : 0 ≤ c₁) (hr : δ ^ 2 ≤ r ^ 2) :
    cutoffLeaf L δ b₁ c₁ r < cutoffLeaf L δ b₂ c₂ r := by
  simp only [cutoffLeaf_def]
  set H := smoothTransition ((r - 2 * δ) / (L * δ))
  have hH₀ : 0 ≤ H := smoothTransition.nonneg _
  have hH₁ : H ≤ 1 := smoothTransition.le_one _
  rcases hH₁.lt_or_eq with hH | hH
  · exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_right hb (by linarith))
      (sqrt_le_sqrt (by nlinarith))
  · simp only [hH, sub_self, mul_zero, zero_add, mul_one]
    exact sqrt_lt_sqrt (by nlinarith) (by linarith)

/-- `L` is a cutoff scale for the estimates on cutoff leaves: `L ≥ 1`, and the first derivative
`p x = smoothTransition' ((x - 2) / L) / L` of the cutoff `x ↦ smoothTransition ((x - 2) / L)`
and its second derivative `q x = smoothTransition'' ((x - 2) / L) / L²` satisfy `|p x| ≤ 1 / 1024`
and `|x q x| ≤ 1 / 1024` for every `x`. These are the bounds that
`SymplecticGeometry.isConvexShapeAt_of_cutoff_bounds` and
`SymplecticGeometry.deriv_le_of_cutoff_bounds` need. -/
structure IsCutoffScale (L : ℝ) : Prop where
  one_le : 1 ≤ L
  abs_deriv_le (x : ℝ) : |deriv smoothTransition ((x - 2) / L) / L| ≤ 1 / 1024
  abs_mul_deriv_deriv_le (x : ℝ) :
    |x * (deriv (deriv smoothTransition) ((x - 2) / L) / L ^ 2)| ≤ 1 / 1024

/-- Every large enough `L` is a cutoff scale. -/
theorem eventually_isCutoffScale : ∀ᶠ L in atTop, IsCutoffScale L := by
  obtain ⟨A, hA⟩ := smoothTransition.exists_forall_norm_deriv_le
  obtain ⟨B, hB⟩ := smoothTransition.exists_forall_norm_deriv_deriv_le
  obtain ⟨M, hM⟩ := smoothTransition.exists_forall_norm_mul_deriv_deriv_le
  simp only [Real.norm_eq_abs] at hA hB hM
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop (1024 * (A + 2 * B + M))]
    with L hL₁ hL
  have h := smoothTransition.abs_deriv_sub_div_le hA hB hM zero_le_two hL₁ (ε := 1 / 1024)
    (by linarith)
  exact ⟨hL₁, fun x ↦ (h x).1, fun x ↦ (h x).2⟩

/-- The cutoff leaf with `0 ≤ b ≤ 8 δ` and `0 ≤ c ≤ 128 δ²`, for `δ > 0`, is an `i`-convex shape
at every `r > δ` when `L` is a cutoff scale. -/
theorem isConvexShapeAt_cutoffLeaf {L b c r : ℝ}
    (hL : IsCutoffScale L) (hδ : 0 < δ) (hb₀ : 0 ≤ b)
    (hb : b ≤ 8 * δ) (hc₀ : 0 ≤ c) (hc : c ≤ 128 * δ ^ 2) (hr : δ < r) :
    IsConvexShapeAt (cutoffLeaf L δ b c) r := by
  have hb₀' : 0 ≤ b / δ := div_nonneg hb₀ hδ.le
  have hb' : b / δ ≤ 8 := (div_le_iff₀ hδ).2 hb
  have hc₀' : 0 ≤ c / δ ^ 2 := div_nonneg hc₀ (sq_nonneg δ)
  have hc' : c / δ ^ 2 ≤ 128 := (div_le_iff₀ (by positivity)).2 hc
  have hr' : 1 < r / δ := (one_lt_div hδ).2 hr
  -- The case `δ = 1`, rescaled by `δ`.
  have h₁ : IsConvexShapeAt (cutoffLeaf L 1 (b / δ) (c / δ ^ 2)) (r / δ) := by
    rcases lt_or_ge (r / δ) 2 with h | h
    · refine ((isConvexShapeAt_sqrt_sub (a := 64) (c := 64 * 1 ^ 2) (by norm_num)
        (by linarith) (by nlinarith)).add_const hb₀').congr_of_eventuallyEq ?_
      filter_upwards [gt_mem_nhds h] with x hx
      exact cutoffLeaf_of_le (by linarith [hL.one_le]) zero_le_one (by linarith)
    · -- From `2` on, the shared estimate.
      exact isConvexShapeAt_of_cutoff_bounds hb₀' hb' hc₀' hc' (smoothTransition.nonneg _)
        (smoothTransition.le_one _) (hL.abs_deriv_le _) (hL.abs_mul_deriv_deriv_le _) h
        (sqrt_nonneg _)
        (sq_sqrt (by nlinarith [mul_nonneg hc₀' (smoothTransition.nonneg ((r / δ - 2) / L))]))
        (by rw [cutoffLeaf_one]) (deriv_cutoffLeaf_one hc₀' hr')
        (iteratedDeriv_two_cutoffLeaf_one hc₀' hr')
  have h := h₁.rescale hδ
  rwa [mul_div_cancel₀ r hδ.ne', ← cutoffLeaf_eq_mul_cutoffLeaf_one hδ] at h

/-- **The cutoff leaves are `i`-convex shapes.** There is `L₀ ≥ 1` such that for every `L ≥ L₀`,
`δ > 0`, `b ∈ [0, 8 δ]` and `c ∈ [0, 128 δ²]`, the cutoff leaf `cutoffLeaf L δ b c` is an
`i`-convex shape at every `r > δ`. -/
theorem exists_isConvexShapeAt_cutoffLeaf :
    ∃ L₀, 1 ≤ L₀ ∧ ∀ L, L₀ ≤ L → ∀ δ, 0 < δ → ∀ b ∈ Icc 0 (8 * δ), ∀ c ∈ Icc 0 (128 * δ ^ 2),
      ∀ r, δ < r → IsConvexShapeAt (cutoffLeaf L δ b c) r := by
  obtain ⟨L₀, h⟩ := eventually_atTop.1 eventually_isCutoffScale
  exact ⟨max 1 L₀, le_max_left _ _, fun L hL δ hδ b hb c hc r hr ↦
    isConvexShapeAt_cutoffLeaf (h L (le_of_max_le_right hL)) hδ hb.1 hb.2 hc.1 hc.2 hr⟩

/-- The slope of the cutoff leaf with `0 ≤ b ≤ 8 δ` and `0 ≤ c ≤ 128 δ²`, for `δ > 0`, is at
most `11` from `2 δ` on when `L` is a cutoff scale. -/
theorem deriv_cutoffLeaf_le {L b c r : ℝ}
    (hL : IsCutoffScale L) (hδ : 0 < δ) (hb₀ : 0 ≤ b)
    (hb : b ≤ 8 * δ) (hc₀ : 0 ≤ c) (hc : c ≤ 128 * δ ^ 2) (hr : 2 * δ ≤ r) :
    deriv (cutoffLeaf L δ b c) r ≤ 11 := by
  have hc₀' : 0 ≤ c / δ ^ 2 := div_nonneg hc₀ (sq_nonneg δ)
  have hr' : 2 ≤ r / δ := (le_div_iff₀ hδ).2 (by linarith)
  rw [cutoffLeaf_eq_mul_cutoffLeaf_one hδ, deriv_const_mul_comp_div_const hδ.ne']
  exact deriv_le_of_cutoff_bounds (div_nonneg hb₀ hδ.le) ((div_le_iff₀ hδ).2 hb) hc₀'
    ((div_le_iff₀ (by positivity)).2 hc) (smoothTransition.nonneg _) (hL.abs_deriv_le _) hr'
    (sqrt_nonneg _)
    (sq_sqrt (by nlinarith [mul_nonneg hc₀' (smoothTransition.nonneg ((r / δ - 2) / L))]))
    (deriv_cutoffLeaf_one hc₀' (by linarith))

/-! ### The leaves `sqrtAddLeaf` -/

/-- The leaf `ℓ` of the family of cutoff leaves over the cylinder of radius `δ` that rises
from the leaf `0` of `sqrtSubLeaf`: the cutoff leaf with `b = δ / 8 + ℓ` and `c = 64 δ² + ℓ²`,
that is, with `h r = smoothTransition ((r - 2 δ) / (L δ))`,
`r ↦ (δ / 8 + ℓ) (1 - h r) + √(64 (r² - δ²) + (64 δ² + ℓ²) h r)`. It is the bottom leaf
`√(64 r² - 64 δ²)` raised by `δ / 8 + ℓ` for `r ≤ 2 δ` (when `L, δ ≥ 0`), and, when `L, δ > 0`,
the standard shape `√(64 r² + ℓ²)` for `r ≥ (2 + L) δ`. -/
noncomputable def sqrtAddLeaf (L δ ℓ r : ℝ) : ℝ :=
  cutoffLeaf L δ (δ / 8 + ℓ) (64 * δ ^ 2 + ℓ ^ 2) r

/-- `sqrtAddLeaf` is the cutoff leaf with `b = δ / 8 + ℓ` and `c = 64 δ² + ℓ²`. -/
theorem sqrtAddLeaf_eq_cutoffLeaf (L δ ℓ : ℝ) :
    sqrtAddLeaf L δ ℓ = cutoffLeaf L δ (δ / 8 + ℓ) (64 * δ ^ 2 + ℓ ^ 2) :=
  (rfl)

theorem sqrtAddLeaf_def (L δ ℓ r : ℝ) : sqrtAddLeaf L δ ℓ r =
    (δ / 8 + ℓ) * (1 - smoothTransition ((r - 2 * δ) / (L * δ))) +
      √(64 * (r ^ 2 - δ ^ 2) + (64 * δ ^ 2 + ℓ ^ 2) * smoothTransition ((r - 2 * δ) / (L * δ))) :=
  by rw [sqrtAddLeaf_eq_cutoffLeaf, cutoffLeaf_def]

/-- The leaves for the radius `δ` are those for the radius `1`, rescaled by `δ`. -/
theorem sqrtAddLeaf_eq_mul_sqrtAddLeaf_one (hδ : 0 < δ) (L ℓ : ℝ) :
    sqrtAddLeaf L δ ℓ = fun r ↦ δ * sqrtAddLeaf L 1 (ℓ / δ) (r / δ) := by
  rw [sqrtAddLeaf_eq_cutoffLeaf, cutoffLeaf_eq_mul_cutoffLeaf_one hδ, sqrtAddLeaf_eq_cutoffLeaf]
  ext r
  congr 2 <;> field_simp

/-- Up to `2 δ`, the leaf `ℓ` is the bottom leaf `√(64 r² - 64 δ²)` raised by `δ / 8 + ℓ`. -/
theorem sqrtAddLeaf_of_le {L ℓ r : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ) (hr : r ≤ 2 * δ) :
    sqrtAddLeaf L δ ℓ r = √(64 * r ^ 2 - 64 * δ ^ 2) + (δ / 8 + ℓ) := by
  rw [sqrtAddLeaf_eq_cutoffLeaf, cutoffLeaf_of_le hL hδ hr]

/-- Up to `2 δ`, the leaf `ℓ` is `8 √(r² - δ²) + (δ / 8 + ℓ)`. -/
theorem sqrtAddLeaf_eq_eight_mul_sqrt_add_of_le {L ℓ r : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hr : r ≤ 2 * δ) : sqrtAddLeaf L δ ℓ r = 8 * √(r ^ 2 - δ ^ 2) + (δ / 8 + ℓ) := by
  rw [sqrtAddLeaf_of_le hL hδ hr,
    show 64 * r ^ 2 - 64 * δ ^ 2 = 8 ^ 2 * (r ^ 2 - δ ^ 2) by ring, sqrt_sq_mul,
    abs_of_pos (by norm_num)]

/-- For `δ = 1` and `0 ≤ L`, up to `2` the leaf `ℓ` is `8 √(r² - 1) + (1 / 8 + ℓ)`. -/
theorem sqrtAddLeaf_one_of_le {L ℓ r : ℝ} (hL : 0 ≤ L) (hr : r ≤ 2) :
    sqrtAddLeaf L 1 ℓ r = 8 * √(r ^ 2 - 1) + (1 / 8 + ℓ) := by
  rw [sqrtAddLeaf_eq_eight_mul_sqrt_add_of_le hL zero_le_one (by linarith), one_pow]

/-- From `(2 + L) δ` on, the leaf `ℓ` is the standard shape `√(64 r² + ℓ²)`. -/
theorem sqrtAddLeaf_of_ge {L ℓ r : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hr : (2 + L) * δ ≤ r) :
    sqrtAddLeaf L δ ℓ r = √(64 * r ^ 2 + ℓ ^ 2) := by
  rw [sqrtAddLeaf_eq_cutoffLeaf, cutoffLeaf_of_ge hL hδ hr]
  ring_nf

/-- The leaves `sqrtAddLeaf L δ ℓ`, for `δ > 0` and `ℓ ∈ [0, 15 δ / 2]`, are `i`-convex shapes at
every `r > δ` when `L` is a cutoff scale. -/
theorem isConvexShapeAt_sqrtAddLeaf {L ℓ r : ℝ}
    (hL : IsCutoffScale L) (hδ : 0 < δ) (hℓ : ℓ ∈ Icc 0 (15 * δ / 2))
    (hr : δ < r) : IsConvexShapeAt (sqrtAddLeaf L δ ℓ) r := by
  obtain ⟨hℓ₀, hℓ₁⟩ := hℓ
  exact isConvexShapeAt_cutoffLeaf hL hδ (by positivity) (by linarith)
    (by positivity) (by nlinarith) hr

/-- **The leaves `sqrtAddLeaf` are `i`-convex shapes.** There is `L₀ ≥ 1` such that for every
`L ≥ L₀`, `δ > 0` and `ℓ ∈ [0, 15 δ / 2]`, the leaf `sqrtAddLeaf L δ ℓ` is an `i`-convex shape at
every `r > δ`. -/
theorem exists_isConvexShapeAt_sqrtAddLeaf :
    ∃ L₀, 1 ≤ L₀ ∧ ∀ L, L₀ ≤ L → ∀ δ, 0 < δ → ∀ ℓ ∈ Icc 0 (15 * δ / 2), ∀ r, δ < r →
      IsConvexShapeAt (sqrtAddLeaf L δ ℓ) r := by
  obtain ⟨L₀, hL₀, h⟩ := exists_isConvexShapeAt_cutoffLeaf
  refine ⟨L₀, hL₀, fun L hL δ hδ ℓ ⟨hℓ₀, hℓ₁⟩ r hr ↦ ?_⟩
  -- The coefficients are `δ / 8 + ℓ ≤ 61 δ / 8` and `64 δ² + ℓ² ≤ 121 δ²`.
  exact h L hL δ hδ _ ⟨by positivity, by linarith⟩ _ ⟨by positivity, by nlinarith⟩ r hr

/-- The slope of the leaf `sqrtAddLeaf L δ ℓ`, for `δ > 0` and `ℓ ∈ [0, 15 δ / 2]`, is at most
`11` from `2 δ` on when `L` is a cutoff scale. -/
theorem deriv_sqrtAddLeaf_le {L ℓ r : ℝ}
    (hL : IsCutoffScale L) (hδ : 0 < δ) (hℓ : ℓ ∈ Icc 0 (15 * δ / 2))
    (hr : 2 * δ ≤ r) : deriv (sqrtAddLeaf L δ ℓ) r ≤ 11 := by
  obtain ⟨hℓ₀, hℓ₁⟩ := hℓ
  exact deriv_cutoffLeaf_le hL hδ (by positivity) (by linarith) (by positivity)
    (by nlinarith) hr

/-- The leaf `ℓ ≥ 0` is at least `8 √(r² - δ²)`, for `0 ≤ δ`. -/
theorem eight_mul_sqrt_le_sqrtAddLeaf (L : ℝ) (hδ : 0 ≤ δ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (r : ℝ) :
    8 * √(r ^ 2 - δ ^ 2) ≤ sqrtAddLeaf L δ ℓ r := by
  set H := smoothTransition ((r - 2 * δ) / (L * δ))
  have hH₀ : 0 ≤ H := smoothTransition.nonneg _
  have hH₁ : H ≤ 1 := smoothTransition.le_one _
  have h8 : 8 * √(r ^ 2 - δ ^ 2) = √(64 * (r ^ 2 - δ ^ 2)) := by
    rw [show (64 : ℝ) = 8 ^ 2 by norm_num, sqrt_sq_mul, abs_of_pos (by norm_num)]
  rw [sqrtAddLeaf_def, h8]
  have h₁ : 0 ≤ (δ / 8 + ℓ) * (1 - H) := mul_nonneg (by positivity) (by linarith)
  have h₂ : √(64 * (r ^ 2 - δ ^ 2)) ≤ √(64 * (r ^ 2 - δ ^ 2) + (64 * δ ^ 2 + ℓ ^ 2) * H) :=
    sqrt_le_sqrt (by nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 64 * δ ^ 2 + ℓ ^ 2) hH₀])
  linarith

/-- The leaf `ℓ ≥ 0` is at most `δ / 8 + ℓ + (8 r + ℓ)` at `r ≥ 0`, for `0 ≤ δ`: the cutoff term
is at most `δ / 8 + ℓ`, and the square root at most `√(64 r² + ℓ²) ≤ 8 r + ℓ`. -/
theorem sqrtAddLeaf_le (L : ℝ) (hδ : 0 ≤ δ) {ℓ r : ℝ} (hℓ : 0 ≤ ℓ) (hr : 0 ≤ r) :
    sqrtAddLeaf L δ ℓ r ≤ δ / 8 + ℓ + (8 * r + ℓ) := by
  set H := smoothTransition ((r - 2 * δ) / (L * δ))
  have hH₀ : 0 ≤ H := smoothTransition.nonneg _
  have hH₁ : H ≤ 1 := smoothTransition.le_one _
  rw [sqrtAddLeaf_def]
  have h₁ : (δ / 8 + ℓ) * (1 - H) ≤ δ / 8 + ℓ :=
    mul_le_of_le_one_right (by positivity) (by linarith)
  have h₂ : √(64 * (r ^ 2 - δ ^ 2) + (64 * δ ^ 2 + ℓ ^ 2) * H) ≤ 8 * r + ℓ := by
    rw [sqrt_le_left (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hH₁ (by positivity : (0 : ℝ) ≤ 64 * δ ^ 2 + ℓ ^ 2)]
  linarith

/-- The family `(ℓ, r) ↦ sqrtAddLeaf L δ ℓ r` is smooth where `δ < r`, for `0 ≤ δ`: there the
radicand is at least `64 (r² - δ²) > 0`. -/
theorem contDiffOn_uncurry_sqrtAddLeaf (L : ℝ) (hδ : 0 ≤ δ) :
    ContDiffOn ℝ ∞ (Function.uncurry (sqrtAddLeaf L δ)) (univ ×ˢ Ioi δ) := by
  have e : Function.uncurry (sqrtAddLeaf L δ) =
      fun p : ℝ × ℝ ↦ cutoffLeaf L δ (δ / 8 + p.1) (64 * δ ^ 2 + p.1 ^ 2) p.2 := by
    ext ⟨ℓ, r⟩
    rw [Function.uncurry_apply_pair, sqrtAddLeaf_eq_cutoffLeaf]
  rintro ⟨ℓ, r⟩ ⟨-, hr⟩
  rw [mem_Ioi] at hr
  have hrδ : δ ^ 2 < r ^ 2 := by gcongr
  rw [e]
  exact ((contDiffAt_const.add contDiffAt_fst).cutoffLeaf
    (contDiffAt_const.add (contDiffAt_fst.pow 2)) contDiffAt_snd
    (cutoffLeaf_radicand_pos L hrδ (by nlinarith)).ne').contDiffWithinAt

/-- The family `(ℓ, r) ↦ sqrtAddLeaf L δ ℓ r` is smooth at every `(ℓ, r)` with `δ < r`, for
`0 ≤ δ`. -/
theorem contDiffAt_uncurry_sqrtAddLeaf (L : ℝ) (hδ : 0 ≤ δ) {q : ℝ × ℝ} (hq : δ < q.2) :
    ContDiffAt ℝ ∞ (Function.uncurry (sqrtAddLeaf L δ)) q :=
  (contDiffOn_uncurry_sqrtAddLeaf L hδ).contDiffAt
    ((isOpen_univ.prod isOpen_Ioi).mem_nhds ⟨trivial, hq⟩)

/-- Each leaf `sqrtAddLeaf L δ ℓ` is `Cⁿ` where `δ < r`, for `0 ≤ δ`. -/
theorem contDiffOn_sqrtAddLeaf {n : ℕ∞} (L : ℝ) (hδ : 0 ≤ δ) (ℓ : ℝ) :
    ContDiffOn ℝ n (sqrtAddLeaf L δ ℓ) (Ioi δ) := fun r hr ↦
  ((contDiffAt_uncurry_sqrtAddLeaf L hδ (q := (ℓ, r)) hr).uncurry_left.of_le
    (by exact_mod_cast le_top)).contDiffWithinAt

/-- The slope of every leaf tends to `+∞` at `δ`, where the leaves meet the cylinder. -/
theorem tendsto_deriv_sqrtAddLeaf {L : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ) (ℓ : ℝ) :
    Tendsto (deriv (sqrtAddLeaf L δ ℓ)) (𝓝[>] δ) atTop := by
  rw [sqrtAddLeaf_eq_cutoffLeaf]
  exact tendsto_deriv_cutoffLeaf hL hδ _ _

/-- Each leaf `sqrtAddLeaf L δ ℓ` is continuous. -/
theorem continuous_sqrtAddLeaf (L δ ℓ : ℝ) : Continuous (sqrtAddLeaf L δ ℓ) := by
  rw [sqrtAddLeaf_eq_cutoffLeaf]
  exact continuous_cutoffLeaf _ _ _ _

/-- Between `δ` and `2 δ`, the slope of each leaf is that of the bottom leaf,
`8 r / √(r² - δ²)`. -/
theorem deriv_sqrtAddLeaf_of_lt {L ℓ r : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ) (hr : δ < r)
    (hr₂ : r < 2 * δ) :
    deriv (sqrtAddLeaf L δ ℓ) r = 8 * r / √(r ^ 2 - δ ^ 2) := by
  rw [sqrtAddLeaf_eq_cutoffLeaf, deriv_cutoffLeaf_of_lt hL hδ hr hr₂,
    show 64 * r ^ 2 - 64 * δ ^ 2 = 8 ^ 2 * (r ^ 2 - δ ^ 2) by ring, sqrt_sq_mul,
    abs_of_pos (by norm_num)]
  field_simp
  ring

/-- For `0 ≤ δ`, at each `r > δ`, the leaves `ℓ ≥ 0` are strictly increasing in `ℓ`: both
terms of `sqrtAddLeaf` are nondecreasing in `ℓ ≥ 0`, the first strictly where the cutoff is
below `1` and the second where it is positive. -/
theorem strictMonoOn_sqrtAddLeaf (L : ℝ) (hδ : 0 ≤ δ) {r : ℝ} (hr : δ < r) :
    StrictMonoOn (fun ℓ ↦ sqrtAddLeaf L δ ℓ r) (Ici 0) := by
  intro ℓ₁ hℓ₁ ℓ₂ hℓ₂ h
  rw [mem_Ici] at hℓ₁ hℓ₂
  simp only [sqrtAddLeaf_eq_cutoffLeaf]
  exact cutoffLeaf_lt_cutoffLeaf (by linarith) (by nlinarith) (by positivity) (by gcongr)

/-! ### The Struwe switch leaves -/

/-- The leaf `ℓ` of the family over the cylinder of radius `δ` that switches from
`sqrtAddLeaf L δ ℓ` to Struwe's shape near the cylinder. With `A = sqrtAddLeaf L δ ℓ` and
`T = struweShape δ 1 (2 ℓ - 47 δ / 8)`, Struwe's shape with value `2 ℓ - 47 δ / 8` at `δ`, it is
`A` for `ℓ ≤ 6 δ`, and the smoothed maximum of `A` and `T` of width `(ℓ - 6 δ) / 200` for
`ℓ > 6 δ`. -/
noncomputable def struweSwitchLeaf (L δ ℓ r : ℝ) : ℝ :=
  if ℓ ≤ 6 * δ then sqrtAddLeaf L δ ℓ r
  else smoothedMax ((ℓ - 6 * δ) / 200) (sqrtAddLeaf L δ ℓ r)
    (struweShape δ 1 (2 * ℓ - 47 * δ / 8) r)

theorem struweSwitchLeaf_def (L δ ℓ r : ℝ) : struweSwitchLeaf L δ ℓ r =
    if ℓ ≤ 6 * δ then sqrtAddLeaf L δ ℓ r
    else smoothedMax ((ℓ - 6 * δ) / 200) (sqrtAddLeaf L δ ℓ r)
      (struweShape δ 1 (2 * ℓ - 47 * δ / 8) r) :=
  (rfl)

/-- For `ℓ ≤ 6 δ` the leaf `ℓ` is `sqrtAddLeaf L δ ℓ`. -/
theorem struweSwitchLeaf_of_le {L ℓ : ℝ} (hℓ : ℓ ≤ 6 * δ) :
    struweSwitchLeaf L δ ℓ = sqrtAddLeaf L δ ℓ := by
  ext r
  simp only [struweSwitchLeaf_def, hℓ, ↓reduceIte]

/-- For `ℓ > 6 δ` the leaf `ℓ` is the smoothed maximum, of width `(ℓ - 6 δ) / 200`, of
`sqrtAddLeaf L δ ℓ` and Struwe's shape with value `2 ℓ - 47 δ / 8` at `δ`. -/
theorem struweSwitchLeaf_of_lt {L ℓ : ℝ} (hℓ : 6 * δ < ℓ) :
    struweSwitchLeaf L δ ℓ = fun r ↦ smoothedMax ((ℓ - 6 * δ) / 200) (sqrtAddLeaf L δ ℓ r)
      (struweShape δ 1 (2 * ℓ - 47 * δ / 8) r) := by
  ext r
  simp only [struweSwitchLeaf_def, hℓ.not_ge, ↓reduceIte]

/-- The leaves for the radius `δ > 0` are those for the radius `1`, rescaled by `δ`. -/
theorem struweSwitchLeaf_eq_mul_struweSwitchLeaf_one (hδ : 0 < δ) (L ℓ : ℝ) :
    struweSwitchLeaf L δ ℓ = fun r ↦ δ * struweSwitchLeaf L 1 (ℓ / δ) (r / δ) := by
  ext r
  have hA := congrFun (sqrtAddLeaf_eq_mul_sqrtAddLeaf_one hδ L ℓ) r
  rcases le_or_gt ℓ (6 * δ) with hℓ | hℓ
  · have hℓ' : ℓ / δ ≤ 6 * 1 := by rw [mul_one, div_le_iff₀ hδ]; exact hℓ
    rw [struweSwitchLeaf_of_le hℓ, struweSwitchLeaf_of_le hℓ', hA]
  · have hℓ' : 6 * 1 < ℓ / δ := by rw [mul_one, lt_div_iff₀ hδ]; exact hℓ
    have hT := congrFun (struweShape_eq_mul_struweShape_one hδ.ne' 1 (2 * ℓ - 47 * δ / 8)) r
    have hc : (2 * ℓ - 47 * δ / 8) / δ = 2 * (ℓ / δ) - 47 * 1 / 8 := by field_simp
    have hw : (ℓ - 6 * δ) / 200 = δ * ((ℓ / δ - 6 * 1) / 200) := by field_simp
    have hw₀ : (ℓ / δ - 6 * 1) / 200 ≠ 0 := (div_pos (sub_pos.2 hℓ') (by norm_num)).ne'
    rw [struweSwitchLeaf_of_lt hℓ, struweSwitchLeaf_of_lt hℓ']
    dsimp only
    rw [hA, hT, hc, hw,
      smoothedMax_eq_mul_smoothedMax_one (mul_ne_zero hδ.ne' hw₀),
      smoothedMax_eq_mul_smoothedMax_one hw₀, mul_div_mul_left _ _ hδ.ne',
      mul_div_mul_left _ _ hδ.ne', mul_assoc]

/-- For `0 ≤ L` and `r ∈ [1, 2]`, the difference of `sqrtAddLeaf L 1 ℓ` and Struwe's shape with
value `2 ℓ - 47 / 8` at `1` lies between `-(ℓ - 6) + (8 - √2) √(r² - 1)` and
`-(ℓ - 6) + 8 √(r² - 1)`: there the first is `1 / 8 + ℓ + 8 √(r² - 1)`, and the second rises by at
most `√2 √(r² - 1)` from `1` to `r` (`struweShape_sub_struweShape_one_mem_Icc`). -/
theorem sqrtAddLeaf_sub_struweShape_mem_Icc {L : ℝ} (hL : 0 ≤ L) (ℓ : ℝ) {r : ℝ}
    (hr : r ∈ Icc 1 2) :
    sqrtAddLeaf L 1 ℓ r - struweShape 1 1 (2 * ℓ - 47 / 8) r ∈
      Icc (-(ℓ - 6) + (8 - √2) * √(r ^ 2 - 1)) (-(ℓ - 6) + 8 * √(r ^ 2 - 1)) := by
  have hT := struweShape_sub_struweShape_one_mem_Icc le_rfl (2 * ℓ - 47 / 8) hr.1
  rw [sqrtAddLeaf_one_of_le hL hr.2]
  rw [struweShape_one_apply_self] at hT
  obtain ⟨hT₀, hT₁⟩ := hT
  constructor <;> nlinarith

/-- From `r = 2` on, `sqrtAddLeaf L 1 ℓ` exceeds Struwe's shape with value `2 ℓ - 47 / 8` at `1`
by at least `2`, for `ℓ ∈ [0, 7]`: the first is at least `8 √(r² - 1) ≥ 8 r - 3`, the second is
at most `11` at `2` and has slope at most `1 / √(log 2) < 5 / 4` from `2` on. -/
theorem two_le_sqrtAddLeaf_sub_struweShape (L : ℝ) {ℓ r : ℝ} (hℓ : ℓ ∈ Icc 0 7) (hr : 2 ≤ r) :
    2 ≤ sqrtAddLeaf L 1 ℓ r - struweShape 1 1 (2 * ℓ - 47 / 8) r := by
  set T := struweShape 1 1 (2 * ℓ - 47 / 8)
  -- The value of `T` at `2`.
  have hT₂ : T 2 ≤ 11 := by
    have h := (struweShape_sub_struweShape_one_mem_Icc le_rfl (2 * ℓ - 47 / 8)
      one_le_two).2
    have h1 : T 1 = 2 * ℓ - 47 / 8 := struweShape_one_apply_self 1 _
    have h6 : √2 * √(2 ^ 2 - 1) < 5 / 2 := by
      rw [← sqrt_mul zero_le_two, sqrt_lt' (by norm_num)]
      norm_num
    linarith [hℓ.2]
  -- The slope of `T` is at most `5 / 4` from `2` on.
  have hslope : T r - T 2 ≤ 5 / 4 * (r - 2) := by
    have h := struweShape_sub_struweShape_le one_pos le_rfl (2 * ℓ - 47 / 8) one_lt_two hr
    have hs : 4 / 5 ≤ √(log (2 / 1)) :=
      le_sqrt_of_sq_le (by rw [div_one]; linarith [log_two_gt_d9])
    calc T r - T 2 ≤ (r - 2) / √(log (2 / 1)) := h
      _ ≤ (r - 2) / (4 / 5) := div_le_div_of_nonneg_left (by linarith) (by norm_num) hs
      _ = 5 / 4 * (r - 2) := by ring
  -- The leaf is at least `8 √(r² - 1) ≥ 8 r - 3`.
  have hA := eight_mul_sqrt_le_sqrtAddLeaf L zero_le_one hℓ.1 r
  have hs : 8 * r - 3 ≤ 8 * √(r ^ 2 - 1 ^ 2) := by
    rw [show 8 * √(r ^ 2 - 1 ^ 2) = √(8 ^ 2 * (r ^ 2 - 1 ^ 2)) by
      rw [sqrt_sq_mul, abs_of_pos (by norm_num)]]
    exact le_sqrt_of_sq_le (by nlinarith)
  linarith

/-! ### The far part, the germ and the vertical tangent of the Struwe switch leaves -/

/-- For `ℓ ∈ [0, 7]` and `r ≥ 2`, the leaf `ℓ` for the radius `1` is `sqrtAddLeaf L 1 ℓ`. -/
private theorem struweSwitchLeaf_one_of_two_le (L : ℝ) {ℓ r : ℝ} (hℓ : ℓ ∈ Icc 0 7)
    (hr : 2 ≤ r) : struweSwitchLeaf L 1 ℓ r = sqrtAddLeaf L 1 ℓ r := by
  rcases le_or_gt ℓ (6 * 1) with h | h
  · rw [struweSwitchLeaf_of_le h]
  · have h2 := two_le_sqrtAddLeaf_sub_struweShape L hℓ hr
    rw [struweSwitchLeaf_of_lt h]
    dsimp only
    rw [mul_one, mul_one] at *
    exact smoothedMax_eq_left (div_pos (by linarith) (by norm_num)) (by linarith [hℓ.2])

/-- From `2 δ` on, the leaf `ℓ ∈ [0, 7 δ]` is `sqrtAddLeaf L δ ℓ`, for `δ > 0`: there
`sqrtAddLeaf L δ ℓ` exceeds Struwe's shape by at least `2 δ`
(`SymplecticGeometry.two_le_sqrtAddLeaf_sub_struweShape`), more than the width of the smoothed
maximum. -/
theorem struweSwitchLeaf_of_two_mul_le (L : ℝ) (hδ : 0 < δ) {ℓ r : ℝ}
    (hℓ : ℓ ∈ Icc 0 (7 * δ)) (hr : 2 * δ ≤ r) :
    struweSwitchLeaf L δ ℓ r = sqrtAddLeaf L δ ℓ r := by
  rw [struweSwitchLeaf_eq_mul_struweSwitchLeaf_one hδ, sqrtAddLeaf_eq_mul_sqrtAddLeaf_one hδ]
  dsimp only
  rw [struweSwitchLeaf_one_of_two_le L ⟨div_nonneg hℓ.1 hδ.le, (div_le_iff₀ hδ).2 hℓ.2⟩
    ((le_div_iff₀ hδ).2 hr)]

/-- From `(2 + L) δ` on, for `L, δ > 0`, the leaf `ℓ ∈ [0, 7 δ]` is the standard shape
`√(64 r² + ℓ²)`. -/
theorem struweSwitchLeaf_of_ge {L : ℝ} (hL : 0 < L) (hδ : 0 < δ) {ℓ r : ℝ}
    (hℓ : ℓ ∈ Icc 0 (7 * δ)) (hr : (2 + L) * δ ≤ r) :
    struweSwitchLeaf L δ ℓ r = √(64 * r ^ 2 + ℓ ^ 2) := by
  rw [struweSwitchLeaf_of_two_mul_le L hδ hℓ (by nlinarith), sqrtAddLeaf_of_ge hL hδ hr]

/-- For `0 ≤ L` and `r ∈ (1, 257 / 256]`, the leaf `7` for the radius `1` is Struwe's shape with
value `65 / 8` at `1`. -/
private theorem struweSwitchLeaf_one_seven {L r : ℝ} (hL : 0 ≤ L) (hr : r ∈ Ioc 1 (257 / 256)) :
    struweSwitchLeaf L 1 7 r = struweShape 1 1 (65 / 8) r := by
  have h := (sqrtAddLeaf_sub_struweShape_mem_Icc hL 7 ⟨hr.1.le, by linarith [hr.2]⟩).2
  have hr2 : r ^ 2 ≤ (257 / 256) ^ 2 := pow_le_pow_left₀ (by linarith [hr.1]) hr.2 2
  -- Here `√(r² - 1) ≤ 1 / 11`, so `sqrtAddLeaf L 1 7 r` is below Struwe's shape by `3 / 11`.
  have hw : √(r ^ 2 - 1) ≤ 1 / 11 := by
    rw [sqrt_le_left (by norm_num)]
    linarith
  rw [show (2 * 7 - 47 / 8 : ℝ) = 65 / 8 by norm_num] at h
  rw [struweSwitchLeaf_of_lt (by norm_num)]
  dsimp only
  rw [show (2 * 7 - 47 * 1 / 8 : ℝ) = 65 / 8 by norm_num]
  exact smoothedMax_eq_right (by norm_num) (by linarith)

/-- **The germ of the leaf `7 δ`.** For `0 ≤ L` and `δ > 0`, near the cylinder, on
`(δ, 257 δ / 256]`, the leaf `7 δ` is Struwe's shape with value `65 δ / 8` at `δ`. -/
theorem struweSwitchLeaf_seven_mul_of_mem_Ioc {L : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ) {r : ℝ}
    (hr : r ∈ Ioc δ (257 * δ / 256)) :
    struweSwitchLeaf L δ (7 * δ) r = struweShape δ 1 (65 * δ / 8) r := by
  rw [struweSwitchLeaf_eq_mul_struweSwitchLeaf_one hδ, struweShape_eq_mul_struweShape_one hδ.ne',
    mul_div_cancel_right₀ _ hδ.ne', show 65 * δ / 8 / δ = 65 / 8 by field_simp]
  dsimp only
  rw [struweSwitchLeaf_one_seven hL ⟨(lt_div_iff₀ hδ).2 (by linarith [hr.1]),
    (div_le_iff₀ hδ).2 (by linarith [hr.2])⟩]

/-- For `0 ≤ L`, `δ > 0` and `ℓ > 6 δ`, the leaf `ℓ` is Struwe's shape with value
`2 ℓ - 47 δ / 8` at `δ` on some interval `[δ, δ + ε)`: at `δ` this shape exceeds
`sqrtAddLeaf L δ ℓ` by `ℓ - 6 δ`, more than the width `(ℓ - 6 δ) / 200` of the smoothed
maximum. -/
theorem exists_eqOn_struweSwitchLeaf_struweShape {L : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ) {ℓ : ℝ}
    (hℓ : 6 * δ < ℓ) :
    ∃ ε > 0, EqOn (struweSwitchLeaf L δ ℓ) (struweShape δ 1 (2 * ℓ - 47 * δ / 8))
      (Ico δ (δ + ε)) := by
  have hT : struweShape δ 1 (2 * ℓ - 47 * δ / 8) δ = 2 * ℓ - 47 * δ / 8 :=
    struweShape_one_apply_self δ _
  have hA : sqrtAddLeaf L δ ℓ δ = δ / 8 + ℓ := by
    rw [sqrtAddLeaf_of_le hL hδ.le (by linarith)]
    simp
  obtain ⟨u, hu, h⟩ :=
    exists_eqOn_smoothedMax_right (div_pos (sub_pos.2 hℓ) (by norm_num : (0 : ℝ) < 200))
    (continuous_sqrtAddLeaf L δ ℓ).continuousWithinAt
    (continuousOn_struweShape hδ le_rfl _ δ self_mem_Ici) (by rw [hA, hT]; linarith)
  refine ⟨u - δ, sub_pos.2 hu, fun r hr ↦ ?_⟩
  rw [add_sub_cancel] at hr
  rw [struweSwitchLeaf_of_lt hℓ]
  exact h hr

/-- For `δ > 0`, each leaf `struweSwitchLeaf L δ ℓ` is continuous on `[δ, ∞)`. -/
theorem continuousOn_struweSwitchLeaf (L : ℝ) (hδ : 0 < δ) (ℓ : ℝ) :
    ContinuousOn (struweSwitchLeaf L δ ℓ) (Ici δ) := by
  rcases le_or_gt ℓ (6 * δ) with hℓ | hℓ
  · rw [struweSwitchLeaf_of_le hℓ]
    exact (continuous_sqrtAddLeaf L δ ℓ).continuousOn
  · rw [struweSwitchLeaf_of_lt hℓ]
    exact (contDiff_smoothedMax (n := 0) _).continuous.comp_continuousOn
      ((continuous_sqrtAddLeaf L δ ℓ).continuousOn.prodMk (continuousOn_struweShape hδ le_rfl _))

/-- For `0 ≤ L` and `δ > 0`, the slope of every leaf `struweSwitchLeaf L δ ℓ` tends to `+∞` at
`δ`: for `ℓ ≤ 6 δ` the leaf is `sqrtAddLeaf L δ ℓ`, and for `ℓ > 6 δ` it is Struwe's shape near
`δ` (`SymplecticGeometry.exists_eqOn_struweSwitchLeaf_struweShape`). -/
theorem tendsto_deriv_struweSwitchLeaf {L : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ) (ℓ : ℝ) :
    Tendsto (deriv (struweSwitchLeaf L δ ℓ)) (𝓝[>] δ) atTop := by
  rcases le_or_gt ℓ (6 * δ) with hℓ | hℓ
  · rw [struweSwitchLeaf_of_le hℓ]
    exact tendsto_deriv_sqrtAddLeaf hL hδ ℓ
  · obtain ⟨ε, hε, h⟩ := exists_eqOn_struweSwitchLeaf_struweShape hL hδ hℓ
    exact tendsto_deriv_of_eqOn_struweShape hδ le_rfl (by linarith) (h.mono Ioo_subset_Ico_self)

/-- The case `δ = 1`, `ℓ ∈ (6, 7]` of `isConvexShapeAt_struweSwitchLeaf`. With
`A = sqrtAddLeaf L 1 ℓ`, `T` Struwe's shape with value `2 ℓ - 47 / 8` at `1` and the width
`η = (ℓ - 6) / 200`: the leaf is `A` near `r` where `A r - T r > η`; it is `T` near `r` where
`A r - T r < -η`, which happens only below `2`, where `T` is an `i`-convex shape; elsewhere `r < 2`
too, and the slopes of `A` and `T` at `r` are small enough against `1 / η`. These are the three
cases of `isConvexShapeAt_smoothedMax_of_imp`. -/
private theorem isConvexShapeAt_struweSwitchLeaf_one {L ℓ r : ℝ} (hL : 0 ≤ L)
    (hℓ : ℓ ∈ Ioc 6 7) (hr : 1 < r) (hA : IsConvexShapeAt (sqrtAddLeaf L 1 ℓ) r) :
    IsConvexShapeAt (struweSwitchLeaf L 1 ℓ) r := by
  obtain ⟨hℓ₆, hℓ₇⟩ := hℓ
  have hχ : struweSwitchLeaf L 1 ℓ = fun x ↦ smoothedMax ((ℓ - 6) / 200) (sqrtAddLeaf L 1 ℓ x)
      (struweShape 1 1 (2 * ℓ - 47 / 8) x) := by
    rw [struweSwitchLeaf_of_lt (by linarith)]
    simp only [mul_one]
  set A := sqrtAddLeaf L 1 ℓ
  set T := struweShape 1 1 (2 * ℓ - 47 / 8)
  set η := (ℓ - 6) / 200 with hη
  have hη₀ : 0 < η := by rw [hη]; linarith
  have hAc : ContDiffAt ℝ 2 A r :=
    (contDiffOn_sqrtAddLeaf L zero_le_one ℓ).contDiffAt (Ioi_mem_nhds hr)
  have hTc : ContDiffAt ℝ 2 T r :=
    (contDiffOn_struweShape one_pos le_rfl _).contDiffAt (Ioi_mem_nhds hr)
  -- From `2` on, `A - T ≥ 2 > η`.
  have hr₂ : A r - T r ≤ η → r < 2 := fun h ↦ by
    by_contra! h'
    have := two_le_sqrtAddLeaf_sub_struweShape L ⟨by linarith, hℓ₇⟩ h'
    linarith
  rw [hχ]
  refine isConvexShapeAt_smoothedMax_of_imp hAc hTc hη₀ (fun _ ↦ hA) (fun h ↦ ?_) (fun h ↦ ?_)
  · -- Struwe's shape is an `i`-convex shape on `(1, 2]`.
    have hr₂ := hr₂ (by linarith)
    have hs : √(log (2 / 1)) ≤ 1 :=
      sqrt_le_one.2 (by rw [div_one]; linarith [log_two_lt_d9])
    have hs₀ : 0 ≤ √(log (2 / 1)) := sqrt_nonneg _
    refine isConvexShapeAt_struweShape_of_le_of_mem_Ioc (m := 6) one_pos le_rfl
      (by rw [struweShape_one_apply_self]; linarith) (by linarith) ?_ ⟨hr, hr₂.le⟩
    nlinarith [pow_le_one₀ hs₀ hs (n := 3)]
  -- Where `|A r - T r| ≤ η`, the width condition of `isConvexShapeAt_smoothedMax`.
  obtain ⟨h₂, h₁⟩ := abs_le.1 h
  have hr₂ := hr₂ h₁
  set w := √(r ^ 2 - 1)
  have hw₀ : 0 < w := sqrt_pos.2 (by nlinarith)
  have hdA : deriv A r = 8 * r / w := by
    rw [deriv_sqrtAddLeaf_of_lt hL zero_le_one hr (by linarith), one_pow]
  have hdT : deriv T r ≤ √2 * r / w := by
    simpa only [one_pow] using deriv_struweShape_le_sqrt_two_mul_div one_pos le_rfl _ hr
  -- The upper bound of `A r - T r` gives `8 w ≥ 199 η`.
  have hw : 199 * η ≤ 8 * w := by
    have h := (sqrtAddLeaf_sub_struweShape_mem_Icc hL ℓ ⟨hr.le, hr₂.le⟩).2
    rw [hη] at h₂ ⊢
    linarith
  have h2 : √2 < 2 := by rw [sqrt_lt' two_pos]; norm_num
  have key : η * ((8 + √2) * r) ≤ 2 * r * w := by
    have h3 : η * r * √2 ≤ η * r * 2 := mul_le_mul_of_nonneg_left h2.le (by positivity)
    have h4 : r * (199 * η) ≤ r * (8 * w) := mul_le_mul_of_nonneg_left hw (by linarith)
    have h5 : 0 ≤ η * r := by positivity
    nlinarith
  calc η * (deriv A r + deriv T r) ≤ η * (8 * r / w + √2 * r / w) := by
        rw [hdA]; gcongr
    _ = η * ((8 + √2) * r) / w := by ring
    _ ≤ 2 * r := by rw [div_le_iff₀ hw₀]; exact key

/-- **The leaves `struweSwitchLeaf` are `i`-convex shapes.** For `δ > 0` and `ℓ ∈ [0, 7 δ]`, the
leaf `struweSwitchLeaf L δ ℓ` is an `i`-convex shape at every `r > δ` when `L` is a cutoff
scale. -/
theorem isConvexShapeAt_struweSwitchLeaf {L ℓ r : ℝ}
    (hL : IsCutoffScale L) (hδ : 0 < δ) (hℓ : ℓ ∈ Icc 0 (7 * δ))
    (hr : δ < r) : IsConvexShapeAt (struweSwitchLeaf L δ ℓ) r := by
  obtain ⟨hℓ₀, hℓ₇⟩ := hℓ
  rcases le_or_gt ℓ (6 * δ) with hℓ | hℓ
  · rw [struweSwitchLeaf_of_le hℓ]
    exact isConvexShapeAt_sqrtAddLeaf hL hδ ⟨hℓ₀, by linarith⟩ hr
  -- For `ℓ > 6 δ`, rescale the leaf `ℓ / δ` for the radius `1`.
  have hℓ' : ℓ / δ ∈ Ioc 6 7 :=
    ⟨by rw [lt_div_iff₀ hδ]; exact hℓ, by rw [div_le_iff₀ hδ]; exact hℓ₇⟩
  have hr' : 1 < r / δ := (one_lt_div hδ).2 hr
  have hc := (isConvexShapeAt_struweSwitchLeaf_one (by linarith [hL.one_le]) hℓ' hr'
    (isConvexShapeAt_sqrtAddLeaf hL one_pos
      ⟨by linarith [hℓ'.1], by linarith [hℓ'.2]⟩ hr')).rescale hδ
  rwa [mul_div_cancel₀ r hδ.ne', ← struweSwitchLeaf_eq_mul_struweSwitchLeaf_one hδ] at hc

/-- **The leaves `struweSwitchLeaf` are `i`-convex shapes.** There is `L₀ ≥ 1` such that for every
`L ≥ L₀`, `δ > 0` and `ℓ ∈ [0, 7 δ]`, the leaf `struweSwitchLeaf L δ ℓ` is an `i`-convex shape at
every `r > δ`. -/
theorem exists_forall_isConvexShapeAt_struweSwitchLeaf :
    ∃ L₀, 1 ≤ L₀ ∧ ∀ L, L₀ ≤ L → ∀ δ, 0 < δ → ∀ ℓ ∈ Icc 0 (7 * δ), ∀ r, δ < r →
      IsConvexShapeAt (struweSwitchLeaf L δ ℓ) r := by
  obtain ⟨L₀, h⟩ := eventually_atTop.1 eventually_isCutoffScale
  exact ⟨max 1 L₀, le_max_left _ _, fun L hL δ hδ ℓ hℓ r hr ↦
    isConvexShapeAt_struweSwitchLeaf (h L (le_of_max_le_right hL)) hδ hℓ hr⟩

/-- At `ℓ = 6 δ`, Struwe's shape with value `2 ℓ - 47 δ / 8` at `δ` lies strictly below
`sqrtAddLeaf L δ ℓ` at every `r > δ`, for `0 ≤ L` and `0 < δ`. -/
private theorem struweShape_lt_sqrtAddLeaf_six_mul {L : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ) {r : ℝ}
    (hr : δ < r) : struweShape δ 1 (2 * (6 * δ) - 47 * δ / 8) r < sqrtAddLeaf L δ (6 * δ) r := by
  rw [sqrtAddLeaf_eq_mul_sqrtAddLeaf_one hδ, struweShape_eq_mul_struweShape_one hδ.ne']
  have hc : (2 * (6 * δ) - 47 * δ / 8) / δ = 2 * 6 - 47 / 8 := by field_simp
  have h6 : 6 * δ / δ = 6 := by field_simp
  rw [hc, h6]
  refine mul_lt_mul_of_pos_left ?_ hδ
  have hr' : 1 < r / δ := (one_lt_div hδ).2 hr
  rcases le_total (r / δ) 2 with h2 | h2
  · have h := (sqrtAddLeaf_sub_struweShape_mem_Icc hL 6 ⟨hr'.le, h2⟩).1
    have hw : 0 < √((r / δ) ^ 2 - 1) := sqrt_pos.2 (by nlinarith)
    have h8 : (0 : ℝ) < 8 - √2 := by
      nlinarith [sq_sqrt (zero_le_two : (0 : ℝ) ≤ 2), sqrt_nonneg 2]
    nlinarith [mul_pos h8 hw]
  · linarith [two_le_sqrtAddLeaf_sub_struweShape L (ℓ := 6) ⟨by norm_num, by norm_num⟩ h2]

/-- For `0 ≤ L` and `0 < δ`, the family `(ℓ, r) ↦ struweSwitchLeaf L δ ℓ r` is smooth at every
point with `δ < r`. Near `ℓ < 6 δ` it is `sqrtAddLeaf`; near `ℓ > 6 δ` it is a smoothed maximum
of smooth functions with positive width; near `ℓ = 6 δ` the leaf `sqrtAddLeaf L δ ℓ` exceeds
Struwe's shape by more than the width, so the family is again `sqrtAddLeaf`. -/
theorem contDiffAt_uncurry_struweSwitchLeaf {L : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ) {q : ℝ × ℝ}
    (hq : δ < q.2) : ContDiffAt ℝ ∞ (Function.uncurry (struweSwitchLeaf L δ)) q := by
  set A := Function.uncurry (sqrtAddLeaf L δ)
  set T := fun p : ℝ × ℝ ↦ struweShape δ 1 (2 * p.1 - 47 * δ / 8) p.2
  have hA : ContDiffAt ℝ ∞ A q := contDiffAt_uncurry_sqrtAddLeaf L hδ.le hq
  -- `T` is the joint Struwe shape composed with `(ℓ, r) ↦ (2 ℓ - 47 δ / 8, r)`.
  have hT : ContDiffAt ℝ ∞ T q :=
    ContDiffAt.comp (g := Function.uncurry (struweShape δ 1))
      (f := fun p : ℝ × ℝ ↦ (2 * p.1 - 47 * δ / 8, p.2)) q
      ((contDiffOn_uncurry_struweShape hδ le_rfl).contDiffAt
        ((isOpen_univ.prod isOpen_Ioi).mem_nhds ⟨trivial, hq⟩))
      (((contDiffAt_const.mul contDiffAt_fst).sub contDiffAt_const).prodMk contDiffAt_snd)
  obtain ⟨ℓ, r⟩ := q
  rcases lt_trichotomy ℓ (6 * δ) with hℓ | rfl | hℓ
  · -- Near `ℓ < 6 δ` the family is `sqrtAddLeaf`.
    refine hA.congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hℓ]
      with ⟨a, b⟩ (h : a < 6 * δ)
    simp only [Function.uncurry_apply_pair, A, struweSwitchLeaf_of_le h.le]
  · -- Near `ℓ = 6 δ` the leaf `sqrtAddLeaf` exceeds Struwe's shape by more than the width.
    have hpos : 0 < A (6 * δ, r) - T (6 * δ, r) - (6 * δ - 6 * δ) / 200 := by
      simp only [A, T, Function.uncurry_apply_pair, sub_self, zero_div, sub_zero, sub_pos]
      exact struweShape_lt_sqrtAddLeaf_six_mul hL hδ hq
    have hF : ContinuousAt (fun p : ℝ × ℝ ↦ A p - T p - (p.1 - 6 * δ) / 200) (6 * δ, r) :=
      (hA.continuousAt.sub hT.continuousAt).sub
        ((continuousAt_fst.sub continuousAt_const).div_const _)
    refine hA.congr_of_eventuallyEq ?_
    filter_upwards [hF.eventually (lt_mem_nhds hpos)] with ⟨a, b⟩ h
    simp only [A, T, Function.uncurry_apply_pair] at h ⊢
    rcases le_or_gt a (6 * δ) with ha | ha
    · rw [struweSwitchLeaf_of_le ha]
    · rw [struweSwitchLeaf_of_lt ha]
      exact smoothedMax_eq_left (div_pos (sub_pos.2 ha) (by norm_num)) (by linarith)
  · -- Near `ℓ > 6 δ` the family is a smoothed maximum of positive width.
    have hη : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ ↦ (p.1 - 6 * δ) / 200) (ℓ, r) :=
      (contDiffAt_fst.sub contDiffAt_const).div_const _
    refine (contDiffAt_smoothedMax hη (div_pos (sub_pos.2 hℓ) (by norm_num)).ne' hA
      hT).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hℓ]
      with ⟨a, b⟩ (h : 6 * δ < a)
    simp only [A, T, Function.uncurry_apply_pair, struweSwitchLeaf_of_lt h]

/-- For `0 ≤ L` and `0 < δ`, each leaf `struweSwitchLeaf L δ ℓ` is `Cⁿ` on `(δ, ∞)`. -/
theorem contDiffOn_struweSwitchLeaf {n : ℕ∞} {L : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ) (ℓ : ℝ) :
    ContDiffOn ℝ n (struweSwitchLeaf L δ ℓ) (Ioi δ) := fun r hr ↦
  ((contDiffAt_uncurry_struweSwitchLeaf hL hδ (q := (ℓ, r)) hr).uncurry_left.of_le
    (by exact_mod_cast le_top)).contDiffWithinAt

/-- For `0 ≤ δ`, at each `r > δ`, the leaves `ℓ ≥ 0` are strictly increasing in `ℓ`. Both
`sqrtAddLeaf L δ ℓ r` and Struwe's shape with value `2 ℓ - 47 δ / 8` at `δ` increase strictly
with `ℓ`; the smoothed maximum lies above the maximum, increases with its width, and increases
strictly when both of its arguments do. -/
theorem strictMonoOn_struweSwitchLeaf (L : ℝ) (hδ : 0 ≤ δ) {r : ℝ} (hr : δ < r) :
    StrictMonoOn (fun ℓ ↦ struweSwitchLeaf L δ ℓ r) (Ici 0) := by
  have hA := strictMonoOn_sqrtAddLeaf L hδ hr
  intro ℓ hℓ ℓ' hℓ' h
  rcases le_or_gt ℓ' (6 * δ) with h' | h'
  · simp only [struweSwitchLeaf_of_le (h.le.trans h'), struweSwitchLeaf_of_le h']
    exact hA hℓ hℓ' h
  have hη' : 0 < (ℓ' - 6 * δ) / 200 := div_pos (sub_pos.2 h') (by norm_num)
  simp only [struweSwitchLeaf_of_lt h']
  rcases le_or_gt ℓ (6 * δ) with h₀ | h₀
  · rw [struweSwitchLeaf_of_le h₀]
    exact (hA hℓ hℓ' h).trans_le ((le_max_left _ _).trans (max_le_smoothedMax hη' _ _))
  have hη : 0 < (ℓ - 6 * δ) / 200 := div_pos (sub_pos.2 h₀) (by norm_num)
  simp only [struweSwitchLeaf_of_lt h₀]
  have ha := hA hℓ hℓ' h
  set a := sqrtAddLeaf L δ ℓ r
  set a' := sqrtAddLeaf L δ ℓ' r
  set b := struweShape δ 1 (2 * ℓ - 47 * δ / 8) r
  have hb : struweShape δ 1 (2 * ℓ' - 47 * δ / 8) r = b + 2 * (ℓ' - ℓ) := by
    rw [show 2 * ℓ' - 47 * δ / 8 = 2 * (ℓ' - ℓ) + (2 * ℓ - 47 * δ / 8) by ring, struweShape_add,
      add_comm]
  rw [hb]
  set m := min (a' - a) (2 * (ℓ' - ℓ))
  have hm : 0 < m := lt_min (by linarith) (by linarith)
  calc smoothedMax ((ℓ - 6 * δ) / 200) a b ≤ smoothedMax ((ℓ' - 6 * δ) / 200) a b :=
        monotoneOn_smoothedMax_width a b hη hη' (by linarith)
    _ < smoothedMax ((ℓ' - 6 * δ) / 200) a b + m := lt_add_of_pos_right _ hm
    _ = smoothedMax ((ℓ' - 6 * δ) / 200) (a + m) (b + m) := (smoothedMax_add_add_right ..).symm
    _ ≤ smoothedMax ((ℓ' - 6 * δ) / 200) a' (b + 2 * (ℓ' - ℓ)) :=
        smoothedMax_le_smoothedMax (by linarith [min_le_left (a' - a) (2 * (ℓ' - ℓ))])
          (by linarith [min_le_right (a' - a) (2 * (ℓ' - ℓ))])

/-- **The leaves `ℓ ∈ [0, 7 δ]` of the family over the cylinder.** There is `L₀ ≥ 1` such that
for every `L ≥ L₀` and `δ > 0` the leaves `χ = struweSwitchLeaf L δ` satisfy:
* `χ` is smooth in `(ℓ, r)` at every point of `[0, 7 δ] × (δ, ∞)`;
* each leaf `χ ℓ`, `ℓ ∈ [0, 7 δ]`, is an `i`-convex shape at every `r > δ`, is continuous on
  `[δ, ∞)`, and its slope tends to `+∞` at `δ`;
* the leaf `0` is `sqrtAddLeaf L δ 0`, and from `2 δ` on the leaf `ℓ` is `sqrtAddLeaf L δ ℓ`;
* at each `r > δ` the leaves increase strictly with `ℓ ∈ [0, 7 δ]`;
* on `(δ, 257 δ / 256]` the leaf `7 δ` is Struwe's shape with value `65 δ / 8` at `δ`. -/
theorem exists_isConvexShapeAt_struweSwitchLeaf :
    ∃ L₀, 1 ≤ L₀ ∧ ∀ L, L₀ ≤ L → ∀ δ, 0 < δ →
      (∀ q ∈ Icc 0 (7 * δ) ×ˢ Ioi δ,
        ContDiffAt ℝ ∞ (Function.uncurry (struweSwitchLeaf L δ)) q) ∧
      (∀ ℓ ∈ Icc 0 (7 * δ), ∀ r, δ < r → IsConvexShapeAt (struweSwitchLeaf L δ ℓ) r) ∧
      (∀ ℓ ∈ Icc 0 (7 * δ), ContinuousOn (struweSwitchLeaf L δ ℓ) (Ici δ) ∧
        Tendsto (deriv (struweSwitchLeaf L δ ℓ)) (𝓝[>] δ) atTop) ∧
      struweSwitchLeaf L δ 0 = sqrtAddLeaf L δ 0 ∧
      (∀ ℓ ∈ Icc 0 (7 * δ), ∀ r, 2 * δ ≤ r →
        struweSwitchLeaf L δ ℓ r = sqrtAddLeaf L δ ℓ r) ∧
      (∀ r, δ < r → StrictMonoOn (fun ℓ ↦ struweSwitchLeaf L δ ℓ r) (Icc 0 (7 * δ))) ∧
      ∀ r ∈ Ioc δ (257 * δ / 256),
        struweSwitchLeaf L δ (7 * δ) r = struweShape δ 1 (65 * δ / 8) r := by
  obtain ⟨L₀, hL₀, hconv⟩ := exists_forall_isConvexShapeAt_struweSwitchLeaf
  refine ⟨L₀, hL₀, fun L hL δ hδ ↦ ?_⟩
  have hL' : 0 ≤ L := by linarith
  exact ⟨fun q hq ↦ contDiffAt_uncurry_struweSwitchLeaf hL' hδ hq.2, hconv L hL δ hδ,
    fun ℓ _ ↦ ⟨continuousOn_struweSwitchLeaf L hδ ℓ, tendsto_deriv_struweSwitchLeaf hL' hδ ℓ⟩,
    struweSwitchLeaf_of_le (by linarith),
    fun ℓ hℓ r hr ↦ struweSwitchLeaf_of_two_mul_le L hδ hℓ hr,
    fun r hr ↦ (strictMonoOn_struweSwitchLeaf L hδ.le hr).mono Icc_subset_Ici_self,
    fun r hr ↦ struweSwitchLeaf_seven_mul_of_mem_Ioc hL' hδ hr⟩

end SymplecticGeometry

end
