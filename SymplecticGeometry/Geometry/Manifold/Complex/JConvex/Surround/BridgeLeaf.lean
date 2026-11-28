/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.CutoffLeaf

import Mathlib.Analysis.Complex.ExponentialBounds
import SymplecticGeometry.Analysis.SpecialFunctions.Sqrt
import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.ConvexShape.SmoothedMax
import TauCeti.Analysis.Real.Sqrt

/-!
# The bridge leaves

The bridge leaves of Cieliebak and Eliashberg's family of §4.6 lie between the Struwe switch leaf
`7 δ` (`SymplecticGeometry.struweSwitchLeaf`) and the leaves of
`SymplecticGeometry.exists_convexShapeFamily_struweShape`. They are built under one fixed shape,
raised by a constant `t`: `SymplecticGeometry.struweLineShape δ`, the smoothed maximum of width
`δ / 4` of Struwe's shape `S = struweShape δ 4 0`, with value `0` at `4 δ`, and the line
`2 r - 8 δ`, which meet at `4 δ`.

* `S δ ∈ [-√30 δ, 0]` (`SymplecticGeometry.struweShape_four_zero_self_mem_Icc`), from the bound
  `struweShape_sub_struweShape_one_mem_Icc` on the rise of Struwe's shape near the cylinder.
* `S - (2 r - 8 δ) ≥ δ / 4` on `[δ, 7 δ / 2]`, since that difference is concave and at least
  `δ / 4` at both ends, and `2 r - 8 δ - S ≥ δ / 4` from `9 δ / 2` on, since the slope of `S` is
  at most `3 / 2` from `4 δ` on. So the shape is `S` on `[δ, 7 δ / 2]`
  (`SymplecticGeometry.struweLineShape_eq_struweShape`) and the line from `9 δ / 2` on
  (`SymplecticGeometry.struweLineShape_eq_linear`).
* `SymplecticGeometry.isConvexShapeAt_struweLineShape_add`: the raised shape
  `r ↦ struweLineShape δ r + t` is an `i`-convex shape at `r > δ` once it exceeds the two
  quantities of `isConvexShapeAt_struweShape_of_lt` by `2 δ` where `r ≤ 9 δ / 2`, and
  `r < 8 (t - 8 δ)` where `r ≥ 7 δ / 2`. On `[7 δ / 2, 9 δ / 2]` both pieces are `i`-convex
  shapes and `isConvexShapeAt_smoothedMax` applies; elsewhere the shape is one of the pieces
  near `r`.

Every bridge leaf is `SymplecticGeometry.bridgeLeaf δ η G t`, the smoothed maximum of width `η` of
a shape `G` and `r ↦ struweLineShape δ r + t`; it is `G` or the raised shape where one of them is
`η` above the other (`SymplecticGeometry.bridgeLeaf_eq_left`,
`SymplecticGeometry.bridgeLeaf_eq_right`).

* `SymplecticGeometry.isConvexShapeAt_bridgeLeaf_sqrtAddLeaf`: for `G = sqrtAddLeaf L δ ℓ` with
  `ℓ ∈ [7 δ, 15 δ / 2]` and `L` as in `isConvexShapeAt_sqrtAddLeaf`, `η = δ / 200` and
  `65 δ / 8 ≤ S δ + t`, the bridge leaf is an `i`-convex shape at every `r > δ`. Where the raised
  shape is used it is at least `G r - η`, which is at least `7 δ` up to `2 δ` and `8 r - 5 δ / 2`
  from there on; that gives the conditions of `isConvexShapeAt_struweLineShape_add`. Where the two
  pieces are within `η`, below `2 δ` the raised shape is at least `65 δ / 8` and `G` is
  `δ / 8 + ℓ + 8 w`, `w = √(r² - δ²)`, so `w ≥ δ / 40`, against slopes `8 r / w` and
  `√2 r / w` (`deriv_struweLineShape_of_lt`, `deriv_struweShape_le_sqrt_two_mul_div`); from
  `2 δ` on the slopes are at most `11` and `2`.
* `SymplecticGeometry.isConvexShapeAt_bridgeLeaf_sqrt`: for the standard leaf
  `G r = √(64 r² + ℓ²)`, `0 < η ≤ δ / 200` and `3 ℓ + 30 δ ≤ S δ + t`, the bridge leaf is an
  `i`-convex shape at every `r > δ`. Where the raised shape is used it is at least `30 δ`, and there
  `8 r ≤ G r ≤ 2 r + t + δ / 8 + η`, which gives `r < 8 (t - 8 δ)`; the two pieces are
  within `η` only beyond `7 δ / 2`, where their slopes are at most `8` and `2`
  (`SymplecticGeometry.isConvexShapeAt_smoothedMax_of_imp`).
* `SymplecticGeometry.bridgeLeaf_sqrtAddLeaf_eqOn_struweSwitchLeaf`: with
  `G = sqrtAddLeaf L δ (7 δ)`, `η = δ / 200` and `t = 65 δ / 8 - S δ`, the bridge leaf is
  `struweSwitchLeaf L δ (7 δ)` on `(δ, ∞)`. Up to `7 δ / 2` the raised shape is the Struwe
  shape of that leaf, since Struwe's shapes over one cylinder differ by constants; beyond,
  both leaves are `G`, which is at least `8 r - 3 δ` there, while the raised shape is at
  most `2 r + 14 δ`.
* `SymplecticGeometry.bridgeLeaf_sqrtAddLeaf_eqOn_sqrt`: once `3 ℓ + 8 (3 + L) δ ≤ S δ + t`, the
  cutoff region `r < (2 + L) δ` of `sqrtAddLeaf L δ ℓ` lies under the raised shape, so in the
  bridge leaf of width `δ / 200` the standard leaf may replace it.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  §4.6, Proposition 4.27.
-/

public section

noncomputable section

namespace SymplecticGeometry

open Real Set Filter Topology
open scoped ContDiff

variable {δ : ℝ}

/-! ### Bounds on Struwe's shape based at `4 δ` -/

/-- For `δ > 0` and `r ≥ 2 δ`, `2 / 3 ≤ √(log (r / δ))`. -/
private theorem two_div_three_le_sqrt_log (hδ : 0 < δ) {r : ℝ} (hr : 2 * δ ≤ r) :
    2 / 3 ≤ √(log (r / δ)) := by
  refine le_sqrt_of_sq_le ?_
  have h2 : (2 : ℝ) ≤ r / δ := (le_div_iff₀ hδ).2 (by linarith)
  have := log_le_log two_pos h2
  linarith [log_two_gt_d9]

/-- For `δ > 0` and `δ < r ≤ 9 δ / 2`, `√(log (r / δ)) ≤ 71 / 50`, since `log (r / δ) ≤ 2`. -/
private theorem sqrt_log_le_of_le (hδ : 0 < δ) {r : ℝ} (hr : δ < r) (hr₉ : r ≤ 9 * δ / 2) :
    √(log (r / δ)) ≤ 71 / 50 := by
  have hl : log (r / δ) ≤ 2 := by
    rw [log_le_iff_le_exp (div_pos (hδ.trans hr) hδ), div_le_iff₀ hδ]
    nlinarith [quadratic_le_exp_of_nonneg (zero_le_two : (0 : ℝ) ≤ 2)]
  rw [sqrt_le_left (by norm_num)]
  linarith

/-- For `δ > 0`, Struwe's shape with value `0` at `4 δ` takes at `δ` a value in `[-√30 δ, 0]`: it
rises by at most `√2 √(4² - 1) δ = √30 δ` from `δ` to `4 δ`. -/
theorem struweShape_four_zero_self_mem_Icc (hδ : 0 < δ) :
    struweShape δ 4 0 δ ∈ Icc (-(√30 * δ)) 0 := by
  have e := congrFun (struweShape_eq_mul_struweShape_one hδ.ne' 4 0) δ
  rw [zero_div, div_self hδ.ne'] at e
  have h := struweShape_sub_struweShape_one_mem_Icc (by norm_num : (1 : ℝ) ≤ 4) 0
    (by norm_num : (1 : ℝ) ≤ 4)
  have h4 : struweShape 1 4 0 4 = 0 := by simpa using struweShape_apply_mul 1 4 0
  rw [h4, ← sqrt_mul zero_le_two] at h
  norm_num at h
  rw [e]
  constructor <;> nlinarith [h.1, h.2]

/-- For `δ > 0`, Struwe's shape with value `0` at `4 δ` is at least `-3 δ / 4` at `7 δ / 2`. -/
private theorem neg_le_struweShape_four_zero (hδ : 0 < δ) :
    -(3 * δ / 4) ≤ struweShape δ 4 0 (7 * δ / 2) := by
  have h := struweShape_sub_struweShape_le hδ (by norm_num : (1 : ℝ) ≤ 4) 0
    (by linarith : δ < 7 * δ / 2) (by linarith : 7 * δ / 2 ≤ 4 * δ)
  rw [struweShape_apply_mul] at h
  have hs := two_div_three_le_sqrt_log hδ (by linarith : 2 * δ ≤ 7 * δ / 2)
  have : (4 * δ - 7 * δ / 2) / √(log (7 * δ / 2 / δ)) ≤ (4 * δ - 7 * δ / 2) / (2 / 3) :=
    div_le_div_of_nonneg_left (by linarith) (by norm_num) hs
  linarith

/-- For `δ > 0` and `r ≥ 4 δ`, Struwe's shape with value `0` at `4 δ` is at most
`3 / 2 (r - 4 δ)`. -/
private theorem struweShape_four_zero_le (hδ : 0 < δ) {r : ℝ} (hr : 4 * δ ≤ r) :
    struweShape δ 4 0 r ≤ 3 / 2 * (r - 4 * δ) := by
  have h := struweShape_sub_struweShape_le hδ (by norm_num : (1 : ℝ) ≤ 4) 0
    (by linarith : δ < 4 * δ) hr
  rw [struweShape_apply_mul, sub_zero] at h
  have hs := two_div_three_le_sqrt_log hδ (by linarith : 2 * δ ≤ 4 * δ)
  have : (r - 4 * δ) / √(log (4 * δ / δ)) ≤ (r - 4 * δ) / (2 / 3) :=
    div_le_div_of_nonneg_left (by linarith) (by norm_num) hs
  linarith

/-- For `δ > 0` and `r ≥ 2 δ`, the slope of Struwe's shape based at `4 δ` is at most `3 / 2`. -/
private theorem deriv_struweShape_four_zero_le (hδ : 0 < δ) {r : ℝ} (hr : 2 * δ ≤ r) :
    deriv (struweShape δ 4 0) r ≤ 3 / 2 := by
  rw [deriv_struweShape hδ (by norm_num) 0 (by linarith)]
  have hs := two_div_three_le_sqrt_log hδ hr
  calc 1 / √(log (r / δ)) ≤ 1 / (2 / 3) := one_div_le_one_div_of_le (by norm_num) hs
    _ = 3 / 2 := by norm_num

/-- For `δ > 0`, Struwe's shape based at `4 δ` exceeds the line `2 r - 8 δ` by at least `δ / 4`
on `[δ, 7 δ / 2]`: the difference is concave, and at least `δ / 4` at both ends. -/
private theorem linear_add_le_struweShape (hδ : 0 < δ) {r : ℝ} (hr : r ∈ Icc δ (7 * δ / 2)) :
    2 * r - 8 * δ + δ / 4 ≤ struweShape δ 4 0 r := by
  have hc : ConcaveOn ℝ (Ici δ) (fun x ↦ struweShape δ 4 0 x - (2 * x - 8 * δ)) :=
    (strictConcaveOn_struweShape hδ (by norm_num) 0).concaveOn.sub
      (convexOn_id (convex_Ici δ) |>.smul (by norm_num : (0 : ℝ) ≤ 2) |>.sub
        (concaveOn_const _ (convex_Ici δ)))
  have h := hc.ge_on_segment (x := δ) (y := 7 * δ / 2) self_mem_Ici
    (mem_Ici.2 (by linarith)) (by rw [segment_eq_Icc (by linarith)]; exact hr)
  have h₁ := (struweShape_four_zero_self_mem_Icc hδ).1
  have h₂ := neg_le_struweShape_four_zero hδ
  have h30 : √30 ≤ 23 / 4 := by rw [sqrt_le_left (by norm_num)]; norm_num
  have hm : δ / 4 ≤ min (struweShape δ 4 0 δ - (2 * δ - 8 * δ))
      (struweShape δ 4 0 (7 * δ / 2) - (2 * (7 * δ / 2) - 8 * δ)) :=
    le_min (by nlinarith) (by linarith)
  linarith

/-- For `δ > 0`, the line `2 r - 8 δ` exceeds Struwe's shape based at `4 δ` by at least `δ / 4`
from `9 δ / 2` on. -/
private theorem struweShape_add_le_linear (hδ : 0 < δ) {r : ℝ} (hr : 9 * δ / 2 ≤ r) :
    struweShape δ 4 0 r + δ / 4 ≤ 2 * r - 8 * δ := by
  linarith [struweShape_four_zero_le hδ (by linarith : 4 * δ ≤ r)]

/-- For `δ > 0` and `r ≥ 7 δ / 2`, the line `2 r - 8 δ` exceeds Struwe's shape based at `4 δ`
by at most `7 δ / 4` up to `9 δ / 2`. -/
private theorem linear_le_struweShape_add (hδ : 0 < δ) {r : ℝ}
    (hr : r ∈ Icc (7 * δ / 2) (9 * δ / 2)) :
    2 * r - 8 * δ ≤ struweShape δ 4 0 r + 7 * δ / 4 := by
  have hm := (strictMonoOn_struweShape hδ (by norm_num : (1 : ℝ) ≤ 4) 0).monotoneOn
    (mem_Ici.2 (by linarith : δ ≤ 7 * δ / 2)) (mem_Ici.2 (by linarith [hr.1])) hr.1
  linarith [neg_le_struweShape_four_zero hδ, hr.2]

/-! ### The raised Struwe/line shape -/

/-- **The Struwe/line shape** over the cylinder of radius `δ`: the smoothed maximum, of width
`δ / 4`, of Struwe's shape with value `0` at `4 δ` and the line `2 r - 8 δ`. For `δ > 0` it is
Struwe's shape on `[δ, 7 δ / 2]` and the line from `9 δ / 2` on. -/
def struweLineShape (δ r : ℝ) : ℝ :=
  smoothedMax (δ / 4) (struweShape δ 4 0 r) (2 * r - 8 * δ)

theorem struweLineShape_def (δ r : ℝ) :
    struweLineShape δ r = smoothedMax (δ / 4) (struweShape δ 4 0 r) (2 * r - 8 * δ) :=
  (rfl)

/-- For `δ > 0`, the Struwe/line shape is Struwe's shape with value `0` at `4 δ` on
`[δ, 7 δ / 2]`. -/
theorem struweLineShape_eq_struweShape (hδ : 0 < δ) {r : ℝ} (hr : r ∈ Icc δ (7 * δ / 2)) :
    struweLineShape δ r = struweShape δ 4 0 r := by
  rw [struweLineShape_def]
  exact smoothedMax_eq_left (by positivity) (linear_add_le_struweShape hδ hr)

/-- For `δ > 0`, the Struwe/line shape is the line `2 r - 8 δ` from `9 δ / 2` on. -/
theorem struweLineShape_eq_linear (hδ : 0 < δ) {r : ℝ} (hr : 9 * δ / 2 ≤ r) :
    struweLineShape δ r = 2 * r - 8 * δ := by
  rw [struweLineShape_def]
  exact smoothedMax_eq_right (by positivity) (struweShape_add_le_linear hδ hr)

/-- For `δ > 0`, the Struwe/line shape is smooth on `(δ, ∞)`. -/
theorem contDiffOn_struweLineShape (hδ : 0 < δ) :
    ContDiffOn ℝ ∞ (struweLineShape δ) (Ioi δ) := by
  have h : ContDiffOn ℝ ∞ (fun r ↦ (struweShape δ 4 0 r, 2 * r - 8 * δ)) (Ioi δ) :=
    (contDiffOn_struweShape hδ (by norm_num) 0).prodMk (by fun_prop)
  exact (contDiff_smoothedMax (δ / 4)).comp_contDiffOn h

/-- For `δ > 0`, the Struwe/line shape lies above Struwe's shape with value `0` at `4 δ`. -/
theorem struweShape_le_struweLineShape (hδ : 0 < δ) (r : ℝ) :
    struweShape δ 4 0 r ≤ struweLineShape δ r := by
  rw [struweLineShape_def]
  exact (le_max_left _ _).trans (max_le_smoothedMax (by positivity) _ _)

/-- For `δ > 0`, the Struwe/line shape exceeds the larger of its two pieces by at most `δ / 8`. -/
theorem struweLineShape_le (hδ : 0 < δ) (r : ℝ) :
    struweLineShape δ r ≤ max (struweShape δ 4 0 r) (2 * r - 8 * δ) + δ / 8 := by
  rw [struweLineShape_def]
  linarith [smoothedMax_le_max_add (by positivity : 0 < δ / 4) (struweShape δ 4 0 r)
    (2 * r - 8 * δ)]

/-- For `δ > 0` and `r ≥ δ`, Struwe's shape based at `4 δ` is at most `2 r`. -/
private theorem struweShape_four_zero_le_two_mul (hδ : 0 < δ) {r : ℝ} (hr : δ ≤ r) :
    struweShape δ 4 0 r ≤ 2 * r := by
  rcases le_total r (4 * δ) with h | h
  · have hm := (strictMonoOn_struweShape hδ (by norm_num : (1 : ℝ) ≤ 4) 0).monotoneOn
      (mem_Ici.2 hr) (mem_Ici.2 (by linarith)) h
    rw [struweShape_apply_mul] at hm
    linarith
  · linarith [struweShape_four_zero_le hδ h]

/-- For `δ > 0` and `r ≥ δ`, the Struwe/line shape is at most `2 r + δ / 8`. -/
theorem struweLineShape_le_two_mul_add (hδ : 0 < δ) {r : ℝ} (hr : δ ≤ r) :
    struweLineShape δ r ≤ 2 * r + δ / 8 := by
  have h := struweLineShape_le hδ r
  have : max (struweShape δ 4 0 r) (2 * r - 8 * δ) ≤ 2 * r :=
    max_le (struweShape_four_zero_le_two_mul hδ hr) (by linarith)
  linarith

/-- For `δ > 0`, the slope of the Struwe/line shape is at most `2` from `2 δ` on. -/
theorem deriv_struweLineShape_le (hδ : 0 < δ) {r : ℝ} (hr : 2 * δ ≤ r) :
    deriv (struweLineShape δ) r ≤ 2 := by
  have hS : DifferentiableAt ℝ (struweShape δ 4 0) r :=
    (hasDerivAt_struweShape hδ (by norm_num) 0 (by linarith)).differentiableAt
  have hl : HasDerivAt (fun x ↦ 2 * x - 8 * δ) 2 r := by
    simpa using ((hasDerivAt_id r).const_mul 2).sub_const (8 * δ)
  have h := deriv_smoothedMax_le_max (δ := δ / 4) hS hl.differentiableAt
  rw [hl.deriv] at h
  rw [show struweLineShape δ = _ from funext (struweLineShape_def δ)]
  refine h.trans (max_le ?_ le_rfl)
  linarith [deriv_struweShape_four_zero_le hδ hr]

/-- For `δ > 0`, the slope of the Struwe/line shape on `(δ, 7 δ / 2)` is the Struwe slope
`1 / √(log (r / δ))`. -/
theorem deriv_struweLineShape_of_lt (hδ : 0 < δ) {r : ℝ} (hr : δ < r) (hr₇ : r < 7 * δ / 2) :
    deriv (struweLineShape δ) r = 1 / √(log (r / δ)) := by
  rw [← deriv_struweShape hδ (by norm_num : (1 : ℝ) ≤ 4) 0 hr]
  refine EventuallyEq.deriv_eq ?_
  filter_upwards [Ioo_mem_nhds hr hr₇] with x hx
  exact struweLineShape_eq_struweShape hδ ⟨hx.1.le, hx.2.le⟩

/-- **The raised Struwe/line shape is an `i`-convex shape.** Let `δ > 0`, `r > δ` and `t` be such
that, with `L = log (r / δ)`, `struweLineShape δ r + t` exceeds `r √L + 2 δ` and
`2 r √L³ + 2 δ` if `r ≤ 9 δ / 2`, and `r < 8 (t - 8 δ)` if `7 δ / 2 ≤ r`. Then
`r ↦ struweLineShape δ r + t` is an `i`-convex shape at `r`. -/
theorem isConvexShapeAt_struweLineShape_add (hδ : 0 < δ) {t r : ℝ} (hr : δ < r)
    (h₁ : r ≤ 9 * δ / 2 → r * √(log (r / δ)) + 2 * δ < struweLineShape δ r + t)
    (h₂ : r ≤ 9 * δ / 2 → 2 * r * √(log (r / δ)) ^ 3 + 2 * δ < struweLineShape δ r + t)
    (h₃ : 7 * δ / 2 ≤ r → r < 8 * (t - 8 * δ)) :
    IsConvexShapeAt (fun r ↦ struweLineShape δ r + t) r := by
  have hr₀ : 0 < r := hδ.trans hr
  have hT : ∀ x, struweShape δ 4 0 x + t = struweShape δ 4 t x := fun x ↦ by
    rw [← add_zero t, struweShape_add, add_comm, add_zero]
  have hl : ∀ x, 2 * x - 8 * δ + t = t - 8 * δ + 2 * x := fun x ↦ by ring
  -- Struwe's shape raised by `t` is an `i`-convex shape at `r ≤ 9 δ / 2`, with `2 δ` to spare
  -- when `struweLineShape δ r` is within `2 δ` of it.
  have hTc : r ≤ 9 * δ / 2 → struweLineShape δ r < struweShape δ 4 0 r + 2 * δ →
      IsConvexShapeAt (struweShape δ 4 t) r := fun hr₉ hle ↦
    isConvexShapeAt_struweShape_of_lt hδ (by norm_num) hr (by linarith [hT r, h₁ hr₉])
      (by linarith [hT r, h₂ hr₉])
  -- The raised line is an `i`-convex shape at `r ≥ 7 δ / 2`.
  have hLc : 7 * δ / 2 ≤ r → IsConvexShapeAt (fun x ↦ t - 8 * δ + 2 * x) r := fun hr₇ ↦ by
    have h := h₃ hr₇
    exact isConvexShapeAt_linear (by linarith) two_pos ⟨hr₀, by linarith⟩
  rcases lt_or_ge r (7 * δ / 2) with hr₇ | hr₇
  · -- Near `r < 7 δ / 2` the shape is Struwe's.
    have hS := struweLineShape_eq_struweShape hδ ⟨hr.le, hr₇.le⟩
    refine (hTc (by linarith) (by linarith)).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hr hr₇] with x hx
    rw [struweLineShape_eq_struweShape hδ ⟨hx.1.le, hx.2.le⟩, hT]
  rcases lt_or_ge (9 * δ / 2) r with hr₉ | hr₉
  · -- Near `r > 9 δ / 2` the shape is the line.
    refine (hLc hr₇).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hr₉] with x hx
    rw [struweLineShape_eq_linear hδ (le_of_lt hx), hl]
  -- On `[7 δ / 2, 9 δ / 2]`, the smoothed maximum of two `i`-convex shapes.
  have e : (fun x ↦ struweLineShape δ x + t) =
      fun x ↦ smoothedMax (δ / 4) (struweShape δ 4 t x) (t - 8 * δ + 2 * x) := by
    ext x
    rw [struweLineShape_def, ← smoothedMax_add_add_right, hT, hl]
  have hle : struweLineShape δ r < struweShape δ 4 0 r + 2 * δ := by
    have h := struweLineShape_le hδ r
    have h' := linear_le_struweShape_add hδ ⟨hr₇, hr₉⟩
    have : max (struweShape δ 4 0 r) (2 * r - 8 * δ) ≤ struweShape δ 4 0 r + 7 * δ / 4 :=
      max_le (by linarith) h'
    linarith
  have hd : deriv (struweShape δ 4 t) r ≤ 3 / 2 := by
    rw [← funext hT]
    rw [deriv_add_const]
    exact deriv_struweShape_four_zero_le hδ (by linarith)
  have hdl : deriv (fun x ↦ t - 8 * δ + 2 * x) r = 2 := by
    simp
  rw [e]
  refine isConvexShapeAt_smoothedMax
    (((contDiffOn_struweShape hδ (by norm_num) t).contDiffAt (Ioi_mem_nhds hr)).of_le
      (by simp))
    (by fun_prop) (by positivity) (hTc hr₉ hle) (hLc hr₇) ?_
  rw [hdl]
  nlinarith

/-! ### The bridge leaves -/

/-- **The bridge leaf** over the cylinder of radius `δ`: the smoothed maximum, of width `η`, of a
shape `G` and the Struwe/line shape raised by `t`. Every stage of the bridge is of this form, for
its own `G`, `η` and `t`. -/
def bridgeLeaf (δ η : ℝ) (G : ℝ → ℝ) (t r : ℝ) : ℝ :=
  smoothedMax η (G r) (struweLineShape δ r + t)

theorem bridgeLeaf_def (δ η : ℝ) (G : ℝ → ℝ) (t r : ℝ) :
    bridgeLeaf δ η G t r = smoothedMax η (G r) (struweLineShape δ r + t) :=
  (rfl)

/-- For `η > 0`, the bridge leaf is `G` at a radius where the raised Struwe/line shape lies at
least `η` below `G`. -/
theorem bridgeLeaf_eq_left {η : ℝ} (hη : 0 < η) {G : ℝ → ℝ} {t r : ℝ}
    (h : struweLineShape δ r + t + η ≤ G r) : bridgeLeaf δ η G t r = G r := by
  rw [bridgeLeaf_def]
  exact smoothedMax_eq_left hη h

/-- For `η > 0`, the bridge leaf is the raised Struwe/line shape at a radius where `G` lies at
least `η` below it. -/
theorem bridgeLeaf_eq_right {η : ℝ} (hη : 0 < η) {G : ℝ → ℝ} {t r : ℝ}
    (h : G r + η ≤ struweLineShape δ r + t) :
    bridgeLeaf δ η G t r = struweLineShape δ r + t := by
  rw [bridgeLeaf_def]
  exact smoothedMax_eq_right hη h

/-- For `δ > 0` and `G` of class `Cⁿ` on `(δ, ∞)`, the bridge leaf is of class `Cⁿ` on
`(δ, ∞)`. -/
theorem contDiffOn_bridgeLeaf {n : ℕ∞} (hδ : 0 < δ) (η : ℝ) {G : ℝ → ℝ}
    (hG : ContDiffOn ℝ n G (Ioi δ)) (t : ℝ) : ContDiffOn ℝ n (bridgeLeaf δ η G t) (Ioi δ) := by
  have hS : ContDiffOn ℝ n (struweLineShape δ) (Ioi δ) :=
    (contDiffOn_struweLineShape hδ).of_le (by exact_mod_cast le_top)
  have h : ContDiffOn ℝ n (fun r ↦ (G r, struweLineShape δ r + t)) (Ioi δ) :=
    hG.prodMk (hS.add contDiffOn_const)
  exact (contDiff_smoothedMax η).comp_contDiffOn h

/-- **The first bridge stage.** Let `δ > 0`, `ℓ ∈ [7 δ, 15 δ / 2]` and `t ≥ 65 δ / 8 - S δ`,
where `S = struweShape δ 4 0`. Then the bridge leaf of width `δ / 200` of `sqrtAddLeaf L δ ℓ` and
the Struwe/line shape raised by `t` is an `i`-convex shape at every `r > δ`, once `L ≥ 1` is large
compared with bounds `A` of `smoothTransition'`, `B` of `smoothTransition''` and `M` of
`x smoothTransition'' x`. -/
theorem isConvexShapeAt_bridgeLeaf_sqrtAddLeaf {A B M L ℓ t r : ℝ}
    (hA : ∀ x, |deriv smoothTransition x| ≤ A)
    (hB : ∀ x, |deriv (deriv smoothTransition) x| ≤ B)
    (hM : ∀ x, |x * deriv (deriv smoothTransition) x| ≤ M)
    (hL₁ : 1 ≤ L) (hL : 1024 * (A + 2 * B + M) ≤ L) (hδ : 0 < δ)
    (hℓ : ℓ ∈ Icc (7 * δ) (15 * δ / 2)) (ht : 65 * δ / 8 - struweShape δ 4 0 δ ≤ t)
    (hr : δ < r) : IsConvexShapeAt (bridgeLeaf δ (δ / 200) (sqrtAddLeaf L δ ℓ) t) r := by
  obtain ⟨hℓ₇, hℓ₁₅⟩ := hℓ
  have hr₀ : 0 < r := hδ.trans hr
  have hη : (0 : ℝ) < δ / 200 := by positivity
  have hAc : ContDiffAt ℝ 2 (sqrtAddLeaf L δ ℓ) r :=
    ((contDiffOn_sqrtAddLeaf L hδ.le ℓ).contDiffAt (Ioi_mem_nhds hr)).of_le (by simp)
  have hPc : ContDiffAt ℝ 2 (fun x ↦ struweLineShape δ x + t) r :=
    (((contDiffOn_struweLineShape hδ).contDiffAt (Ioi_mem_nhds hr)).of_le (by simp)).add
      contDiffAt_const
  set w := √(r ^ 2 - δ ^ 2)
  have hw₀ : 0 < w := sqrt_pos.2 (by nlinarith)
  -- The leaf `A = sqrtAddLeaf L δ ℓ` is at least `8 w`, and `δ / 8 + ℓ + 8 w` up to `2 δ`; from
  -- `2 δ` on, `8 w ≥ 8 r - 5 δ / 2`.
  have hA8 := eight_mul_sqrt_le_sqrtAddLeaf L hδ.le (by linarith : 0 ≤ ℓ) r
  have hA₂ : r ≤ 2 * δ → sqrtAddLeaf L δ ℓ r = 8 * w + (δ / 8 + ℓ) :=
    sqrtAddLeaf_eq_eight_mul_sqrt_add_of_le (by linarith) hδ.le
  have hw₂ : 2 * δ ≤ r → 8 * r - 5 * δ / 2 ≤ 8 * w := fun h ↦ by
    have : r - 5 * δ / 16 ≤ w := le_sqrt_of_sq_le (by nlinarith)
    linarith
  rw [show bridgeLeaf δ (δ / 200) (sqrtAddLeaf L δ ℓ) t = _ from
    funext (bridgeLeaf_def δ (δ / 200) _ t)]
  refine isConvexShapeAt_smoothedMax_of_imp hAc hPc hη
    (fun _ ↦ isConvexShapeAt_sqrtAddLeaf hA hB hM hL₁ hL hδ ⟨by linarith, hℓ₁₅⟩ hr)
    (fun h ↦ ?_) (fun h ↦ ?_)
  · -- Where the raised Struwe/line shape is used, it is high enough to be an `i`-convex shape.
    have hs₀ : 0 ≤ √(log (r / δ)) := sqrt_nonneg _
    have hH : r ≤ 9 * δ / 2 → r * √(log (r / δ)) + 2 * δ < struweLineShape δ r + t ∧
        2 * r * √(log (r / δ)) ^ 3 + 2 * δ < struweLineShape δ r + t := fun hr₉ ↦ by
      rcases le_total r (2 * δ) with h2 | h2
      · -- Up to `2 δ`, `√(log (r / δ)) ≤ 1` and the leaf is at least `δ / 8 + ℓ ≥ 7 δ`.
        have hs : √(log (r / δ)) ≤ 1 := by
          refine sqrt_le_one.2 ((log_le_sub_one_of_pos (div_pos hr₀ hδ)).trans ?_)
          rw [sub_le_iff_le_add, div_le_iff₀ hδ]
          linarith
        have h3 : √(log (r / δ)) ^ 3 ≤ 1 := pow_le_one₀ hs₀ hs
        have e₁ : r * √(log (r / δ)) ≤ r := mul_le_of_le_one_right hr₀.le hs
        have e₂ : 2 * r * √(log (r / δ)) ^ 3 ≤ 2 * r :=
          mul_le_of_le_one_right (by positivity) h3
        have := hA₂ h2
        constructor <;> nlinarith
      · -- From `2 δ` on, `√(log (r / δ)) ≤ 71 / 50` and the leaf is at least `8 r - 5 δ / 2`.
        have hs := sqrt_log_le_of_le hδ hr hr₉
        have h3 : √(log (r / δ)) ^ 3 ≤ (71 / 50) ^ 3 := pow_le_pow_left₀ hs₀ hs 3
        have e₁ : r * √(log (r / δ)) ≤ r * (71 / 50) :=
          mul_le_mul_of_nonneg_left hs hr₀.le
        have e₂ : 2 * r * √(log (r / δ)) ^ 3 ≤ 2 * r * (71 / 50) ^ 3 :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
        have := hw₂ h2
        constructor <;> nlinarith
    refine isConvexShapeAt_struweLineShape_add hδ hr (fun hr₉ ↦ (hH hr₉).1)
      (fun hr₉ ↦ (hH hr₉).2) (fun hr₇ ↦ ?_)
    -- Beyond `7 δ / 2`, `8 r - 5 δ / 2 ≤ A ≤ 2 r + δ / 8 + t + δ / 200` makes `t` large.
    have := hw₂ (by linarith)
    have := struweLineShape_le_two_mul_add hδ hr.le
    linarith
  · -- The width condition where the two pieces are within `δ / 200` of each other.
    obtain ⟨h₁, -⟩ := abs_le.1 h
    rcases lt_or_ge r (2 * δ) with h2 | h2
    · -- Below `2 δ`, the slopes are at most `8 r / w` and `√2 r / w`, and `w ≥ δ / 40`.
      have hdA : deriv (sqrtAddLeaf L δ ℓ) r = 8 * r / w :=
        deriv_sqrtAddLeaf_of_lt (by linarith) hδ.le hr h2
      have hdP : deriv (fun x ↦ struweLineShape δ x + t) r ≤ √2 * r / w := by
        rw [deriv_add_const, deriv_struweLineShape_of_lt hδ hr (by linarith),
          ← deriv_struweShape hδ (by norm_num : (1 : ℝ) ≤ 4) 0 hr]
        exact deriv_struweShape_le_sqrt_two_mul_div hδ (by norm_num) 0 hr
      -- `P r ≥ S δ + t ≥ 65 δ / 8`, so `A r ≥ P r - δ / 200` gives `w ≥ δ / 40`.
      have hSr := (strictMonoOn_struweShape hδ (by norm_num : (1 : ℝ) ≤ 4) 0).monotoneOn
        self_mem_Ici (mem_Ici.2 hr.le) hr.le
      have hP := struweShape_le_struweLineShape hδ r
      have hwδ : δ / 40 ≤ w := by linarith [hA₂ h2.le]
      have h2' : √2 < 2 := by rw [sqrt_lt' two_pos]; norm_num
      calc δ / 200 * (deriv (sqrtAddLeaf L δ ℓ) r + deriv (fun x ↦ struweLineShape δ x + t) r)
          ≤ δ / 200 * (8 * r / w + √2 * r / w) := by rw [hdA]; gcongr
        _ = δ / 40 * ((8 + √2) / 5 * r) / w := by ring
        _ ≤ w * (2 * r) / w := by
          gcongr
          nlinarith
        _ = 2 * r := by field_simp
    · -- From `2 δ` on, the slopes are at most `11` and `2`.
      have hdA := deriv_sqrtAddLeaf_le hA hB hM hL₁ hL hδ ⟨by linarith, hℓ₁₅⟩ h2
      have hdP : deriv (fun x ↦ struweLineShape δ x + t) r ≤ 2 := by
        rw [deriv_add_const]
        exact deriv_struweLineShape_le hδ h2
      have : δ / 200 * (deriv (sqrtAddLeaf L δ ℓ) r +
          deriv (fun x ↦ struweLineShape δ x + t) r) ≤ δ / 200 * 13 :=
        mul_le_mul_of_nonneg_left (by linarith) hη.le
      linarith

/-- **The second bridge stage.** Let `δ > 0`, `ℓ ≥ 0`, `0 < η ≤ δ / 200`, and `t` with
`3 ℓ + 30 δ ≤ S δ + t`, where `S = struweShape δ 4 0`. Then the bridge leaf of the standard leaf
`r ↦ √(64 r² + ℓ²)` and the Struwe/line shape raised by `t` is an `i`-convex shape at every
`r > δ`. -/
theorem isConvexShapeAt_bridgeLeaf_sqrt (hδ : 0 < δ) {ℓ η t r : ℝ} (hℓ : 0 ≤ ℓ)
    (hη : η ∈ Ioc 0 (δ / 200)) (ht : 3 * ℓ + 30 * δ ≤ struweShape δ 4 0 δ + t) (hr : δ < r) :
    IsConvexShapeAt (bridgeLeaf δ η (fun r ↦ √(64 * r ^ 2 + ℓ ^ 2)) t) r := by
  obtain ⟨hη₀, hη₁⟩ := hη
  have hr₀ : 0 < r := hδ.trans hr
  have hQe : (fun x ↦ √(64 * x ^ 2 + ℓ ^ 2)) = fun x ↦ √(64 * x ^ 2 - -ℓ ^ 2) := by
    simp only [sub_neg_eq_add]
  have hpos : 0 < 64 * r ^ 2 - -ℓ ^ 2 := by nlinarith [sq_nonneg ℓ]
  have hQc : ContDiffAt ℝ 2 (fun x ↦ √(64 * x ^ 2 + ℓ ^ 2)) r := by
    rw [hQe]
    exact (by fun_prop : ContDiffAt ℝ 2 (fun x ↦ 64 * x ^ 2 - -ℓ ^ 2) r).sqrt hpos.ne'
  have hS2 : ContDiffAt ℝ 2 (struweLineShape δ) r :=
    ((contDiffOn_struweLineShape hδ).contDiffAt (Ioi_mem_nhds hr)).of_le (by simp)
  have hPc : ContDiffAt ℝ 2 (fun x ↦ struweLineShape δ x + t) r :=
    hS2.add contDiffAt_const
  -- The standard leaf lies between `8 r` and `8 r + ℓ`, with slope at most `8`.
  have hQ8 : 8 * r ≤ √(64 * r ^ 2 + ℓ ^ 2) := le_sqrt_of_sq_le (by nlinarith [sq_nonneg ℓ])
  have hQle : √(64 * r ^ 2 + ℓ ^ 2) ≤ 8 * r + ℓ :=
    (sqrt_le_left (by positivity)).2 (by nlinarith)
  have hdQ : deriv (fun x ↦ √(64 * x ^ 2 + ℓ ^ 2)) r ≤ 8 := by
    rw [hQe, deriv_sqrt_sub hpos.ne', sub_neg_eq_add, div_le_iff₀ (by linarith)]
    linarith
  -- The raised Struwe/line shape lies between `3 ℓ + 30 δ` and `2 r + δ / 8 + t`.
  have hSδ := (struweShape_four_zero_self_mem_Icc hδ).2
  have hSr := (strictMonoOn_struweShape hδ (by norm_num : (1 : ℝ) ≤ 4) 0).monotoneOn
    self_mem_Ici (mem_Ici.2 hr.le) hr.le
  have hP30 : 3 * ℓ + 30 * δ ≤ struweLineShape δ r + t := by
    linarith [struweShape_le_struweLineShape hδ r]
  have hPle : struweLineShape δ r + t ≤ 2 * r + δ / 8 + t := by
    linarith [struweLineShape_le_two_mul_add hδ hr.le]
  rw [show bridgeLeaf δ η (fun r ↦ √(64 * r ^ 2 + ℓ ^ 2)) t = _ from
    funext (bridgeLeaf_def δ η _ t)]
  refine isConvexShapeAt_smoothedMax_of_imp hQc hPc hη₀ (fun _ ↦ ?_) (fun h ↦ ?_) (fun h ↦ ?_)
  · rw [show (fun x ↦ √(64 * x ^ 2 + ℓ ^ 2)) = fun x ↦ √(ℓ ^ 2 + 64 * x ^ 2) from
      funext fun x ↦ by rw [add_comm]]
    exact isConvexShapeAt_sqrt (by norm_num) hr₀
  · -- Where the raised Struwe/line shape is used, it is high enough to be an `i`-convex shape.
    have hlog : r ≤ 9 * δ / 2 → √(log (r / δ)) ≤ 71 / 50 := sqrt_log_le_of_le hδ hr
    refine isConvexShapeAt_struweLineShape_add hδ hr (fun hr₉ ↦ ?_) (fun hr₉ ↦ ?_) (fun _ ↦ ?_)
    · have : r * √(log (r / δ)) ≤ 9 * δ / 2 * (71 / 50) :=
        mul_le_mul hr₉ (hlog hr₉) (sqrt_nonneg _) (by positivity)
      linarith
    · have h3 : √(log (r / δ)) ^ 3 ≤ (71 / 50) ^ 3 :=
        pow_le_pow_left₀ (sqrt_nonneg _) (hlog hr₉) 3
      have : 2 * r * √(log (r / δ)) ^ 3 ≤ 2 * (9 * δ / 2) * (71 / 50) ^ 3 :=
        mul_le_mul (by linarith) h3 (by positivity) (by positivity)
      linarith
    · linarith
  · -- The two pieces are within `η` of each other only beyond `7 δ / 2`, where their slopes are
    -- at most `8` and `2`.
    have h' := (abs_le.1 h).1
    have hr₇ : 7 * δ / 2 ≤ r := by
      by_contra! hr₇
      linarith
    have hdP : deriv (fun x ↦ struweLineShape δ x + t) r ≤ 2 := by
      rw [deriv_add_const]
      exact deriv_struweLineShape_le hδ (by linarith [hr₇])
    have : η * (deriv (fun x ↦ √(64 * x ^ 2 + ℓ ^ 2)) r +
        deriv (fun x ↦ struweLineShape δ x + t) r) ≤ η * 10 :=
      mul_le_mul_of_nonneg_left (by linarith) hη₀.le
    linarith

/-- **The first bridge stage starts at the Struwe switch leaf `7 δ`.** For `δ > 0`, with
`S = struweShape δ 4 0` and `t₀ = 65 δ / 8 - S δ`, the bridge leaf of width `δ / 200` of
`sqrtAddLeaf L δ (7 δ)` and the Struwe/line shape raised by `t₀` is
`struweSwitchLeaf L δ (7 δ)` on `(δ, ∞)`. -/
theorem bridgeLeaf_sqrtAddLeaf_eqOn_struweSwitchLeaf (L : ℝ) (hδ : 0 < δ) :
    EqOn (bridgeLeaf δ (δ / 200) (sqrtAddLeaf L δ (7 * δ)) (65 * δ / 8 - struweShape δ 4 0 δ))
      (struweSwitchLeaf L δ (7 * δ)) (Ioi δ) := by
  intro r hr
  rw [mem_Ioi] at hr
  rcases le_or_gt r (7 * δ / 2) with hr₇ | hr₇
  · -- Up to `7 δ / 2` the raised shape is the Struwe shape of `struweSwitchLeaf L δ (7 δ)`.
    have hT : struweLineShape δ r + (65 * δ / 8 - struweShape δ 4 0 δ) =
        struweShape δ 1 (2 * (7 * δ) - 47 * δ / 8) r := by
      rw [struweLineShape_eq_struweShape hδ ⟨hr.le, hr₇⟩,
        struweShape_eq_struweShape_apply_mul hδ (by norm_num) le_rfl 0 hr.le, one_mul,
        add_comm, ← struweShape_add]
      congr 1
      ring
    rw [bridgeLeaf_def, struweSwitchLeaf_of_lt (by linarith), hT]
    congr 1
    ring
  · -- Beyond `7 δ / 2` both leaves are `sqrtAddLeaf L δ (7 δ)`.
    have hA := eight_mul_sqrt_le_sqrtAddLeaf L hδ.le (by positivity : (0 : ℝ) ≤ 7 * δ) r
    have hs : r - 3 * δ / 8 ≤ √(r ^ 2 - δ ^ 2) := le_sqrt_of_sq_le (by nlinarith)
    have hP := struweLineShape_le_two_mul_add hδ hr.le
    have hSδ := (struweShape_four_zero_self_mem_Icc hδ).1
    have h30 : √30 ≤ 23 / 4 := by rw [sqrt_le_left (by norm_num)]; norm_num
    rw [struweSwitchLeaf_of_two_mul_le L hδ ⟨by positivity, le_rfl⟩ (by linarith)]
    exact bridgeLeaf_eq_left (by positivity) (by nlinarith)

/-- **A high enough raised shape hides the cutoff region of `sqrtAddLeaf`.** Let `L, δ > 0`,
`ℓ ≥ 0` and `t` with `3 ℓ + 8 (3 + L) δ ≤ S δ + t`, where `S = struweShape δ 4 0`. Then on
`(δ, ∞)` the bridge leaf of width `δ / 200` of `sqrtAddLeaf L δ ℓ` and the Struwe/line shape
raised by `t` is the bridge leaf of the standard leaf `r ↦ √(64 r² + ℓ²)`. -/
theorem bridgeLeaf_sqrtAddLeaf_eqOn_sqrt {L : ℝ} (hL : 0 < L) (hδ : 0 < δ) {ℓ t : ℝ} (hℓ : 0 ≤ ℓ)
    (ht : 3 * ℓ + 8 * (3 + L) * δ ≤ struweShape δ 4 0 δ + t) :
    EqOn (bridgeLeaf δ (δ / 200) (sqrtAddLeaf L δ ℓ) t)
      (bridgeLeaf δ (δ / 200) (fun r ↦ √(64 * r ^ 2 + ℓ ^ 2)) t) (Ioi δ) := by
  intro r hr
  rw [mem_Ioi] at hr
  rcases le_or_gt ((2 + L) * δ) r with hrL | hrL
  · -- From `(2 + L) δ` on, `sqrtAddLeaf L δ ℓ` is the standard leaf.
    rw [bridgeLeaf_def, bridgeLeaf_def, sqrtAddLeaf_of_ge hL hδ hrL]
  · -- Below `(2 + L) δ`, both shapes lie more than `δ / 200` below the raised shape.
    have hSr := (strictMonoOn_struweShape hδ (by norm_num : (1 : ℝ) ≤ 4) 0).monotoneOn
      self_mem_Ici (mem_Ici.2 hr.le) hr.le
    have hP := struweShape_le_struweLineShape hδ r
    have hA := sqrtAddLeaf_le L hδ.le hℓ (hδ.trans hr).le
    have hQ : √(64 * r ^ 2 + ℓ ^ 2) ≤ 8 * r + ℓ :=
      (sqrt_le_left (by nlinarith)).2 (by nlinarith)
    rw [bridgeLeaf_eq_right (by positivity) (by nlinarith),
      bridgeLeaf_eq_right (by positivity) (by nlinarith)]

end SymplecticGeometry

end
