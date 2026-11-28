/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.SpecialFunctions.SmoothedMax
public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.ConvexShape.Basic

import SymplecticGeometry.Algebra.Order.Ring.Basic
import SymplecticGeometry.Analysis.Calculus.IteratedDeriv.Prod
import SymplecticGeometry.Order.Interval.Set.Piecewise
import SymplecticGeometry.Topology.Order.Compact
import SymplecticGeometry.Topology.Order.Piecewise
import TauCeti.Order.Interval.Set.Piecewise

/-!
# Smoothed maxima and minima of `i`-convex shapes

Two `i`-convex shapes (`SymplecticGeometry.IsConvexShapeAt`) meet, near their crossings, in a
smoothing of their maximum that is again an `i`-convex shape; two shapes over `R`
(`SymplecticGeometry.IsConvexShapeOverRAt`) meet in a smoothing of their minimum. The smoothing
is `SymplecticGeometry.smoothedMax`.

* `SymplecticGeometry.exists_isConvexShapeAt_eq_max`: two `i`-convex shapes on `[r₁, r₂]` have
  a common smoothing of their maximum, `r ↦ smoothedMax δ (χ₁ r) (χ₂ r)` for small `δ`, that is
  again an `i`-convex shape and is the maximum away from a given neighbourhood of their crossings
  in `[r₁, r₂]`. It is convex where both shapes are
  (`SymplecticGeometry.iteratedDeriv_two_smoothedMax_nonneg`).
  Its slope is a convex combination of theirs, which gives (4.3). For the case `σ = r` of (4.4)
  the cube of that slope falls short of the combination of the cubes by a multiple of
  `(χ₁' - χ₂')²` (`SymplecticGeometry.mul_pow_three_add_mul_pow_three_sub_pow_three_le`);
  where the weight is near `0` or `1` this is small, and elsewhere the term
  `(smoothedAbs δ)'' (χ₁' - χ₂')² / 2` of the second derivative, of order `1 / δ`
  (`SymplecticGeometry.exists_pos_div_le_iteratedDeriv_two_smoothedAbs`), makes up for it. So
  this route, unlike the book's quadratic bridge, needs no transversality of the crossings.
  It is the case of a single pair in
  `SymplecticGeometry.exists_forall_isConvexShapeAt_smoothedMax`, which gives every width up to
  some `δ₀ > 0` at once for a compact family of pairs whose values and two derivatives are
  jointly continuous in the parameter, since the margins and bounds above are then uniform.
  `SymplecticGeometry.exists_pos_forall_isConvexShapeAt_smoothedMax` is the pointwise statement
  behind both: `δ₀` depends only on the margin and the two bounds, not on the shapes.
* `SymplecticGeometry.min_le_deriv_smoothedMax_div_sub_one_div` and
  `SymplecticGeometry.min_le_iteratedDeriv_two_smoothedMax_add_pow_three_div_sub_one_div`: the
  smoothed maximum keeps the smaller of the two margins in (4.3), and in the case `σ = r` of
  (4.4) when `δ (χ₁' + χ₂') ≤ 2 r`. Like the proof that `smoothedMax` gives a shape, the second
  goes through the lower bound
  `SymplecticGeometry.le_iteratedDeriv_two_smoothedMax_add_pow_three_div_sub_one_div`; there the
  curvature bound
  `SymplecticGeometry.two_mul_one_sub_smoothedSign_sq_div_le_iteratedDeriv_two_smoothedAbs`
  makes up for the loss of the cube under that condition alone. So under it the smoothed
  maximum of two `i`-convex shapes at `r` is one, for any such `δ`
  (`SymplecticGeometry.isConvexShapeAt_smoothedMax`). The shapes need only be `C²` at `r`, as in
  each pointwise lemma of this file.
  The condition bounds only the slopes, which the smoothed maximum does not raise, so it
  carries over to each member of a chain of smoothed maxima of shapes whose slopes are at most
  `G` with `δ G ≤ r` (`SymplecticGeometry.isConvexShapeAt_smoothedMaxChain`).
* `SymplecticGeometry.exists_isConvexShapeAt_eqOn_Iic_Ici`: the same smoothing, for shapes that
  cross only inside `(u, v) ⊆ [r₁, r₂]`, continued by the first shape to the left of `u` and the
  second to the right of `v`, which gives an `i`-convex shape that passes from one to the other,
  and stays one outside `[r₁, r₂]` wherever the shape it equals there is.
  It glues by `SymplecticGeometry.IsConvexShapeAt.congr_of_eventuallyEq`: being an `i`-convex
  shape at `r` only depends on the germ at `r`.
* `SymplecticGeometry.exists_isConvexShapeOverRAt_eq_min`: the analogue of
  `exists_isConvexShapeAt_eq_max` over `R`, with the smoothed minimum
  `R ↦ -smoothedMax δ (-ρ₁ R) (-ρ₂ R)` in place of the smoothed maximum, since the inside of a
  graph over `R` is the side of small `r`. Its slope is again a convex combination, and the term
  `(smoothedAbs δ)'' (ρ₁' - ρ₂')² / 2`, now subtracted from the second derivative, makes up near a
  crossing for the errors of the cube and of the square of the slope, which may have either sign
  (`SymplecticGeometry.abs_mul_pow_three_add_mul_pow_three_sub_pow_three_le`). Both proofs take
  the trade-off between these errors and the curvature from
  `SymplecticGeometry.exists_pos_forall_one_sub_smoothedSign_sq_div_two_mul_lt`, and the
  distance between the two functions away from their crossings from
  `IsCompact.exists_pos_forall_le_abs_sub_of_mem_nhdsSet`. As over `r`, it is the case of a
  single pair in `SymplecticGeometry.exists_forall_isConvexShapeOverRAt_smoothedMin`, one width
  bound for a compact family of pairs, which rests on the pointwise
  `SymplecticGeometry.exists_pos_forall_isConvexShapeOverRAt_smoothedMin`, whose `δ₀` depends
  only on the margin, a lower bound of the two functions and two bounds on the slopes.
* `SymplecticGeometry.min_le_one_div_smoothedMin_sub_deriv_div`,
  `SymplecticGeometry.min_le_one_div_smoothedMin_sub_deriv_pow_three_div_sub_iteratedDeriv_two`
  and `SymplecticGeometry.min_le_one_add_sq_div_smoothedMin_sub_iteratedDeriv_two`: for a width
  `δ` at most both values, the smoothed minimum keeps the smaller of the two margins in each
  inequality of `isConvexShapeOverRAt_iff`, the second under `δ (|ρ₁'| + |ρ₂'|) ≤ 2 R`. They go
  through the lower bounds
  `SymplecticGeometry.le_one_div_smoothedMin_sub_deriv_pow_three_div_sub_iteratedDeriv_two` and
  `SymplecticGeometry.le_one_add_sq_div_smoothedMin_sub_iteratedDeriv_two`, which the uniform
  statement uses too, and give `SymplecticGeometry.isConvexShapeOverRAt_smoothedMin`, the
  analogue of `isConvexShapeAt_smoothedMax`. For such a width the first three conditions of
  `isConvexShapeOverRAt_iff` hold already
  (`SymplecticGeometry.isConvexShapeOverRAt_smoothedMin_iff`).

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  §4.3: Lemma 4.13 (d); the margin lemmas serve the foliations of Proposition 3.25.
-/

public section

noncomputable section

namespace SymplecticGeometry

open Topology

variable {r R : ℝ}

/-! ### The smoothed maximum of two shapes -/

/-- **The smoothed maximum keeps the smaller margin in (4.3).** For `δ > 0` and functions
`χ₁`, `χ₂` differentiable at `r` with `χ₁ r, χ₂ r > 0`, the quantity `χ' / r - 1 / χ` of
`χ = fun r ↦ smoothedMax δ (χ₁ r) (χ₂ r)` at `r` is at least the smaller of those of `χ₁` and
`χ₂`. -/
theorem min_le_deriv_smoothedMax_div_sub_one_div {χ₁ χ₂ : ℝ → ℝ} {δ : ℝ}
    (h₁ : DifferentiableAt ℝ χ₁ r) (h₂ : DifferentiableAt ℝ χ₂ r) (hδ : 0 < δ)
    (hv₁ : 0 < χ₁ r) (hv₂ : 0 < χ₂ r) :
    min (deriv χ₁ r / r - 1 / χ₁ r) (deriv χ₂ r / r - 1 / χ₂ r) ≤
      deriv (fun r ↦ smoothedMax δ (χ₁ r) (χ₂ r)) r / r -
        1 / smoothedMax δ (χ₁ r) (χ₂ r) := by
  have hinv := one_div_smoothedMax_le hδ hv₁ hv₂
  rw [deriv_smoothedMax_weighted h₁ h₂]
  obtain ⟨hw₀, hw₁⟩ := one_add_smoothedSign_div_two_mem_Icc δ (χ₁ r - χ₂ r)
  have hm := Convex.min_le_combo (𝕜 := ℝ) (deriv χ₁ r / r - 1 / χ₁ r)
    (deriv χ₂ r / r - 1 / χ₂ r) hw₀ (sub_nonneg.2 hw₁) (add_sub_cancel _ _)
  simp only [smul_eq_mul] at hm
  rw [add_div, mul_div_assoc, mul_div_assoc]
  linarith

/-- The first inequality of `isConvexShapeAt_iff` for the smoothed maximum of two `i`-convex
shapes at `r`. -/
private theorem one_div_smoothedMax_lt_deriv_div {χ₁ χ₂ : ℝ → ℝ} {δ : ℝ}
    (h₁ : ContDiffAt ℝ 2 χ₁ r) (h₂ : ContDiffAt ℝ 2 χ₂ r) (hδ : 0 < δ)
    (hc₁ : IsConvexShapeAt χ₁ r) (hc₂ : IsConvexShapeAt χ₂ r) :
    1 / smoothedMax δ (χ₁ r) (χ₂ r) < deriv (fun r ↦ smoothedMax δ (χ₁ r) (χ₂ r)) r / r := by
  have h := min_le_deriv_smoothedMax_div_sub_one_div (δ := δ) (h₁.differentiableAt two_ne_zero)
    (h₂.differentiableAt two_ne_zero) hδ hc₁.pos_value hc₂.pos_value
  have hm := lt_min (sub_pos.2 hc₁.one_div_lt_deriv_div) (sub_pos.2 hc₂.one_div_lt_deriv_div)
  linarith

/-- A lower bound for the second inequality of `isConvexShapeAt_iff` for the smoothed maximum.
Let `χ₁`, `χ₂` be `C²` at `r`, `δ > 0`, `r > 0`, `χ₁ r, χ₂ r > 0` and `x = χ₁' r ≥ 0`,
`y = χ₂' r ≥ 0`, and let `s = smoothedSign δ (χ₁ r - χ₂ r)` and
`p = (smoothedAbs δ)'' (χ₁ r - χ₂ r)`. Then the quantity `χ'' + χ'³ / r - 1 / χ` of
`χ = fun r ↦ smoothedMax δ (χ₁ r) (χ₂ r)` at `r` is at least the combination of those of `χ₁` and
`χ₂` with the weights `(1 ± s) / 2`, plus `p (x - y)² / 2 - (1 - s²) / 2 · (x - y)² (x + y) / r`:
the curvature that `smoothedAbs δ` adds, less what the cube of the slope loses. -/
theorem le_iteratedDeriv_two_smoothedMax_add_pow_three_div_sub_one_div {χ₁ χ₂ : ℝ → ℝ} {δ : ℝ}
    (h₁ : ContDiffAt ℝ 2 χ₁ r) (h₂ : ContDiffAt ℝ 2 χ₂ r) (hδ : 0 < δ) (hr : 0 < r)
    (hv₁ : 0 < χ₁ r) (hv₂ : 0 < χ₂ r) (hx : 0 ≤ deriv χ₁ r) (hy : 0 ≤ deriv χ₂ r) :
    (1 + smoothedSign δ (χ₁ r - χ₂ r)) / 2 *
        (iteratedDeriv 2 χ₁ r + deriv χ₁ r ^ 3 / r - 1 / χ₁ r) +
      (1 - smoothedSign δ (χ₁ r - χ₂ r)) / 2 *
        (iteratedDeriv 2 χ₂ r + deriv χ₂ r ^ 3 / r - 1 / χ₂ r) +
      (iteratedDeriv 2 (smoothedAbs δ) (χ₁ r - χ₂ r) * (deriv χ₁ r - deriv χ₂ r) ^ 2 / 2 -
        (1 - smoothedSign δ (χ₁ r - χ₂ r) ^ 2) / 2 *
          ((deriv χ₁ r - deriv χ₂ r) ^ 2 * ((deriv χ₁ r + deriv χ₂ r) / r))) ≤
      iteratedDeriv 2 (fun r ↦ smoothedMax δ (χ₁ r) (χ₂ r)) r +
        deriv (fun r ↦ smoothedMax δ (χ₁ r) (χ₂ r)) r ^ 3 / r -
        1 / smoothedMax δ (χ₁ r) (χ₂ r) := by
  have hinv := one_div_smoothedMax_le hδ hv₁ hv₂
  rw [deriv_smoothedMax_weighted (h₁.differentiableAt two_ne_zero)
    (h₂.differentiableAt two_ne_zero), iteratedDeriv_two_smoothedMax h₁ h₂]
  obtain ⟨hw₀, hw₁⟩ := one_add_smoothedSign_div_two_mem_Icc δ (χ₁ r - χ₂ r)
  set x := deriv χ₁ r
  set y := deriv χ₂ r
  set s := smoothedSign δ (χ₁ r - χ₂ r)
  set p := iteratedDeriv 2 (smoothedAbs δ) (χ₁ r - χ₂ r)
  set w := (1 + s) / 2 with hw
  rw [show (1 - s) / 2 = 1 - w by rw [hw]; ring] at hinv ⊢
  -- The cube of the slope falls short of the combination of the cubes by
  -- `E ≤ (1 - s²) / 2 · (x - y)² (x + y) / r`.
  set E := w * (x ^ 3 / r) + (1 - w) * (y ^ 3 / r) - (w * x + (1 - w) * y) ^ 3 / r with hE
  have hEle : E ≤ (1 - s ^ 2) / 2 * ((x - y) ^ 2 * ((x + y) / r)) := by
    have h := div_le_div_of_nonneg_right
      (mul_pow_three_add_mul_pow_three_sub_pow_three_le hw₀ hw₁ hx hy) hr.le
    convert h using 1
    · rw [hE]; ring
    · rw [hw]; ring
  have he : (iteratedDeriv 2 χ₁ r + iteratedDeriv 2 χ₂ r + s * (iteratedDeriv 2 χ₁ r -
      iteratedDeriv 2 χ₂ r) + p * (x - y) ^ 2) / 2 =
      w * iteratedDeriv 2 χ₁ r + (1 - w) * iteratedDeriv 2 χ₂ r + p * (x - y) ^ 2 / 2 := by
    rw [hw]; ring
  rw [he]
  simp only [div_eq_mul_inv, hE] at hEle hinv ⊢
  linarith

/-- **The smoothed maximum keeps the smaller margin in the case `σ = r` of (4.4).** Let `χ₁`,
`χ₂` be `C²` at `r`, `δ > 0`, `r > 0`, `χ₁ r, χ₂ r > 0`, `χ₁' r, χ₂' r ≥ 0` and
`δ (χ₁' r + χ₂' r) ≤ 2 r`. Then the quantity `χ'' + χ'³ / r - 1 / χ` of
`χ = fun r ↦ smoothedMax δ (χ₁ r) (χ₂ r)` at `r` is at least the smaller of those of `χ₁` and
`χ₂`. -/
theorem min_le_iteratedDeriv_two_smoothedMax_add_pow_three_div_sub_one_div {χ₁ χ₂ : ℝ → ℝ}
    {δ : ℝ} (h₁ : ContDiffAt ℝ 2 χ₁ r) (h₂ : ContDiffAt ℝ 2 χ₂ r) (hδ : 0 < δ) (hr : 0 < r)
    (hv₁ : 0 < χ₁ r) (hv₂ : 0 < χ₂ r) (hx : 0 ≤ deriv χ₁ r) (hy : 0 ≤ deriv χ₂ r)
    (hδr : δ * (deriv χ₁ r + deriv χ₂ r) ≤ 2 * r) :
    min (iteratedDeriv 2 χ₁ r + deriv χ₁ r ^ 3 / r - 1 / χ₁ r)
        (iteratedDeriv 2 χ₂ r + deriv χ₂ r ^ 3 / r - 1 / χ₂ r) ≤
      iteratedDeriv 2 (fun r ↦ smoothedMax δ (χ₁ r) (χ₂ r)) r +
        deriv (fun r ↦ smoothedMax δ (χ₁ r) (χ₂ r)) r ^ 3 / r -
        1 / smoothedMax δ (χ₁ r) (χ₂ r) := by
  have h := le_iteratedDeriv_two_smoothedMax_add_pow_three_div_sub_one_div h₁ h₂ hδ hr hv₁ hv₂
    hx hy
  -- Since `δ (x + y) ≤ 2 r`, the curvature `p ≥ 2 (1 - s²) / δ` makes up for the cube.
  have hT : (deriv χ₁ r + deriv χ₂ r) / r ≤ 2 / δ := by
    rw [div_le_div_iff₀ hr hδ]
    linarith
  have hc := one_sub_smoothedSign_sq_div_two_mul_le hδ (sq_nonneg (deriv χ₁ r - deriv χ₂ r)) hT
    (χ₁ r - χ₂ r)
  have hs := abs_le.1 (abs_smoothedSign_le_one δ (χ₁ r - χ₂ r))
  have hm := Convex.min_le_combo (𝕜 := ℝ) (iteratedDeriv 2 χ₁ r + deriv χ₁ r ^ 3 / r - 1 / χ₁ r)
    (iteratedDeriv 2 χ₂ r + deriv χ₂ r ^ 3 / r - 1 / χ₂ r)
    (by linarith : 0 ≤ (1 + smoothedSign δ (χ₁ r - χ₂ r)) / 2)
    (by linarith : 0 ≤ (1 - smoothedSign δ (χ₁ r - χ₂ r)) / 2) (by ring)
  simp only [smul_eq_mul] at hm
  linarith

/-- **The smoothed maximum of two `i`-convex shapes, for a moderate width.** Let `χ₁`,
`χ₂` be `C²` at `r` and `i`-convex shapes at `r`, and `δ > 0` with `δ (χ₁' r + χ₂' r) ≤ 2 r`.
Then `r ↦ smoothedMax δ (χ₁ r) (χ₂ r)` is an `i`-convex shape at `r`. -/
theorem isConvexShapeAt_smoothedMax {χ₁ χ₂ : ℝ → ℝ} {δ : ℝ} (h₁ : ContDiffAt ℝ 2 χ₁ r)
    (h₂ : ContDiffAt ℝ 2 χ₂ r) (hδ : 0 < δ) (hc₁ : IsConvexShapeAt χ₁ r)
    (hc₂ : IsConvexShapeAt χ₂ r) (hδr : δ * (deriv χ₁ r + deriv χ₂ r) ≤ 2 * r) :
    IsConvexShapeAt (fun r ↦ smoothedMax δ (χ₁ r) (χ₂ r)) r := by
  have h := min_le_iteratedDeriv_two_smoothedMax_add_pow_three_div_sub_one_div h₁ h₂ hδ hc₁.pos
    hc₁.pos_value hc₂.pos_value hc₁.deriv_pos.le hc₂.deriv_pos.le hδr
  have hm := lt_min (sub_pos.2 hc₁.one_div_lt_iteratedDeriv_add)
    (sub_pos.2 hc₂.one_div_lt_iteratedDeriv_add)
  exact isConvexShapeAt_iff.2 ⟨hc₁.pos, hc₁.pos_value.trans_le
    ((le_max_left _ _).trans (max_le_smoothedMax hδ _ _)),
    one_div_smoothedMax_lt_deriv_div h₁ h₂ hδ hc₁ hc₂, by linarith⟩

/-- **A chain of smoothed maxima of `i`-convex shapes.** Let `δ > 0`, and let `A 0, …, A n` be
`C²` at `r` and `i`-convex shapes at `r` with slopes at most `G` there, where `δ G ≤ r`. Then the
`n`-th member of their chain of smoothed maxima is an `i`-convex shape at `r`. -/
theorem isConvexShapeAt_smoothedMaxChain {A : ℕ → ℝ → ℝ} {δ G : ℝ} {n : ℕ} (hδ : 0 < δ)
    (hA : ∀ j ≤ n, ContDiffAt ℝ 2 (A j) r) (hc : ∀ j ≤ n, IsConvexShapeAt (A j) r)
    (hG : ∀ j ≤ n, deriv (A j) r ≤ G) (hδG : δ * G ≤ r) :
    IsConvexShapeAt (smoothedMaxChain δ A n) r := by
  induction n with
  | zero => rw [smoothedMaxChain_zero]; exact hc 0 le_rfl
  | succ n ih =>
    have hA' : ∀ j ≤ n, ContDiffAt ℝ 2 (A j) r := fun j hj ↦ hA j (Nat.le_succ_of_le hj)
    have hM := deriv_smoothedMaxChain_le δ
      (fun j hj ↦ (hA' j hj).differentiableAt two_ne_zero) fun j hj ↦ hG j (Nat.le_succ_of_le hj)
    have hδr := mul_le_mul_of_nonneg_left (add_le_add hM (hG (n + 1) le_rfl)) hδ.le
    rw [smoothedMaxChain_succ]
    exact isConvexShapeAt_smoothedMax (contDiffAt_smoothedMaxChain δ hA') (hA (n + 1) le_rfl) hδ
      (ih hA' (fun j hj ↦ hc j (Nat.le_succ_of_le hj)) fun j hj ↦ hG j (Nat.le_succ_of_le hj))
      (hc (n + 1) le_rfl) (by linarith)

/-- The second inequality of `isConvexShapeAt_iff` for the smoothed maximum of two `i`-convex
shapes at `r`, given a margin `a` in it for both, upper bounds `G` and `Q` for the error made by
the cube of the slope, and the bound of
`exists_pos_forall_one_sub_smoothedSign_sq_div_two_mul_lt` at `χ₁ r - χ₂ r`, by which the
curvature of `smoothedAbs δ` makes up for that error. -/
private theorem one_div_smoothedMax_lt_iteratedDeriv_add {χ₁ χ₂ : ℝ → ℝ} {δ a G Q : ℝ}
    (h₁ : ContDiffAt ℝ 2 χ₁ r) (h₂ : ContDiffAt ℝ 2 χ₂ r) (hδ : 0 < δ)
    (hc₁ : IsConvexShapeAt χ₁ r)
    (hc₂ : IsConvexShapeAt χ₂ r)
    (ha₁ : a ≤ iteratedDeriv 2 χ₁ r + deriv χ₁ r ^ 3 / r - 1 / χ₁ r)
    (ha₂ : a ≤ iteratedDeriv 2 χ₂ r + deriv χ₂ r ^ 3 / r - 1 / χ₂ r)
    (hG : (deriv χ₁ r - deriv χ₂ r) ^ 2 * ((deriv χ₁ r + deriv χ₂ r) / r) ≤ G)
    (hQ : (deriv χ₁ r + deriv χ₂ r) / r ≤ Q)
    (hL : ∀ {g T : ℝ}, 0 ≤ g → 0 ≤ T → T ≤ Q → g * T ≤ G →
      (1 - smoothedSign δ (χ₁ r - χ₂ r) ^ 2) / 2 * (g * T) <
        a + iteratedDeriv 2 (smoothedAbs δ) (χ₁ r - χ₂ r) * g / 2) :
    1 / smoothedMax δ (χ₁ r) (χ₂ r) < iteratedDeriv 2 (fun r ↦ smoothedMax δ (χ₁ r) (χ₂ r)) r +
      deriv (fun r ↦ smoothedMax δ (χ₁ r) (χ₂ r)) r ^ 3 / r := by
  have hr := hc₁.pos
  have hx := hc₁.deriv_pos
  have hy := hc₂.deriv_pos
  have h := le_iteratedDeriv_two_smoothedMax_add_pow_three_div_sub_one_div h₁ h₂ hδ hr
    hc₁.pos_value hc₂.pos_value hx.le hy.le
  obtain ⟨hw₀, hw₁⟩ := one_add_smoothedSign_div_two_mem_Icc δ (χ₁ r - χ₂ r)
  have hw₁' : 0 ≤ (1 - smoothedSign δ (χ₁ r - χ₂ r)) / 2 := by linarith
  have hT : 0 ≤ (deriv χ₁ r + deriv χ₂ r) / r := by positivity
  have hl := hL (sq_nonneg (deriv χ₁ r - deriv χ₂ r)) hT hQ hG
  linarith [mul_le_mul_of_nonneg_left ha₁ hw₀, mul_le_mul_of_nonneg_left ha₂ hw₁']

/-- The pointwise step of `exists_pos_forall_isConvexShapeAt_smoothedMax`: at `r`, the smoothed
maximum of two `i`-convex shapes is one, under the hypotheses of
`one_div_smoothedMax_lt_iteratedDeriv_add`. -/
private theorem isConvexShapeAt_smoothedMax_of_le {χ₁ χ₂ : ℝ → ℝ} {δ a G Q : ℝ}
    (h₁ : ContDiffAt ℝ 2 χ₁ r) (h₂ : ContDiffAt ℝ 2 χ₂ r) (hδ : 0 < δ)
    (hc₁ : IsConvexShapeAt χ₁ r)
    (hc₂ : IsConvexShapeAt χ₂ r)
    (ha₁ : a ≤ iteratedDeriv 2 χ₁ r + deriv χ₁ r ^ 3 / r - 1 / χ₁ r)
    (ha₂ : a ≤ iteratedDeriv 2 χ₂ r + deriv χ₂ r ^ 3 / r - 1 / χ₂ r)
    (hG : (deriv χ₁ r - deriv χ₂ r) ^ 2 * ((deriv χ₁ r + deriv χ₂ r) / r) ≤ G)
    (hQ : (deriv χ₁ r + deriv χ₂ r) / r ≤ Q)
    (hL : ∀ {g T : ℝ}, 0 ≤ g → 0 ≤ T → T ≤ Q → g * T ≤ G →
      (1 - smoothedSign δ (χ₁ r - χ₂ r) ^ 2) / 2 * (g * T) <
        a + iteratedDeriv 2 (smoothedAbs δ) (χ₁ r - χ₂ r) * g / 2) :
    IsConvexShapeAt (fun r ↦ smoothedMax δ (χ₁ r) (χ₂ r)) r :=
  isConvexShapeAt_iff.2 ⟨hc₁.pos, hc₁.pos_value.trans_le
    ((le_max_left _ _).trans (max_le_smoothedMax hδ _ _)),
    one_div_smoothedMax_lt_deriv_div h₁ h₂ hδ hc₁ hc₂,
    one_div_smoothedMax_lt_iteratedDeriv_add h₁ h₂ hδ hc₁ hc₂ ha₁ ha₂ hG hQ hL⟩

/-- **A uniform width for the smoothed maximum of two `i`-convex shapes.** Given `a > 0` and
bounds `G` and `Q`, there is `δ₀ > 0` such that, for every `δ ∈ (0, δ₀]`, the smoothed maximum
`r ↦ smoothedMax δ (χ₁ r) (χ₂ r)` of two functions `χ₁`, `χ₂` is an `i`-convex shape at each `r`
where both are `C²` and `i`-convex shapes, where both satisfy the second inequality of
`isConvexShapeAt_iff` with margin at least `a`, and where `(χ₁' - χ₂')² (χ₁' + χ₂') / r ≤ G`
and `(χ₁' + χ₂') / r ≤ Q`.

So `δ₀` depends only on `a`, `G` and `Q`, not on the shapes. -/
theorem exists_pos_forall_isConvexShapeAt_smoothedMax {a : ℝ} (ha : 0 < a) (G Q : ℝ) :
    ∃ δ₀ > 0, ∀ δ ∈ Set.Ioc 0 δ₀, ∀ {χ₁ χ₂ : ℝ → ℝ} {r : ℝ}, ContDiffAt ℝ 2 χ₁ r →
      ContDiffAt ℝ 2 χ₂ r → IsConvexShapeAt χ₁ r → IsConvexShapeAt χ₂ r →
      a ≤ iteratedDeriv 2 χ₁ r + deriv χ₁ r ^ 3 / r - 1 / χ₁ r →
      a ≤ iteratedDeriv 2 χ₂ r + deriv χ₂ r ^ 3 / r - 1 / χ₂ r →
      (deriv χ₁ r - deriv χ₂ r) ^ 2 * ((deriv χ₁ r + deriv χ₂ r) / r) ≤ G →
      (deriv χ₁ r + deriv χ₂ r) / r ≤ Q →
      IsConvexShapeAt (fun r ↦ smoothedMax δ (χ₁ r) (χ₂ r)) r := by
  obtain ⟨δ₀, hδ₀, hL⟩ := exists_pos_forall_one_sub_smoothedSign_sq_div_two_mul_lt ha G Q
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ χ₁ χ₂ r h₁ h₂ hc₁ hc₂ ha₁ ha₂ hG hQ
  exact isConvexShapeAt_smoothedMax_of_le h₁ h₂ hδ.1 hc₁ hc₂ ha₁ ha₂ hG hQ
    fun hg hT hTQ hgT ↦ hL δ hδ.1 hδ.2 hg hT hTQ hgT _

/-- **The smoothed maximum of a compact family of pairs of `i`-convex shapes.** Let `K` be a
compact set of parameters, and for `p ∈ K` let `M p` and `A p` be `C²` at, and `i`-convex shapes
at, every point of `[r₁, r₂]`, whose values and first two derivatives are jointly continuous in
`(p, r)` on `K × [r₁, r₂]`. Then there is `δ₀ > 0` such that, for every `δ ∈ (0, δ₀]` and
`p ∈ K`, `r ↦ smoothedMax δ (M p r) (A p r)` is an `i`-convex shape at every point of
`[r₁, r₂]`. -/
theorem exists_forall_isConvexShapeAt_smoothedMax {P : Type*} [TopologicalSpace P] {K : Set P}
    (hK : IsCompact K) {M A : P → ℝ → ℝ} {r₁ r₂ : ℝ}
    (hM : ∀ p ∈ K, ∀ r ∈ Set.Icc r₁ r₂, ContDiffAt ℝ 2 (M p) r)
    (hA : ∀ p ∈ K, ∀ r ∈ Set.Icc r₁ r₂, ContDiffAt ℝ 2 (A p) r)
    (hcM : ∀ p ∈ K, ∀ r ∈ Set.Icc r₁ r₂, IsConvexShapeAt (M p) r)
    (hcA : ∀ p ∈ K, ∀ r ∈ Set.Icc r₁ r₂, IsConvexShapeAt (A p) r)
    (hdM : ∀ k ≤ 2, ContinuousOn (fun q : P × ℝ ↦ iteratedDeriv k (M q.1) q.2)
      (K ×ˢ Set.Icc r₁ r₂))
    (hdA : ∀ k ≤ 2, ContinuousOn (fun q : P × ℝ ↦ iteratedDeriv k (A q.1) q.2)
      (K ×ˢ Set.Icc r₁ r₂)) :
    ∃ δ₀ > 0, ∀ δ ∈ Set.Ioc 0 δ₀, ∀ p ∈ K, ∀ r ∈ Set.Icc r₁ r₂,
      IsConvexShapeAt (fun r ↦ smoothedMax δ (M p r) (A p r)) r := by
  set S := K ×ˢ Set.Icc r₁ r₂
  have hS : IsCompact S := hK.prod isCompact_Icc
  have hr₀ : ∀ q ∈ S, q.2 ≠ 0 := fun q hq ↦ (hcM q.1 hq.1 q.2 hq.2).pos.ne'
  have hsM := ContinuousOn.deriv_of_iteratedDeriv hdM one_le_two
  have hsA := ContinuousOn.deriv_of_iteratedDeriv hdA one_le_two
  -- A common margin `a` in the second inequality of `isConvexShapeAt_iff` for both families.
  have margin {F : P → ℝ → ℝ}
      (hd : ∀ k ≤ 2, ContinuousOn (fun q : P × ℝ ↦ iteratedDeriv k (F q.1) q.2) S)
      (hc : ∀ p ∈ K, ∀ r ∈ Set.Icc r₁ r₂, IsConvexShapeAt (F p) r) :
      ∃ a > 0, ∀ q ∈ S,
        a ≤ iteratedDeriv 2 (F q.1) q.2 + deriv (F q.1) q.2 ^ 3 / q.2 - 1 / F q.1 q.2 := by
    have hv := ContinuousOn.uncurry_of_iteratedDeriv hd
    have hs := ContinuousOn.deriv_of_iteratedDeriv hd one_le_two
    have h₁ : ContinuousOn (fun q : P × ℝ ↦ deriv (F q.1) q.2 ^ 3 / q.2) S :=
      (hs.pow 3).div continuousOn_snd hr₀
    have h₂ : ContinuousOn (fun q : P × ℝ ↦ 1 / F q.1 q.2) S :=
      continuousOn_const.div hv fun q hq ↦ (hc q.1 hq.1 q.2 hq.2).pos_value.ne'
    exact hS.exists_forall_le' (((hd 2 le_rfl).add h₁).sub h₂)
      fun q hq ↦ sub_pos.2 (hc q.1 hq.1 q.2 hq.2).one_div_lt_iteratedDeriv_add
  obtain ⟨a₁, ha₁, hA₁⟩ := margin hdM hcM
  obtain ⟨a₂, ha₂, hA₂⟩ := margin hdA hcA
  -- Bounds on the error terms.
  have hcq : ContinuousOn (fun q : P × ℝ ↦ (deriv (M q.1) q.2 + deriv (A q.1) q.2) / q.2) S :=
    (hsM.add hsA).div continuousOn_snd hr₀
  obtain ⟨Q, hQ⟩ := hS.exists_bound_of_continuousOn hcq
  obtain ⟨G, hG⟩ := hS.exists_bound_of_continuousOn (((hsM.sub hsA).pow 2).mul hcq)
  obtain ⟨δ₀, hδ₀, h⟩ := exists_pos_forall_isConvexShapeAt_smoothedMax (lt_min ha₁ ha₂) G Q
  refine ⟨δ₀, hδ₀, fun δ hδ p hp r hr ↦ ?_⟩
  have hq : (p, r) ∈ S := ⟨hp, hr⟩
  have e₁ : a₁ ≤ iteratedDeriv 2 (M p) r + deriv (M p) r ^ 3 / r - 1 / M p r := hA₁ (p, r) hq
  have e₂ : a₂ ≤ iteratedDeriv 2 (A p) r + deriv (A p) r ^ 3 / r - 1 / A p r := hA₂ (p, r) hq
  exact h δ hδ (hM p hp r hr) (hA p hp r hr) (hcM p hp r hr) (hcA p hp r hr)
    ((min_le_left _ _).trans e₁) ((min_le_right _ _).trans e₂)
    ((Real.le_norm_self _).trans (hG _ hq)) ((Real.le_norm_self _).trans (hQ _ hq))

/-- **The smoothed maximum of two `i`-convex shapes.** Let `χ₁` and `χ₂` be `C²` and `i`-convex
shapes at every point of `[r₁, r₂]`, and let `O` be a neighbourhood of the points of `[r₁, r₂]`
where they cross. Then some `χ`, as smooth as `χ₁` and `χ₂` are (so at least `C²`), is an
`i`-convex shape at every point of `[r₁, r₂]` and equals `max (χ₁ r) (χ₂ r)`
at the points of `[r₁, r₂]` outside `O`. Its second derivative is nonnegative at each `r`
where those of `χ₁` and `χ₂` are.

The function is `r ↦ smoothedMax δ (χ₁ r) (χ₂ r)` for `δ` small. Unlike the book's, this
statement does not ask that the shapes cross transversally. -/
theorem exists_isConvexShapeAt_eq_max {χ₁ χ₂ : ℝ → ℝ} {r₁ r₂ : ℝ} {O : Set ℝ}
    (h₁ : ContDiff ℝ 2 χ₁) (h₂ : ContDiff ℝ 2 χ₂)
    (hc₁ : ∀ r ∈ Set.Icc r₁ r₂, IsConvexShapeAt χ₁ r)
    (hc₂ : ∀ r ∈ Set.Icc r₁ r₂, IsConvexShapeAt χ₂ r)
    (hO : O ∈ 𝓝ˢ (Set.Icc r₁ r₂ ∩ {r | χ₁ r = χ₂ r})) :
    ∃ χ : ℝ → ℝ, (∀ n : ℕ∞, ContDiff ℝ n χ₁ → ContDiff ℝ n χ₂ → ContDiff ℝ n χ) ∧
      (∀ r ∈ Set.Icc r₁ r₂, IsConvexShapeAt χ r) ∧
      (∀ r ∈ Set.Icc r₁ r₂ \ O, χ r = max (χ₁ r) (χ₂ r)) ∧
      ∀ r, 0 ≤ iteratedDeriv 2 χ₁ r → 0 ≤ iteratedDeriv 2 χ₂ r → 0 ≤ iteratedDeriv 2 χ r := by
  obtain ⟨δ₀, hδ₀, h⟩ := exists_forall_isConvexShapeAt_smoothedMax isCompact_univ
    (M := fun _ : Unit ↦ χ₁) (A := fun _ ↦ χ₂) (fun _ _ _ _ ↦ h₁.contDiffAt)
    (fun _ _ _ _ ↦ h₂.contDiffAt) (fun _ _ ↦ hc₁)
    (fun _ _ ↦ hc₂)
    (h₁.continuousOn_iteratedDeriv_snd le_rfl)
    (h₂.continuousOn_iteratedDeriv_snd le_rfl)
  -- A lower bound `β` for `|χ₁ - χ₂|` on `[r₁, r₂]` outside `O`.
  obtain ⟨β, hβ, hβD⟩ := isCompact_Icc.exists_pos_forall_le_abs_sub_of_mem_nhdsSet
    h₁.continuous.continuousOn h₂.continuous.continuousOn hO
  set δ := min δ₀ β
  have hδ : 0 < δ := lt_min hδ₀ hβ
  refine ⟨fun r ↦ smoothedMax δ (χ₁ r) (χ₂ r), fun n hn₁ hn₂ ↦
    (contDiff_smoothedMax δ).comp (hn₁.prodMk hn₂), fun r hr ↦
    h δ ⟨hδ, min_le_left _ _⟩ () (Set.mem_univ _) r hr,
    fun r hr ↦ smoothedMax_eq_max hδ ((min_le_right _ _).trans (hβD r hr)),
    fun r ↦ iteratedDeriv_two_smoothedMax_nonneg h₁.contDiffAt h₂.contDiffAt hδ.le⟩

open Set in
/-- **Passing from one `i`-convex shape to another.** Let `χ₁` and `χ₂` be `Cⁿ`, `n ≥ 2`, and
`i`-convex shapes at every point of `[r₁, r₂]`, and let `r₁ < u < v < r₂`. Suppose that `χ₁` is
at least `χ₂` on `[r₁, u]`, at most `χ₂` on `[v, r₂]`, and that they cross in `[r₁, r₂]` only
inside `(u, v)`. Then some `Cⁿ` function `χ`, an `i`-convex shape at every point of `[r₁, r₂]`,
equals `χ₁` on `(-∞, u]` and `χ₂` on `[v, ∞)`. Outside `[r₁, r₂]` it is still an `i`-convex
shape where `χ₁` is, left of `u`, and where `χ₂` is, right of `v`. Its second derivative is
nonnegative at each `r` where those of `χ₁` and `χ₂` are.

It is the smoothed maximum of `exists_isConvexShapeAt_eq_max` on `[r₁, r₂]`, continued by `χ₁` to
the left and by `χ₂` to the right. -/
theorem exists_isConvexShapeAt_eqOn_Iic_Ici {χ₁ χ₂ : ℝ → ℝ} {n : ℕ∞} {r₁ u v r₂ : ℝ}
    (hn : 2 ≤ n) (h₁ : ContDiff ℝ n χ₁) (h₂ : ContDiff ℝ n χ₂) (hr₁ : r₁ < u) (huv : u < v)
    (hr₂ : v < r₂) (hc₁ : ∀ r ∈ Icc r₁ r₂, IsConvexShapeAt χ₁ r)
    (hc₂ : ∀ r ∈ Icc r₁ r₂, IsConvexShapeAt χ₂ r) (hle₁ : ∀ r ∈ Icc r₁ u, χ₂ r ≤ χ₁ r)
    (hle₂ : ∀ r ∈ Icc v r₂, χ₁ r ≤ χ₂ r)
    (hcross : ∀ r ∈ Icc r₁ r₂, χ₁ r = χ₂ r → r ∈ Ioo u v) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ n χ ∧ (∀ r ∈ Icc r₁ r₂, IsConvexShapeAt χ r) ∧
      EqOn χ χ₁ (Iic u) ∧ EqOn χ χ₂ (Ici v) ∧
      (∀ r < u, IsConvexShapeAt χ₁ r → IsConvexShapeAt χ r) ∧
      (∀ r, v < r → IsConvexShapeAt χ₂ r → IsConvexShapeAt χ r) ∧
      ∀ r, 0 ≤ iteratedDeriv 2 χ₁ r → 0 ≤ iteratedDeriv 2 χ₂ r → 0 ≤ iteratedDeriv 2 χ r := by
  have hn' : ((2 : ℕ∞) : WithTop ℕ∞) ≤ n := WithTop.coe_le_coe.2 hn
  obtain ⟨χ, hχs, hχc, hχ, hχcv⟩ := exists_isConvexShapeAt_eq_max (O := Ioo u v)
    (h₁.of_le hn') (h₂.of_le hn') hc₁ hc₂
    (isOpen_Ioo.mem_nhdsSet.2 fun r hr ↦ hcross r hr.1 hr.2)
  replace hχs := hχs n h₁ h₂
  have hχ₁ : EqOn χ χ₁ (Icc r₁ u) := fun r hr ↦ by
    rw [hχ r ⟨⟨hr.1, by linarith [hr.2]⟩, fun h ↦ hr.2.not_gt h.1⟩, max_eq_left (hle₁ r hr)]
  have hχ₂ : EqOn χ χ₂ (Icc v r₂) := fun r hr ↦ by
    rw [hχ r ⟨⟨by linarith [hr.1], hr.2⟩, fun h ↦ hr.1.not_gt h.2⟩, max_eq_right (hle₂ r hr)]
  -- Outside `[r₁, r₂]`, replace `χ` by `χ₁` on the left and by `χ₂` on the right.
  set φ : ℝ → ℝ := fun r ↦ if r ≤ (v + r₂) / 2 then χ r else χ₂ r
  set ψ : ℝ → ℝ := fun r ↦ if r ≤ (r₁ + u) / 2 then χ₁ r else φ r
  have hφχ : EqOn φ χ (Iio r₂) := EqOn.eqOn_ite_le_left
    (hχ₂.mono fun r hr ↦ mem_Icc.2 ⟨by linarith [mem_Ioi.1 hr.2], (mem_Iio.1 hr.1).le⟩)
  have hφ₂ : EqOn φ χ₂ (Ici v) := EqOn.eqOn_ite_le_right
    (hχ₂.mono fun r hr ↦ mem_Icc.2 ⟨hr.1, by linarith [mem_Iic.1 hr.2]⟩)
  have h₁φ : EqOn χ₁ φ (Icc r₁ u) := fun r hr ↦
    (hχ₁ hr).symm.trans (hφχ (by linarith [hr.2] : r < r₂)).symm
  have e₁ : EqOn ψ χ₁ (Iic u) := EqOn.eqOn_ite_le_left
    (h₁φ.mono fun r hr ↦ mem_Icc.2 ⟨by linarith [mem_Ioi.1 hr.2], hr.1⟩)
  have e₂ : EqOn ψ χ₂ (Ici v) := fun r hr ↦ (eqOn_ite_le_Ici (h₁φ ⟨by linarith, by linarith⟩)
    (by linarith [mem_Ici.1 hr] : (r₁ + u) / 2 ≤ r)).trans (hφ₂ hr)
  have key : ∀ r, (ψ =ᶠ[𝓝 r] χ₁ ∧ r < u) ∨ (ψ =ᶠ[𝓝 r] χ ∧ r ∈ Ioo r₁ r₂) ∨
      (ψ =ᶠ[𝓝 r] χ₂ ∧ v < r) := fun r ↦ by
    rcases lt_or_ge r u with h | h
    · exact Or.inl ⟨(e₁.mono Iio_subset_Iic_self).eventuallyEq_of_mem (isOpen_Iio.mem_nhds h), h⟩
    rcases le_or_gt r v with h' | h'
    · have hr : r ∈ Ioo r₁ r₂ := ⟨by linarith, by linarith⟩
      refine Or.inr (Or.inl ⟨?_, hr⟩)
      exact ((h₁φ.mono Ioo_subset_Icc_self).eventuallyEq_ite_le_right (by linarith) hr.1).trans
        ((hχ₂.mono Ioo_subset_Icc_self).eventuallyEq_ite_le_left (by linarith) hr.2)
    · exact Or.inr (Or.inr
        ⟨(e₂.mono Ioi_subset_Ici_self).eventuallyEq_of_mem (isOpen_Ioi.mem_nhds h'), h'⟩)
  refine ⟨ψ, contDiff_iff_contDiffAt.2 fun r ↦ ?_, fun r hr ↦ ?_, e₁, e₂,
    fun r hr h ↦ h.congr_of_eventuallyEq
      ((e₁.mono Iio_subset_Iic_self).eventuallyEq_of_mem (isOpen_Iio.mem_nhds hr)),
    fun r hr h ↦ h.congr_of_eventuallyEq
      ((e₂.mono Ioi_subset_Ici_self).eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hr)),
    fun r hr₁ hr₂ ↦ ?_⟩
  · rcases key r with ⟨he, -⟩ | ⟨he, -⟩ | ⟨he, -⟩
    · exact h₁.contDiffAt.congr_of_eventuallyEq he
    · exact hχs.contDiffAt.congr_of_eventuallyEq he
    · exact h₂.contDiffAt.congr_of_eventuallyEq he
  · rcases key r with ⟨he, -⟩ | ⟨he, h⟩ | ⟨he, -⟩
    · exact (hc₁ r hr).congr_of_eventuallyEq he
    · exact (hχc r (Ioo_subset_Icc_self h)).congr_of_eventuallyEq he
    · exact (hc₂ r hr).congr_of_eventuallyEq he
  · rcases key r with ⟨he, -⟩ | ⟨he, -⟩ | ⟨he, -⟩
    · rwa [he.iteratedDeriv_eq]
    · rw [he.iteratedDeriv_eq]
      exact hχcv r hr₁ hr₂
    · rwa [he.iteratedDeriv_eq]

/-! ### The smoothed minimum of two shapes over `R` -/

/-- **The smoothed minimum keeps the smaller margin in the first inequality over `R`.** For
`δ > 0` and functions `ρ₁`, `ρ₂` differentiable at `R` with `δ ≤ ρ₁ R` and `δ ≤ ρ₂ R`, the
quantity `1 / ρ - ρ' / R` of `ρ = fun R ↦ -smoothedMax δ (-ρ₁ R) (-ρ₂ R)` at `R` is at least the
smaller of those of `ρ₁` and `ρ₂`. -/
theorem min_le_one_div_smoothedMin_sub_deriv_div {ρ₁ ρ₂ : ℝ → ℝ} {δ : ℝ}
    (h₁ : DifferentiableAt ℝ ρ₁ R) (h₂ : DifferentiableAt ℝ ρ₂ R) (hδ : 0 < δ)
    (hδ₁ : δ ≤ ρ₁ R) (hδ₂ : δ ≤ ρ₂ R) :
    min (1 / ρ₁ R - deriv ρ₁ R / R) (1 / ρ₂ R - deriv ρ₂ R / R) ≤
      1 / -smoothedMax δ (-ρ₁ R) (-ρ₂ R) -
        deriv (fun R ↦ -smoothedMax δ (-ρ₁ R) (-ρ₂ R)) R / R := by
  have hk₁ := one_div_le_one_div_neg_smoothedMax_neg_left hδ hδ₁ hδ₂
  have hk₂ := one_div_le_one_div_neg_smoothedMax_neg_right hδ hδ₁ hδ₂
  rw [deriv_neg_smoothedMax_neg_weighted h₁ h₂]
  obtain ⟨hw₀, hw₁⟩ := one_add_smoothedSign_div_two_mem_Icc δ (ρ₂ R - ρ₁ R)
  set w := (1 + smoothedSign δ (ρ₂ R - ρ₁ R)) / 2
  set k := 1 / -smoothedMax δ (-ρ₁ R) (-ρ₂ R)
  have hm := Convex.min_le_combo (𝕜 := ℝ) (1 / ρ₁ R - deriv ρ₁ R / R)
    (1 / ρ₂ R - deriv ρ₂ R / R) hw₀ (sub_nonneg.2 hw₁) (add_sub_cancel _ _)
  simp only [smul_eq_mul] at hm
  have e : k - (w * deriv ρ₁ R + (1 - w) * deriv ρ₂ R) / R =
      w * (k - deriv ρ₁ R / R) + (1 - w) * (k - deriv ρ₂ R / R) := by ring
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left hk₁ hw₀, mul_le_mul_of_nonneg_left hk₂ (sub_nonneg.2 hw₁)]

/-- A lower bound for the quantity `1 / ρ - ρ'³ / R - ρ''` of the second inequality of
`isConvexShapeOverRAt_iff` for the smoothed minimum. Let `ρ₁`, `ρ₂` be `C²` at `R`, `δ > 0`,
`R > 0`, `δ ≤ ρ₁ R`, `δ ≤ ρ₂ R`, `x = ρ₁' R`, `y = ρ₂' R`, and let
`s = smoothedSign δ (ρ₂ R - ρ₁ R)` and `p = (smoothedAbs δ)'' (ρ₂ R - ρ₁ R)`. Then that quantity
for `ρ = fun R ↦ -smoothedMax δ (-ρ₁ R) (-ρ₂ R)` is at least the combination of those of `ρ₁`
and `ρ₂` with the weights `(1 ± s) / 2`, plus
`p (x - y)² / 2 - (1 - s²) / 2 · (x - y)² (|x| + |y|) / R`. -/
theorem le_one_div_smoothedMin_sub_deriv_pow_three_div_sub_iteratedDeriv_two {ρ₁ ρ₂ : ℝ → ℝ}
    {δ : ℝ} (h₁ : ContDiffAt ℝ 2 ρ₁ R) (h₂ : ContDiffAt ℝ 2 ρ₂ R) (hδ : 0 < δ) (hR : 0 < R)
    (hδ₁ : δ ≤ ρ₁ R) (hδ₂ : δ ≤ ρ₂ R) :
    (1 + smoothedSign δ (ρ₂ R - ρ₁ R)) / 2 *
        (1 / ρ₁ R - deriv ρ₁ R ^ 3 / R - iteratedDeriv 2 ρ₁ R) +
      (1 - smoothedSign δ (ρ₂ R - ρ₁ R)) / 2 *
        (1 / ρ₂ R - deriv ρ₂ R ^ 3 / R - iteratedDeriv 2 ρ₂ R) +
      (iteratedDeriv 2 (smoothedAbs δ) (ρ₂ R - ρ₁ R) * (deriv ρ₁ R - deriv ρ₂ R) ^ 2 / 2 -
        (1 - smoothedSign δ (ρ₂ R - ρ₁ R) ^ 2) / 2 *
          ((deriv ρ₁ R - deriv ρ₂ R) ^ 2 * ((|deriv ρ₁ R| + |deriv ρ₂ R|) / R))) ≤
      1 / -smoothedMax δ (-ρ₁ R) (-ρ₂ R) -
        deriv (fun R ↦ -smoothedMax δ (-ρ₁ R) (-ρ₂ R)) R ^ 3 / R -
        iteratedDeriv 2 (fun R ↦ -smoothedMax δ (-ρ₁ R) (-ρ₂ R)) R := by
  have hk₁ := one_div_le_one_div_neg_smoothedMax_neg_left hδ hδ₁ hδ₂
  have hk₂ := one_div_le_one_div_neg_smoothedMax_neg_right hδ hδ₁ hδ₂
  rw [deriv_neg_smoothedMax_neg_weighted (h₁.differentiableAt two_ne_zero)
    (h₂.differentiableAt two_ne_zero), iteratedDeriv_two_neg_smoothedMax_neg_weighted h₁ h₂]
  obtain ⟨hw₀, hw₁⟩ := one_add_smoothedSign_div_two_mem_Icc δ (ρ₂ R - ρ₁ R)
  set x := deriv ρ₁ R
  set y := deriv ρ₂ R
  set s := smoothedSign δ (ρ₂ R - ρ₁ R)
  set p := iteratedDeriv 2 (smoothedAbs δ) (ρ₂ R - ρ₁ R)
  set k := 1 / -smoothedMax δ (-ρ₁ R) (-ρ₂ R)
  set w := (1 + s) / 2 with hw
  rw [show (1 - s) / 2 = 1 - w by rw [hw]; ring]
  -- The cube of the slope differs from the combination of the cubes by at most
  -- `(1 - s²) / 2 · (x - y)² (|x| + |y|) / R`.
  have hE := div_le_div_of_nonneg_right ((neg_le_abs _).trans
    (abs_mul_pow_three_add_mul_pow_three_sub_pow_three_le (x := x) (y := y) hw₀ hw₁)) hR.le
  have e : 2 * (w * (1 - w)) * ((x - y) ^ 2 * (|x| + |y|)) / R =
      (1 - s ^ 2) / 2 * ((x - y) ^ 2 * ((|x| + |y|) / R)) := by rw [hw]; ring
  rw [e] at hE
  have h₃ := mul_le_mul_of_nonneg_left hk₁ hw₀
  have h₄ := mul_le_mul_of_nonneg_left hk₂ (sub_nonneg.2 hw₁)
  simp only [div_eq_mul_inv] at hE h₃ h₄ ⊢
  linarith

/-- A lower bound for the quantity `(1 + ρ'²) / ρ - ρ''` of the third inequality of
`isConvexShapeOverRAt_iff` for the smoothed minimum `v = -smoothedMax δ (-ρ₁ R) (-ρ₂ R)`. With
`ρ₁`, `ρ₂` `C²` at `R`, `δ > 0`, `δ ≤ ρ₁ R`, `δ ≤ ρ₂ R` and `x`, `y`, `s`, `p` as in
`le_one_div_smoothedMin_sub_deriv_pow_three_div_sub_iteratedDeriv_two`, that quantity for
`ρ = fun R ↦ -smoothedMax δ (-ρ₁ R) (-ρ₂ R)` is at least the combination of those of `ρ₁` and
`ρ₂` with the weights `(1 ± s) / 2`, plus `p (x - y)² / 2 - (1 - s²) / 2 · (x - y)² / (2 v)`. -/
theorem le_one_add_sq_div_smoothedMin_sub_iteratedDeriv_two {ρ₁ ρ₂ : ℝ → ℝ} {δ : ℝ}
    (h₁ : ContDiffAt ℝ 2 ρ₁ R) (h₂ : ContDiffAt ℝ 2 ρ₂ R) (hδ : 0 < δ)
    (hδ₁ : δ ≤ ρ₁ R) (hδ₂ : δ ≤ ρ₂ R) :
    (1 + smoothedSign δ (ρ₂ R - ρ₁ R)) / 2 *
        ((1 + deriv ρ₁ R ^ 2) / ρ₁ R - iteratedDeriv 2 ρ₁ R) +
      (1 - smoothedSign δ (ρ₂ R - ρ₁ R)) / 2 *
        ((1 + deriv ρ₂ R ^ 2) / ρ₂ R - iteratedDeriv 2 ρ₂ R) +
      (iteratedDeriv 2 (smoothedAbs δ) (ρ₂ R - ρ₁ R) * (deriv ρ₁ R - deriv ρ₂ R) ^ 2 / 2 -
        (1 - smoothedSign δ (ρ₂ R - ρ₁ R) ^ 2) / 2 *
          ((deriv ρ₁ R - deriv ρ₂ R) ^ 2 * (1 / (2 * -smoothedMax δ (-ρ₁ R) (-ρ₂ R))))) ≤
      (1 + deriv (fun R ↦ -smoothedMax δ (-ρ₁ R) (-ρ₂ R)) R ^ 2) /
          -smoothedMax δ (-ρ₁ R) (-ρ₂ R) -
        iteratedDeriv 2 (fun R ↦ -smoothedMax δ (-ρ₁ R) (-ρ₂ R)) R := by
  have hv₀ : 0 < -smoothedMax δ (-ρ₁ R) (-ρ₂ R) := by
    linarith [div_two_le_neg_smoothedMax_neg hδ le_rfl hδ₁ hδ₂]
  have hk₁ := one_div_le_one_div_neg_smoothedMax_neg_left hδ hδ₁ hδ₂
  have hk₂ := one_div_le_one_div_neg_smoothedMax_neg_right hδ hδ₁ hδ₂
  rw [deriv_neg_smoothedMax_neg_weighted (h₁.differentiableAt two_ne_zero)
    (h₂.differentiableAt two_ne_zero), iteratedDeriv_two_neg_smoothedMax_neg_weighted h₁ h₂]
  obtain ⟨hw₀, hw₁⟩ := one_add_smoothedSign_div_two_mem_Icc δ (ρ₂ R - ρ₁ R)
  set x := deriv ρ₁ R
  set y := deriv ρ₂ R
  set s := smoothedSign δ (ρ₂ R - ρ₁ R)
  set p := iteratedDeriv 2 (smoothedAbs δ) (ρ₂ R - ρ₁ R)
  set v := -smoothedMax δ (-ρ₁ R) (-ρ₂ R)
  set w := (1 + s) / 2 with hw
  rw [show (1 - s) / 2 = 1 - w by rw [hw]; ring]
  -- The square of the slope falls short of the combination of the squares by
  -- `(1 - s²) / 4 · (x - y)²`.
  have e : (1 + (w * x + (1 - w) * y) ^ 2) / v = w * ((1 + x ^ 2) / v) +
      (1 - w) * ((1 + y ^ 2) / v) - (1 - s ^ 2) / 2 * ((x - y) ^ 2 * (1 / (2 * v))) := by
    rw [hw]; field_simp; ring
  rw [e]
  have h₃ := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hk₁ (by positivity : 0 ≤ 1 + x ^ 2)) hw₀
  have h₄ := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hk₂ (by positivity : 0 ≤ 1 + y ^ 2)) (sub_nonneg.2 hw₁)
  simp only [mul_one_div] at h₃ h₄
  linarith

/-- **The smoothed minimum keeps the smaller margin in the second inequality over `R`.** Let
`ρ₁`, `ρ₂` be `C²` at `R`, `δ > 0`, `R > 0`, `δ ≤ ρ₁ R`, `δ ≤ ρ₂ R` and
`δ (|ρ₁' R| + |ρ₂' R|) ≤ 2 R`. Then the quantity `1 / ρ - ρ'³ / R - ρ''` of
`ρ = fun R ↦ -smoothedMax δ (-ρ₁ R) (-ρ₂ R)` at `R` is at least the smaller of those of `ρ₁` and
`ρ₂`. -/
theorem min_le_one_div_smoothedMin_sub_deriv_pow_three_div_sub_iteratedDeriv_two
    {ρ₁ ρ₂ : ℝ → ℝ} {δ : ℝ} (h₁ : ContDiffAt ℝ 2 ρ₁ R) (h₂ : ContDiffAt ℝ 2 ρ₂ R) (hδ : 0 < δ)
    (hR : 0 < R) (hδ₁ : δ ≤ ρ₁ R) (hδ₂ : δ ≤ ρ₂ R)
    (hδR : δ * (|deriv ρ₁ R| + |deriv ρ₂ R|) ≤ 2 * R) :
    min (1 / ρ₁ R - deriv ρ₁ R ^ 3 / R - iteratedDeriv 2 ρ₁ R)
        (1 / ρ₂ R - deriv ρ₂ R ^ 3 / R - iteratedDeriv 2 ρ₂ R) ≤
      1 / -smoothedMax δ (-ρ₁ R) (-ρ₂ R) -
        deriv (fun R ↦ -smoothedMax δ (-ρ₁ R) (-ρ₂ R)) R ^ 3 / R -
        iteratedDeriv 2 (fun R ↦ -smoothedMax δ (-ρ₁ R) (-ρ₂ R)) R := by
  have h := le_one_div_smoothedMin_sub_deriv_pow_three_div_sub_iteratedDeriv_two h₁ h₂ hδ hR
    hδ₁ hδ₂
  have hT : (|deriv ρ₁ R| + |deriv ρ₂ R|) / R ≤ 2 / δ := by
    rw [div_le_div_iff₀ hR hδ]
    linarith
  have hc := one_sub_smoothedSign_sq_div_two_mul_le hδ (sq_nonneg (deriv ρ₁ R - deriv ρ₂ R)) hT
    (ρ₂ R - ρ₁ R)
  have hs := abs_le.1 (abs_smoothedSign_le_one δ (ρ₂ R - ρ₁ R))
  have hm := Convex.min_le_combo (𝕜 := ℝ) (1 / ρ₁ R - deriv ρ₁ R ^ 3 / R - iteratedDeriv 2 ρ₁ R)
    (1 / ρ₂ R - deriv ρ₂ R ^ 3 / R - iteratedDeriv 2 ρ₂ R)
    (by linarith : 0 ≤ (1 + smoothedSign δ (ρ₂ R - ρ₁ R)) / 2)
    (by linarith : 0 ≤ (1 - smoothedSign δ (ρ₂ R - ρ₁ R)) / 2) (by ring)
  simp only [smul_eq_mul] at hm
  linarith

/-- **The smoothed minimum keeps the smaller margin in the third inequality over `R`.** Let
`ρ₁`, `ρ₂` be `C²` at `R`, `δ > 0`, `δ ≤ ρ₁ R` and `δ ≤ ρ₂ R`. Then the quantity
`(1 + ρ'²) / ρ - ρ''` of `ρ = fun R ↦ -smoothedMax δ (-ρ₁ R) (-ρ₂ R)` at `R` is at least the
smaller of those of `ρ₁` and `ρ₂`. -/
theorem min_le_one_add_sq_div_smoothedMin_sub_iteratedDeriv_two {ρ₁ ρ₂ : ℝ → ℝ} {δ : ℝ}
    (h₁ : ContDiffAt ℝ 2 ρ₁ R) (h₂ : ContDiffAt ℝ 2 ρ₂ R) (hδ : 0 < δ)
    (hδ₁ : δ ≤ ρ₁ R) (hδ₂ : δ ≤ ρ₂ R) :
    min ((1 + deriv ρ₁ R ^ 2) / ρ₁ R - iteratedDeriv 2 ρ₁ R)
        ((1 + deriv ρ₂ R ^ 2) / ρ₂ R - iteratedDeriv 2 ρ₂ R) ≤
      (1 + deriv (fun R ↦ -smoothedMax δ (-ρ₁ R) (-ρ₂ R)) R ^ 2) /
          -smoothedMax δ (-ρ₁ R) (-ρ₂ R) -
        iteratedDeriv 2 (fun R ↦ -smoothedMax δ (-ρ₁ R) (-ρ₂ R)) R := by
  have h := le_one_add_sq_div_smoothedMin_sub_iteratedDeriv_two h₁ h₂ hδ hδ₁ hδ₂
  -- The smoothed minimum is at least `δ / 2`, so `1 / (2 v) ≤ 1 / δ ≤ 2 / δ`.
  have hv : δ / 2 ≤ -smoothedMax δ (-ρ₁ R) (-ρ₂ R) :=
    div_two_le_neg_smoothedMax_neg hδ le_rfl hδ₁ hδ₂
  have hT : 1 / (2 * -smoothedMax δ (-ρ₁ R) (-ρ₂ R)) ≤ 2 / δ := by
    rw [div_le_div_iff₀ (by linarith) hδ]
    linarith
  have hc := one_sub_smoothedSign_sq_div_two_mul_le hδ (sq_nonneg (deriv ρ₁ R - deriv ρ₂ R)) hT
    (ρ₂ R - ρ₁ R)
  have hs := abs_le.1 (abs_smoothedSign_le_one δ (ρ₂ R - ρ₁ R))
  have hm := Convex.min_le_combo (𝕜 := ℝ) ((1 + deriv ρ₁ R ^ 2) / ρ₁ R - iteratedDeriv 2 ρ₁ R)
    ((1 + deriv ρ₂ R ^ 2) / ρ₂ R - iteratedDeriv 2 ρ₂ R)
    (by linarith : 0 ≤ (1 + smoothedSign δ (ρ₂ R - ρ₁ R)) / 2)
    (by linarith : 0 ≤ (1 - smoothedSign δ (ρ₂ R - ρ₁ R)) / 2) (by ring)
  simp only [smul_eq_mul] at hm
  linarith

/-- For `δ > 0` with `δ ≤ ρ₁ R` and `δ ≤ ρ₂ R`, the smoothed minimum of two functions
differentiable at `R` that satisfy the criterion over `R` there satisfies it if and only if it
satisfies the last two inequalities of `isConvexShapeOverRAt_iff`: the first three conditions
hold already. -/
theorem isConvexShapeOverRAt_smoothedMin_iff {ρ₁ ρ₂ : ℝ → ℝ} {δ : ℝ}
    (h₁ : DifferentiableAt ℝ ρ₁ R) (h₂ : DifferentiableAt ℝ ρ₂ R) (hδ : 0 < δ)
    (hc₁ : IsConvexShapeOverRAt ρ₁ R) (hc₂ : IsConvexShapeOverRAt ρ₂ R)
    (hδ₁ : δ ≤ ρ₁ R) (hδ₂ : δ ≤ ρ₂ R) :
    IsConvexShapeOverRAt (fun R ↦ -smoothedMax δ (-ρ₁ R) (-ρ₂ R)) R ↔
      iteratedDeriv 2 (fun R ↦ -smoothedMax δ (-ρ₁ R) (-ρ₂ R)) R <
          1 / -smoothedMax δ (-ρ₁ R) (-ρ₂ R) -
            deriv (fun R ↦ -smoothedMax δ (-ρ₁ R) (-ρ₂ R)) R ^ 3 / R ∧
        iteratedDeriv 2 (fun R ↦ -smoothedMax δ (-ρ₁ R) (-ρ₂ R)) R <
          (1 + deriv (fun R ↦ -smoothedMax δ (-ρ₁ R) (-ρ₂ R)) R ^ 2) /
            -smoothedMax δ (-ρ₁ R) (-ρ₂ R) := by
  have h := min_le_one_div_smoothedMin_sub_deriv_div h₁ h₂ hδ hδ₁ hδ₂
  have hm := lt_min (sub_pos.2 hc₁.deriv_div_lt_one_div) (sub_pos.2 hc₂.deriv_div_lt_one_div)
  have hv₀ : 0 < -smoothedMax δ (-ρ₁ R) (-ρ₂ R) := by
    linarith [div_two_le_neg_smoothedMax_neg hδ le_rfl hδ₁ hδ₂]
  rw [isConvexShapeOverRAt_iff]
  exact ⟨fun h ↦ h.2.2.2, fun h' ↦ ⟨hc₁.pos, hv₀, by linarith, h'⟩⟩

/-- **The smoothed minimum of two shapes over `R`, for a moderate width.** Let `ρ₁`, `ρ₂` be
`C²` at `R` and satisfy the criterion over `R` there, and let `δ > 0` with `δ ≤ ρ₁ R`,
`δ ≤ ρ₂ R` and `δ (|ρ₁' R| + |ρ₂' R|) ≤ 2 R`. Then `R ↦ -smoothedMax δ (-ρ₁ R) (-ρ₂ R)`
satisfies the criterion over `R` at `R`. -/
theorem isConvexShapeOverRAt_smoothedMin {ρ₁ ρ₂ : ℝ → ℝ} {δ : ℝ} (h₁ : ContDiffAt ℝ 2 ρ₁ R)
    (h₂ : ContDiffAt ℝ 2 ρ₂ R) (hδ : 0 < δ) (hc₁ : IsConvexShapeOverRAt ρ₁ R)
    (hc₂ : IsConvexShapeOverRAt ρ₂ R) (hδ₁ : δ ≤ ρ₁ R) (hδ₂ : δ ≤ ρ₂ R)
    (hδR : δ * (|deriv ρ₁ R| + |deriv ρ₂ R|) ≤ 2 * R) :
    IsConvexShapeOverRAt (fun R ↦ -smoothedMax δ (-ρ₁ R) (-ρ₂ R)) R := by
  have h := min_le_one_div_smoothedMin_sub_deriv_pow_three_div_sub_iteratedDeriv_two h₁ h₂ hδ
    hc₁.pos hδ₁ hδ₂ hδR
  have h' := min_le_one_add_sq_div_smoothedMin_sub_iteratedDeriv_two h₁ h₂ hδ hδ₁ hδ₂
  have hm := lt_min (sub_pos.2 hc₁.iteratedDeriv_two_lt) (sub_pos.2 hc₂.iteratedDeriv_two_lt)
  have hm' := lt_min (sub_pos.2 hc₁.iteratedDeriv_two_lt_one_add_sq_div)
    (sub_pos.2 hc₂.iteratedDeriv_two_lt_one_add_sq_div)
  exact (isConvexShapeOverRAt_smoothedMin_iff (h₁.differentiableAt two_ne_zero)
    (h₂.differentiableAt two_ne_zero) hδ hc₁ hc₂ hδ₁ hδ₂).2 ⟨by linarith, by linarith⟩

/-- The pointwise step of `exists_pos_forall_isConvexShapeOverRAt_smoothedMin`: at `R`, the
smoothed minimum `-smoothedMax δ (-ρ₁ R) (-ρ₂ R)` of two shapes over `R` is one, given a common
lower bound `μ ≥ δ` of `ρ₁ R` and `ρ₂ R`, a margin `a` in the last two inequalities of
`isConvexShapeOverRAt_iff` for both, bounds `Q` and `G` for the errors, and the bound of
`exists_pos_forall_one_sub_smoothedSign_sq_div_two_mul_lt` at `ρ₂ R - ρ₁ R`. -/
private theorem isConvexShapeOverRAt_smoothedMin_of_le {ρ₁ ρ₂ : ℝ → ℝ} {δ μ a G Q : ℝ}
    (h₁ : ContDiffAt ℝ 2 ρ₁ R) (h₂ : ContDiffAt ℝ 2 ρ₂ R) (hδ : 0 < δ)
    (hc₁ : IsConvexShapeOverRAt ρ₁ R) (hc₂ : IsConvexShapeOverRAt ρ₂ R)
    (hμ₁ : μ ≤ ρ₁ R) (hμ₂ : μ ≤ ρ₂ R) (hδμ : δ ≤ μ)
    (ha₁ : a ≤ 1 / ρ₁ R - deriv ρ₁ R ^ 3 / R - iteratedDeriv 2 ρ₁ R)
    (ha₂ : a ≤ 1 / ρ₂ R - deriv ρ₂ R ^ 3 / R - iteratedDeriv 2 ρ₂ R)
    (hb₁ : a ≤ (1 + deriv ρ₁ R ^ 2) / ρ₁ R - iteratedDeriv 2 ρ₁ R)
    (hb₂ : a ≤ (1 + deriv ρ₂ R ^ 2) / ρ₂ R - iteratedDeriv 2 ρ₂ R)
    (hQ : (|deriv ρ₁ R| + |deriv ρ₂ R|) / R + 1 / μ ≤ Q)
    (hG : (deriv ρ₁ R - deriv ρ₂ R) ^ 2 * Q ≤ G)
    (hL : ∀ {g T : ℝ}, 0 ≤ g → 0 ≤ T → T ≤ Q → g * T ≤ G →
      (1 - smoothedSign δ (ρ₂ R - ρ₁ R) ^ 2) / 2 * (g * T) <
        a + iteratedDeriv 2 (smoothedAbs δ) (ρ₂ R - ρ₁ R) * g / 2) :
    IsConvexShapeOverRAt (fun R ↦ -smoothedMax δ (-ρ₁ R) (-ρ₂ R)) R := by
  have hR := hc₁.pos
  have hμ : 0 < μ := hδ.trans_le hδμ
  have hδ₁ := hδμ.trans hμ₁
  have hδ₂ := hδμ.trans hμ₂
  have h := le_one_div_smoothedMin_sub_deriv_pow_three_div_sub_iteratedDeriv_two h₁ h₂ hδ hR
    hδ₁ hδ₂
  have h' := le_one_add_sq_div_smoothedMin_sub_iteratedDeriv_two h₁ h₂ hδ hδ₁ hδ₂
  -- The smoothed minimum is at least `μ / 2`, so `1 / (2 v) ≤ 1 / μ`.
  have hv : μ / 2 ≤ -smoothedMax δ (-ρ₁ R) (-ρ₂ R) :=
    div_two_le_neg_smoothedMax_neg hδ hδμ hμ₁ hμ₂
  have hvμ : 1 / (2 * -smoothedMax δ (-ρ₁ R) (-ρ₂ R)) ≤ 1 / μ :=
    one_div_le_one_div_of_le hμ (by linarith)
  set x := deriv ρ₁ R
  set y := deriv ρ₂ R
  set s := smoothedSign δ (ρ₂ R - ρ₁ R)
  set p := iteratedDeriv 2 (smoothedAbs δ) (ρ₂ R - ρ₁ R)
  have hs : -1 ≤ s ∧ s ≤ 1 := abs_le.1 (abs_smoothedSign_le_one δ _)
  have hw₀ : 0 ≤ (1 + s) / 2 := by linarith
  have hw₁ : 0 ≤ (1 - s) / 2 := by linarith
  have h1s : 0 ≤ (1 - s ^ 2) / 2 * (x - y) ^ 2 := by
    have : 0 ≤ 1 - s ^ 2 := by nlinarith
    positivity
  have hT₀ : 0 ≤ (|x| + |y|) / R := by positivity
  have hμ₀ : 0 ≤ 1 / μ := by positivity
  have hgQ (T : ℝ) (hT : T ≤ Q) : (x - y) ^ 2 * T ≤ G :=
    (mul_le_mul_of_nonneg_left hT (sq_nonneg _)).trans hG
  have hL₁ : (1 - s ^ 2) / 2 * ((x - y) ^ 2 * ((|x| + |y|) / R)) < a + p * (x - y) ^ 2 / 2 :=
    hL (sq_nonneg (x - y)) hT₀ (by linarith) (hgQ _ (by linarith))
  have hL₂ : (1 - s ^ 2) / 2 * ((x - y) ^ 2 * (1 / μ)) < a + p * (x - y) ^ 2 / 2 :=
    hL (sq_nonneg (x - y)) hμ₀ (by linarith) (hgQ _ (by linarith))
  have hE : (1 - s ^ 2) / 2 * ((x - y) ^ 2 * (1 / (2 * -smoothedMax δ (-ρ₁ R) (-ρ₂ R)))) ≤
      (1 - s ^ 2) / 2 * ((x - y) ^ 2 * (1 / μ)) := by
    rw [← mul_assoc, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left hvμ h1s
  refine (isConvexShapeOverRAt_smoothedMin_iff (h₁.differentiableAt two_ne_zero)
    (h₂.differentiableAt two_ne_zero) hδ hc₁ hc₂ hδ₁ hδ₂).2 ⟨?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left ha₁ hw₀, mul_le_mul_of_nonneg_left ha₂ hw₁]
  · nlinarith [mul_le_mul_of_nonneg_left hb₁ hw₀, mul_le_mul_of_nonneg_left hb₂ hw₁]

/-- **A uniform width for the smoothed minimum of two shapes over `R`.** Given `a > 0`, `μ > 0`
and bounds `B` and `Q`, there is `δ₀ > 0` such that, for every `δ ∈ (0, δ₀]`, the smoothed
minimum `R ↦ -smoothedMax δ (-ρ₁ R) (-ρ₂ R)` of two functions `ρ₁`, `ρ₂` satisfies the criterion
over `R` at each `R` where both are `C²` and satisfy it, where `μ ≤ ρ₁ R` and `μ ≤ ρ₂ R`, where
both satisfy the last two inequalities of `isConvexShapeOverRAt_iff` with margin at least `a`,
and where `(ρ₁' - ρ₂')² ≤ B` and `(|ρ₁'| + |ρ₂'|) / R ≤ Q`.

So `δ₀` depends only on `a`, `μ`, `B` and `Q`, not on the shapes. -/
theorem exists_pos_forall_isConvexShapeOverRAt_smoothedMin {a μ : ℝ} (ha : 0 < a) (hμ : 0 < μ)
    (B Q : ℝ) :
    ∃ δ₀ > 0, ∀ δ ∈ Set.Ioc 0 δ₀, ∀ {ρ₁ ρ₂ : ℝ → ℝ} {R : ℝ}, ContDiffAt ℝ 2 ρ₁ R →
      ContDiffAt ℝ 2 ρ₂ R → IsConvexShapeOverRAt ρ₁ R → IsConvexShapeOverRAt ρ₂ R →
      μ ≤ ρ₁ R → μ ≤ ρ₂ R →
      a ≤ 1 / ρ₁ R - deriv ρ₁ R ^ 3 / R - iteratedDeriv 2 ρ₁ R →
      a ≤ 1 / ρ₂ R - deriv ρ₂ R ^ 3 / R - iteratedDeriv 2 ρ₂ R →
      a ≤ (1 + deriv ρ₁ R ^ 2) / ρ₁ R - iteratedDeriv 2 ρ₁ R →
      a ≤ (1 + deriv ρ₂ R ^ 2) / ρ₂ R - iteratedDeriv 2 ρ₂ R →
      (deriv ρ₁ R - deriv ρ₂ R) ^ 2 ≤ B → (|deriv ρ₁ R| + |deriv ρ₂ R|) / R ≤ Q →
      IsConvexShapeOverRAt (fun R ↦ -smoothedMax δ (-ρ₁ R) (-ρ₂ R)) R := by
  set Q' := |Q| + 1 / μ
  have hQ' : 0 < Q' := by positivity
  obtain ⟨δ₁, hδ₁, hL⟩ := exists_pos_forall_one_sub_smoothedSign_sq_div_two_mul_lt ha (|B| * Q') Q'
  refine ⟨min δ₁ μ, lt_min hδ₁ hμ, ?_⟩
  intro δ hδ ρ₁ ρ₂ R h₁ h₂ hc₁ hc₂ hμ₁ hμ₂ ha₁ ha₂ hb₁ hb₂ hB hQ
  exact isConvexShapeOverRAt_smoothedMin_of_le h₁ h₂ hδ.1 hc₁ hc₂ hμ₁ hμ₂
    (hδ.2.trans (min_le_right _ _)) ha₁ ha₂ hb₁ hb₂
    (add_le_add_left (hQ.trans (le_abs_self Q)) _)
    (mul_le_mul_of_nonneg_right (hB.trans (le_abs_self B)) hQ'.le)
    fun hg hT hTQ hgT ↦ hL δ hδ.1 (hδ.2.trans (min_le_left _ _)) hg hT hTQ hgT _

/-- **The smoothed minimum of a compact family of pairs of shapes over `R`.** Let `K` be a
compact set of parameters, and for `p ∈ K` let `M p` and `A p` be `C²` at, and satisfy the
criterion over `R` at, every point of `[R₁, R₂]`, with values and first two derivatives jointly
continuous in `(p, R)` on `K × [R₁, R₂]`. Then there is `δ₀ > 0` such that, for every
`δ ∈ (0, δ₀]` and `p ∈ K`, `R ↦ -smoothedMax δ (-M p R) (-A p R)` satisfies the criterion over
`R` at every point of `[R₁, R₂]`. -/
theorem exists_forall_isConvexShapeOverRAt_smoothedMin {P : Type*} [TopologicalSpace P]
    {K : Set P} (hK : IsCompact K) {M A : P → ℝ → ℝ} {R₁ R₂ : ℝ}
    (hM : ∀ p ∈ K, ∀ R ∈ Set.Icc R₁ R₂, ContDiffAt ℝ 2 (M p) R)
    (hA : ∀ p ∈ K, ∀ R ∈ Set.Icc R₁ R₂, ContDiffAt ℝ 2 (A p) R)
    (hcM : ∀ p ∈ K, ∀ R ∈ Set.Icc R₁ R₂, IsConvexShapeOverRAt (M p) R)
    (hcA : ∀ p ∈ K, ∀ R ∈ Set.Icc R₁ R₂, IsConvexShapeOverRAt (A p) R)
    (hdM : ∀ k ≤ 2, ContinuousOn (fun q : P × ℝ ↦ iteratedDeriv k (M q.1) q.2)
      (K ×ˢ Set.Icc R₁ R₂))
    (hdA : ∀ k ≤ 2, ContinuousOn (fun q : P × ℝ ↦ iteratedDeriv k (A q.1) q.2)
      (K ×ˢ Set.Icc R₁ R₂)) :
    ∃ δ₀ > 0, ∀ δ ∈ Set.Ioc 0 δ₀, ∀ p ∈ K, ∀ R ∈ Set.Icc R₁ R₂,
      IsConvexShapeOverRAt (fun R ↦ -smoothedMax δ (-M p R) (-A p R)) R := by
  set S := K ×ˢ Set.Icc R₁ R₂
  have hS : IsCompact S := hK.prod isCompact_Icc
  have hR₀ : ∀ q ∈ S, q.2 ≠ 0 := fun q hq ↦ (hcM q.1 hq.1 q.2 hq.2).pos.ne'
  have hvM := ContinuousOn.uncurry_of_iteratedDeriv hdM
  have hvA := ContinuousOn.uncurry_of_iteratedDeriv hdA
  have hsM := ContinuousOn.deriv_of_iteratedDeriv hdM one_le_two
  have hsA := ContinuousOn.deriv_of_iteratedDeriv hdA one_le_two
  -- A common margin in the last two inequalities of `isConvexShapeOverRAt_iff` for a family.
  have margin {F : P → ℝ → ℝ}
      (hd : ∀ k ≤ 2, ContinuousOn (fun q : P × ℝ ↦ iteratedDeriv k (F q.1) q.2) S)
      (hc : ∀ p ∈ K, ∀ R ∈ Set.Icc R₁ R₂, IsConvexShapeOverRAt (F p) R) :
      ∃ a > 0, ∀ q ∈ S,
        a ≤ 1 / F q.1 q.2 - deriv (F q.1) q.2 ^ 3 / q.2 - iteratedDeriv 2 (F q.1) q.2 ∧
        a ≤ (1 + deriv (F q.1) q.2 ^ 2) / F q.1 q.2 - iteratedDeriv 2 (F q.1) q.2 := by
    have hv := ContinuousOn.uncurry_of_iteratedDeriv hd
    have hs := ContinuousOn.deriv_of_iteratedDeriv hd one_le_two
    have hne : ∀ q ∈ S, F q.1 q.2 ≠ 0 := fun q hq ↦ (hc q.1 hq.1 q.2 hq.2).pos_value.ne'
    obtain ⟨a, ha, hA⟩ := hS.exists_forall_le'
      (((continuousOn_const.div hv hne).sub ((hs.pow 3).div continuousOn_snd hR₀)).sub
        (hd 2 le_rfl))
      fun q hq ↦ sub_pos.2 (hc q.1 hq.1 q.2 hq.2).iteratedDeriv_two_lt
    obtain ⟨b, hb, hB⟩ := hS.exists_forall_le'
      (((continuousOn_const.add (hs.pow 2)).div hv hne).sub (hd 2 le_rfl))
      fun q hq ↦ sub_pos.2 (hc q.1 hq.1 q.2 hq.2).iteratedDeriv_two_lt_one_add_sq_div
    exact ⟨min a b, lt_min ha hb, fun q hq ↦
      ⟨(min_le_left _ _).trans (hA q hq), (min_le_right _ _).trans (hB q hq)⟩⟩
  obtain ⟨a₁, ha₁, hA₁⟩ := margin hdM hcM
  obtain ⟨a₂, ha₂, hA₂⟩ := margin hdA hcA
  -- A positive lower bound `μ` for both families, and bounds on the error terms.
  obtain ⟨μ, hμ, hμS⟩ := hS.exists_forall_le'
    (continuous_min.comp_continuousOn (hvM.prodMk hvA)) fun q hq ↦
      lt_min (hcM q.1 hq.1 q.2 hq.2).pos_value (hcA q.1 hq.1 q.2 hq.2).pos_value
  obtain ⟨Q, hQ⟩ := hS.exists_bound_of_continuousOn
    ((hsM.abs.add hsA.abs).div continuousOn_snd hR₀)
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn ((hsM.sub hsA).pow 2)
  obtain ⟨δ₀, hδ₀, h⟩ :=
    exists_pos_forall_isConvexShapeOverRAt_smoothedMin (lt_min ha₁ ha₂) hμ B Q
  refine ⟨δ₀, hδ₀, fun δ hδ p hp R hR ↦ ?_⟩
  have hq : (p, R) ∈ S := ⟨hp, hR⟩
  have e₁ := hA₁ (p, R) hq
  have e₂ := hA₂ (p, R) hq
  have hμq : μ ≤ min (M p R) (A p R) := hμS (p, R) hq
  exact h δ hδ (hM p hp R hR) (hA p hp R hR) (hcM p hp R hR) (hcA p hp R hR)
    (hμq.trans (min_le_left _ _)) (hμq.trans (min_le_right _ _))
    ((min_le_left _ _).trans e₁.1) ((min_le_right _ _).trans e₂.1)
    ((min_le_left _ _).trans e₁.2) ((min_le_right _ _).trans e₂.2)
    ((Real.le_norm_self _).trans (hB _ hq)) ((Real.le_norm_self _).trans (hQ _ hq))

/-- **The smoothed minimum of two shapes over `R`.** Let `ρ₁` and `ρ₂` be `C²` and satisfy the
criterion over `R` at every point of `[R₁, R₂]`, and let `O` be a neighbourhood of the points of
`[R₁, R₂]` where they cross. Then some `ρ`, as smooth as `ρ₁` and `ρ₂` are (so at least `C²`),
satisfies the criterion over `R` at every point of `[R₁, R₂]` and equals `min (ρ₁ R) (ρ₂ R)`
at the points of `[R₁, R₂]` outside `O`.

The function is `R ↦ -smoothedMax δ (-ρ₁ R) (-ρ₂ R)` for `δ` small. For graphs `r = ρ (R)` the
side of `r` small is the inside, so two insides meet in the minimum of the graphs, as they meet in
the maximum of the shapes in `exists_isConvexShapeAt_eq_max`. As there, the crossings need not be
transversal. -/
theorem exists_isConvexShapeOverRAt_eq_min {ρ₁ ρ₂ : ℝ → ℝ} {R₁ R₂ : ℝ} {O : Set ℝ}
    (h₁ : ContDiff ℝ 2 ρ₁) (h₂ : ContDiff ℝ 2 ρ₂)
    (hc₁ : ∀ R ∈ Set.Icc R₁ R₂, IsConvexShapeOverRAt ρ₁ R)
    (hc₂ : ∀ R ∈ Set.Icc R₁ R₂, IsConvexShapeOverRAt ρ₂ R)
    (hO : O ∈ 𝓝ˢ (Set.Icc R₁ R₂ ∩ {R | ρ₁ R = ρ₂ R})) :
    ∃ ρ : ℝ → ℝ, (∀ n : ℕ∞, ContDiff ℝ n ρ₁ → ContDiff ℝ n ρ₂ → ContDiff ℝ n ρ) ∧
      (∀ R ∈ Set.Icc R₁ R₂, IsConvexShapeOverRAt ρ R) ∧
      ∀ R ∈ Set.Icc R₁ R₂ \ O, ρ R = min (ρ₁ R) (ρ₂ R) := by
  obtain ⟨δ₀, hδ₀, h⟩ := exists_forall_isConvexShapeOverRAt_smoothedMin isCompact_univ
    (M := fun _ : Unit ↦ ρ₁) (A := fun _ ↦ ρ₂) (fun _ _ _ _ ↦ h₁.contDiffAt)
    (fun _ _ _ _ ↦ h₂.contDiffAt) (fun _ _ ↦ hc₁) (fun _ _ ↦ hc₂)
    (h₁.continuousOn_iteratedDeriv_snd le_rfl)
    (h₂.continuousOn_iteratedDeriv_snd le_rfl)
  -- A lower bound `β` for `|ρ₁ - ρ₂|` on `[R₁, R₂]` outside `O`.
  obtain ⟨β, hβ, hβD⟩ := isCompact_Icc.exists_pos_forall_le_abs_sub_of_mem_nhdsSet
    h₁.continuous.continuousOn h₂.continuous.continuousOn hO
  set δ := min δ₀ β
  have hδ : 0 < δ := lt_min hδ₀ hβ
  refine ⟨fun R ↦ -smoothedMax δ (-ρ₁ R) (-ρ₂ R), fun n hn₁ hn₂ ↦
    ((contDiff_smoothedMax δ).comp (hn₁.neg.prodMk hn₂.neg)).neg,
    fun R hR ↦ h δ ⟨hδ, min_le_left _ _⟩ () (Set.mem_univ _) R hR, fun R hR ↦ ?_⟩
  have h : δ ≤ |-ρ₁ R - -ρ₂ R| := by
    rw [neg_sub_neg, abs_sub_comm]
    exact (min_le_right _ _).trans (hβD R hR)
  -- `change` only beta-reduces the application of `fun R ↦ …` to `R`.
  change -smoothedMax δ (-ρ₁ R) (-ρ₂ R) = min (ρ₁ R) (ρ₂ R)
  rw [smoothedMax_eq_max hδ h, max_neg_neg, neg_neg]

end SymplecticGeometry

end
