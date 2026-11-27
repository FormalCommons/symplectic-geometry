/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.SpecialShape

import Mathlib.Analysis.Calculus.Deriv.Inv
import SymplecticGeometry.Analysis.Calculus.IteratedDeriv.Comp
import SymplecticGeometry.Analysis.SpecialFunctions.Sqrt
import SymplecticGeometry.Analysis.SpecialFunctions.SmoothTransition.Deriv
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
(`SymplecticGeometry.deriv_le_of_cutoff_bounds`). The bounds on `p` and `q` hold once `L` is
large compared with bounds on `smoothTransition'`, `smoothTransition''` and
`x smoothTransition'' x` (`Real.smoothTransition.abs_deriv_sub_div_le`). The first two
derivatives of the leaf are `SymplecticGeometry.deriv_cutoff_add_sqrt` and
`SymplecticGeometry.iteratedDeriv_two_cutoff_add_sqrt`, and together these give
`SymplecticGeometry.isConvexShapeAt_cutoff_add_sqrt_of_two_le`.

## The leaves `sqrtAddLeaf`

* `SymplecticGeometry.sqrtAddLeaf L δ ℓ`: the leaf with `b = δ / 8 + ℓ` and
  `c = 64 δ² + ℓ²`. It is `√(64 r² - 64 δ²) + δ / 8 + ℓ` up to `2 δ`
  (`SymplecticGeometry.sqrtAddLeaf_of_le`) and the standard shape `√(64 r² + ℓ²)` from `(2 + L) δ`
  on (`SymplecticGeometry.sqrtAddLeaf_of_ge`); the leaves for `δ` are those for `δ = 1` rescaled
  (`SymplecticGeometry.sqrtAddLeaf_eq_mul_sqrtAddLeaf_one`).
* `SymplecticGeometry.exists_isConvexShapeAt_sqrtAddLeaf`: for `L` large enough, every leaf with
  `ℓ ∈ [0, 15 δ / 2]` is an `i`-convex shape at every `r > δ`. For `δ = 1` and `r < 2` the leaf is,
  near `r`, the shape `√(64 r² - 64)` of `SymplecticGeometry.isConvexShapeAt_sqrt_sub` plus a
  constant `≥ 0`; for `r ≥ 2` the shared estimate applies, as `b ≤ 61 / 8` and `c ≤ 121`.
* The family is smooth in `(ℓ, r)` on `r > δ` (`SymplecticGeometry.contDiffOn_uncurry_sqrtAddLeaf`),
  the slope of each leaf tends to `+∞` at `δ` (`SymplecticGeometry.tendsto_deriv_sqrtAddLeaf`),
  and at each `r > δ` the leaves increase strictly with `ℓ ≥ 0`
  (`SymplecticGeometry.strictMonoOn_sqrtAddLeaf`). The bounds
  `8 √(r² - δ²) ≤ sqrtAddLeaf L δ ℓ r ≤ δ / 8 + ℓ + (8 r + ℓ)` and, for large `L`, the slope bound
  `11` from `2 δ` on are `SymplecticGeometry.eight_mul_sqrt_le_sqrtAddLeaf`,
  `SymplecticGeometry.sqrtAddLeaf_le` and `SymplecticGeometry.deriv_sqrtAddLeaf_le`.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  §4.6: Proposition 4.27.
-/

public section

namespace SymplecticGeometry

open Real Set Filter Topology
open scoped ContDiff

variable {δ : ℝ}

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
theorem deriv_cutoff_add_sqrt {L b c x : ℝ} (hc : 0 ≤ c) (hx : 1 < x) :
    deriv (fun x ↦ b * (1 - smoothTransition ((x - 2) / L)) +
        √(64 * x ^ 2 - 64 + c * smoothTransition ((x - 2) / L))) x =
      -b * (deriv smoothTransition ((x - 2) / L) / L) +
        (128 * x + c * (deriv smoothTransition ((x - 2) / L) / L)) /
          (2 * √(64 * x ^ 2 - 64 + c * smoothTransition ((x - 2) / L))) := by
  have hpos : 0 < 64 * x ^ 2 - 64 + c * smoothTransition ((x - 2) / L) := by
    nlinarith [mul_nonneg hc (smoothTransition.nonneg ((x - 2) / L))]
  have hH := (((hasDerivAt_id' x).sub_const 2).div_const L).smoothTransition
  have hF := (((hasDerivAt_pow 2 x).const_mul 64).sub_const 64).add (hH.const_mul c)
  refine HasDerivAt.deriv ?_
  refine (((hH.const_sub 1).const_mul b).add (hF.sqrt hpos.ne')).congr_deriv ?_
  simp only [Pi.add_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  ring

/-- The second derivative at `x > 1` of the cutoff leaf
`b (1 - H x) + √(64 x² - 64 + c H x)` for `δ = 1`, with the cutoff
`H x = smoothTransition ((x - 2) / L)`, for `0 ≤ c`. -/
theorem iteratedDeriv_two_cutoff_add_sqrt {L b c x : ℝ} (hc : 0 ≤ c) (hx : 1 < x) :
    iteratedDeriv 2 (fun x ↦ b * (1 - smoothTransition ((x - 2) / L)) +
        √(64 * x ^ 2 - 64 + c * smoothTransition ((x - 2) / L))) x =
      -b * (deriv (deriv smoothTransition) ((x - 2) / L) / L ^ 2) +
        (128 + c * (deriv (deriv smoothTransition) ((x - 2) / L) / L ^ 2)) /
          (2 * √(64 * x ^ 2 - 64 + c * smoothTransition ((x - 2) / L))) -
        (128 * x + c * (deriv smoothTransition ((x - 2) / L) / L)) ^ 2 /
          (4 * √(64 * x ^ 2 - 64 + c * smoothTransition ((x - 2) / L)) ^ 3) := by
  have hpos : 0 < 64 * x ^ 2 - 64 + c * smoothTransition ((x - 2) / L) := by
    nlinarith [mul_nonneg hc (smoothTransition.nonneg ((x - 2) / L))]
  have hev : deriv (fun x ↦ b * (1 - smoothTransition ((x - 2) / L)) +
        √(64 * x ^ 2 - 64 + c * smoothTransition ((x - 2) / L))) =ᶠ[𝓝 x] fun y ↦
      -b * (deriv smoothTransition ((y - 2) / L) / L) +
        (128 * y + c * (deriv smoothTransition ((y - 2) / L) / L)) /
          (2 * √(64 * y ^ 2 - 64 + c * smoothTransition ((y - 2) / L))) := by
    filter_upwards [lt_mem_nhds hx] with y hy using deriv_cutoff_add_sqrt hc hy
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

/-- The cutoff leaf `b (1 - H x) + √(64 x² - 64 + c H x)` for `δ = 1`, with the cutoff
`H x = smoothTransition ((x - 2) / L)`, is an `i`-convex shape at every `r ≥ 2`, for
`0 ≤ b ≤ 8` and `0 ≤ c ≤ 128`, once `L ≥ 1` is large compared with bounds `A` of
`smoothTransition'`, `B` of `smoothTransition''` and `M` of `x smoothTransition'' x`. -/
theorem isConvexShapeAt_cutoff_add_sqrt_of_two_le {A B M L b c r : ℝ}
    (hA : ∀ x, |deriv smoothTransition x| ≤ A)
    (hB : ∀ x, |deriv (deriv smoothTransition) x| ≤ B)
    (hM : ∀ x, |x * deriv (deriv smoothTransition) x| ≤ M)
    (hL₁ : 1 ≤ L) (hL : 1024 * (A + 2 * B + M) ≤ L) (hb₀ : 0 ≤ b) (hb : b ≤ 8) (hc₀ : 0 ≤ c)
    (hc : c ≤ 128) (hr : 2 ≤ r) :
    IsConvexShapeAt (fun x ↦ b * (1 - smoothTransition ((x - 2) / L)) +
      √(64 * x ^ 2 - 64 + c * smoothTransition ((x - 2) / L))) r := by
  have hr₁ : 1 < r := by linarith
  obtain ⟨hp, hq⟩ := smoothTransition.abs_deriv_sub_div_le hA hB hM zero_le_two hL₁
    (ε := 1 / 1024) (by linarith) r
  exact isConvexShapeAt_of_cutoff_bounds hb₀ hb hc₀ hc (smoothTransition.nonneg _)
    (smoothTransition.le_one _) hp hq hr (sqrt_nonneg _)
    (sq_sqrt (by nlinarith [mul_nonneg hc₀ (smoothTransition.nonneg ((r - 2) / L))])) rfl
    (deriv_cutoff_add_sqrt hc₀ hr₁) (iteratedDeriv_two_cutoff_add_sqrt hc₀ hr₁)

/-- The slope of the cutoff leaf `b (1 - H x) + √(64 x² - 64 + c H x)` for `δ = 1`, with the
cutoff `H x = smoothTransition ((x - 2) / L)`, is at most `11` at every `r ≥ 2`, for
`0 ≤ b ≤ 8` and `0 ≤ c ≤ 128`, once `L ≥ 1` is large compared with bounds `A` of
`smoothTransition'`, `B` of `smoothTransition''` and `M` of `x smoothTransition'' x`. -/
theorem deriv_cutoff_add_sqrt_le_of_two_le {A B M L b c r : ℝ}
    (hA : ∀ x, |deriv smoothTransition x| ≤ A)
    (hB : ∀ x, |deriv (deriv smoothTransition) x| ≤ B)
    (hM : ∀ x, |x * deriv (deriv smoothTransition) x| ≤ M)
    (hL₁ : 1 ≤ L) (hL : 1024 * (A + 2 * B + M) ≤ L) (hb₀ : 0 ≤ b) (hb : b ≤ 8) (hc₀ : 0 ≤ c)
    (hc : c ≤ 128) (hr : 2 ≤ r) :
    deriv (fun x ↦ b * (1 - smoothTransition ((x - 2) / L)) +
      √(64 * x ^ 2 - 64 + c * smoothTransition ((x - 2) / L))) r ≤ 11 := by
  have hr₁ : 1 < r := by linarith
  obtain ⟨hp, -⟩ := smoothTransition.abs_deriv_sub_div_le hA hB hM zero_le_two hL₁
    (ε := 1 / 1024) (by linarith) r
  exact deriv_le_of_cutoff_bounds hb₀ hb hc₀ hc (smoothTransition.nonneg _) hp hr (sqrt_nonneg _)
    (sq_sqrt (by nlinarith [mul_nonneg hc₀ (smoothTransition.nonneg ((r - 2) / L))]))
    (deriv_cutoff_add_sqrt hc₀ hr₁)

/-! ### The leaves `sqrtAddLeaf` -/

/-- The leaf `ℓ` of the family of cutoff leaves over the cylinder of radius `δ` that rises
from the leaf `0` of `sqrtSubLeaf`: with `h r = smoothTransition ((r - 2 δ) / (L δ))`,
`r ↦ (δ / 8 + ℓ) (1 - h r) + √(64 (r² - δ²) + (64 δ² + ℓ²) h r)`. It is the bottom leaf
`√(64 r² - 64 δ²)` raised by `δ / 8 + ℓ` for `r ≤ 2 δ` (when `L, δ ≥ 0`), and, when `L, δ > 0`,
the standard shape `√(64 r² + ℓ²)` for `r ≥ (2 + L) δ`. -/
noncomputable def sqrtAddLeaf (L δ ℓ r : ℝ) : ℝ :=
  (δ / 8 + ℓ) * (1 - smoothTransition ((r - 2 * δ) / (L * δ))) +
    √(64 * (r ^ 2 - δ ^ 2) + (64 * δ ^ 2 + ℓ ^ 2) * smoothTransition ((r - 2 * δ) / (L * δ)))

theorem sqrtAddLeaf_def (L δ ℓ r : ℝ) : sqrtAddLeaf L δ ℓ r =
    (δ / 8 + ℓ) * (1 - smoothTransition ((r - 2 * δ) / (L * δ))) +
      √(64 * (r ^ 2 - δ ^ 2) + (64 * δ ^ 2 + ℓ ^ 2) * smoothTransition ((r - 2 * δ) / (L * δ))) :=
  (rfl)

/-- The leaves for the radius `δ` are those for the radius `1`, rescaled by `δ`. -/
theorem sqrtAddLeaf_eq_mul_sqrtAddLeaf_one (hδ : 0 < δ) (L ℓ : ℝ) :
    sqrtAddLeaf L δ ℓ = fun r ↦ δ * sqrtAddLeaf L 1 (ℓ / δ) (r / δ) := by
  ext r
  have e : (r / δ - 2 * 1) / (L * 1) = (r - 2 * δ) / (L * δ) := by
    rcases eq_or_ne L 0 with rfl | hL
    · simp
    · field_simp
  have hm (X : ℝ) : δ * √X = √(δ ^ 2 * X) := by rw [sqrt_mul (sq_nonneg _), sqrt_sq hδ.le]
  rw [sqrtAddLeaf_def, sqrtAddLeaf_def, e, mul_add, hm]
  congr 1
  · field_simp
  · congr 1
    field_simp

/-- Up to `2 δ`, the leaf `ℓ` is the bottom leaf `√(64 r² - 64 δ²)` raised by `δ / 8 + ℓ`. -/
theorem sqrtAddLeaf_of_le {L ℓ r : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ) (hr : r ≤ 2 * δ) :
    sqrtAddLeaf L δ ℓ r = √(64 * r ^ 2 - 64 * δ ^ 2) + (δ / 8 + ℓ) := by
  rw [sqrtAddLeaf_def, smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))]
  ring_nf

/-- From `(2 + L) δ` on, the leaf `ℓ` is the standard shape `√(64 r² + ℓ²)`. -/
theorem sqrtAddLeaf_of_ge {L ℓ r : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hr : (2 + L) * δ ≤ r) :
    sqrtAddLeaf L δ ℓ r = √(64 * r ^ 2 + ℓ ^ 2) := by
  rw [sqrtAddLeaf_def,
    smoothTransition.one_of_one_le ((one_le_div (by positivity)).2 (by linarith))]
  ring_nf

/-- The leaf `m` for `δ = 1`, with the cutoff `smoothTransition ((x - 2) / L)` written out. -/
private theorem sqrtAddLeaf_one_eq (L m : ℝ) : sqrtAddLeaf L 1 m = fun x ↦
    (1 / 8 + m) * (1 - smoothTransition ((x - 2) / L)) +
      √(64 * x ^ 2 - 64 + (64 + m ^ 2) * smoothTransition ((x - 2) / L)) := by
  ext x
  simp only [sqrtAddLeaf_def, one_pow, mul_one]
  ring_nf

/-- The leaves for `δ = 1` are `i`-convex shapes at every `r > 1`, for `m ∈ [0, 15 / 2]`, once
`L ≥ 1` is large compared with bounds of `smoothTransition'`, `smoothTransition''` and
`x smoothTransition'' x`. -/
private theorem isConvexShapeAt_sqrtAddLeaf_one {A B M L m r : ℝ}
    (hA : ∀ x, |deriv smoothTransition x| ≤ A)
    (hB : ∀ x, |deriv (deriv smoothTransition) x| ≤ B)
    (hM : ∀ x, |x * deriv (deriv smoothTransition) x| ≤ M)
    (hL₁ : 1 ≤ L) (hL : 1024 * (A + 2 * B + M) ≤ L) (hm : m ∈ Icc 0 (15 / 2)) (hr : 1 < r) :
    IsConvexShapeAt (sqrtAddLeaf L 1 m) r := by
  obtain ⟨hm₀, hm₁⟩ := hm
  rcases lt_or_ge r 2 with h | h
  · have hb : 0 ≤ 1 / 8 + m := by linarith
    refine ((isConvexShapeAt_sqrt_sub (a := 64) (c := 64 * 1 ^ 2) (by norm_num)
      (by linarith) (by nlinarith)).add_const hb).congr_of_eventuallyEq ?_
    filter_upwards [gt_mem_nhds h] with x hx
    exact sqrtAddLeaf_of_le (by linarith) zero_le_one (by linarith)
  · rw [sqrtAddLeaf_one_eq]
    exact isConvexShapeAt_cutoff_add_sqrt_of_two_le hA hB hM hL₁ hL (by linarith) (by linarith)
      (by positivity) (by nlinarith) h

/-- The leaves `sqrtAddLeaf L δ ℓ`, for `δ > 0` and `ℓ ∈ [0, 15 δ / 2]`, are `i`-convex shapes at
every `r > δ`, once `L ≥ 1` is large compared with bounds `A` of `smoothTransition'`, `B` of
`smoothTransition''` and `M` of `x smoothTransition'' x`. -/
theorem isConvexShapeAt_sqrtAddLeaf {A B M L ℓ r : ℝ}
    (hA : ∀ x, |deriv smoothTransition x| ≤ A)
    (hB : ∀ x, |deriv (deriv smoothTransition) x| ≤ B)
    (hM : ∀ x, |x * deriv (deriv smoothTransition) x| ≤ M)
    (hL₁ : 1 ≤ L) (hL : 1024 * (A + 2 * B + M) ≤ L) (hδ : 0 < δ) (hℓ : ℓ ∈ Icc 0 (15 * δ / 2))
    (hr : δ < r) : IsConvexShapeAt (sqrtAddLeaf L δ ℓ) r := by
  have hm : ℓ / δ ∈ Icc 0 (15 / 2) :=
    ⟨div_nonneg hℓ.1 hδ.le, (div_le_iff₀ hδ).2 (by linarith [hℓ.2])⟩
  have h := (isConvexShapeAt_sqrtAddLeaf_one hA hB hM hL₁ hL hm
    ((one_lt_div hδ).2 hr)).rescale hδ
  rwa [mul_div_cancel₀ r hδ.ne', ← sqrtAddLeaf_eq_mul_sqrtAddLeaf_one hδ] at h

/-- **The leaves `sqrtAddLeaf` are `i`-convex shapes.** There is `L₀ ≥ 1` such that for every
`L ≥ L₀`, `δ > 0` and `ℓ ∈ [0, 15 δ / 2]`, the leaf `sqrtAddLeaf L δ ℓ` is an `i`-convex shape at
every `r > δ`. -/
theorem exists_isConvexShapeAt_sqrtAddLeaf :
    ∃ L₀, 1 ≤ L₀ ∧ ∀ L, L₀ ≤ L → ∀ δ, 0 < δ → ∀ ℓ ∈ Icc 0 (15 * δ / 2), ∀ r, δ < r →
      IsConvexShapeAt (sqrtAddLeaf L δ ℓ) r := by
  obtain ⟨A, hA⟩ := smoothTransition.exists_forall_norm_deriv_le
  obtain ⟨B, hB⟩ := smoothTransition.exists_forall_norm_deriv_deriv_le
  obtain ⟨M, hM⟩ := smoothTransition.exists_forall_norm_mul_deriv_deriv_le
  simp only [Real.norm_eq_abs] at hA hB hM
  exact ⟨max 1 (1024 * (A + 2 * B + M)), le_max_left _ _, fun L hL δ hδ ℓ hℓ r hr ↦
    isConvexShapeAt_sqrtAddLeaf hA hB hM ((le_max_left _ _).trans hL)
      ((le_max_right _ _).trans hL) hδ hℓ hr⟩

/-- The slope of the leaf `sqrtAddLeaf L δ ℓ`, for `δ > 0` and `ℓ ∈ [0, 15 δ / 2]`, is at most
`11` from `2 δ` on, once `L ≥ 1` is large compared with bounds `A` of `smoothTransition'`, `B`
of `smoothTransition''` and `M` of `x smoothTransition'' x`. -/
theorem deriv_sqrtAddLeaf_le {A B M L ℓ r : ℝ}
    (hA : ∀ x, |deriv smoothTransition x| ≤ A)
    (hB : ∀ x, |deriv (deriv smoothTransition) x| ≤ B)
    (hM : ∀ x, |x * deriv (deriv smoothTransition) x| ≤ M)
    (hL₁ : 1 ≤ L) (hL : 1024 * (A + 2 * B + M) ≤ L) (hδ : 0 < δ) (hℓ : ℓ ∈ Icc 0 (15 * δ / 2))
    (hr : 2 * δ ≤ r) : deriv (sqrtAddLeaf L δ ℓ) r ≤ 11 := by
  have hm₀ : 0 ≤ ℓ / δ := div_nonneg hℓ.1 hδ.le
  have hm₁ : ℓ / δ ≤ 15 / 2 := (div_le_iff₀ hδ).2 (by linarith [hℓ.2])
  have h₁ : deriv (fun r ↦ δ * sqrtAddLeaf L 1 (ℓ / δ) (r / δ)) r =
      deriv (sqrtAddLeaf L 1 (ℓ / δ)) (r / δ) := by
    have h := congrFun (iteratedDeriv_comp_div_const 1 δ (sqrtAddLeaf L 1 (ℓ / δ))) r
    simp only [iteratedDeriv_one, pow_one, smul_eq_mul] at h
    rw [deriv_const_mul_field, h]
    field_simp
  rw [sqrtAddLeaf_eq_mul_sqrtAddLeaf_one hδ, h₁, sqrtAddLeaf_one_eq]
  exact deriv_cutoff_add_sqrt_le_of_two_le hA hB hM hL₁ hL (by linarith) (by linarith)
    (by positivity) (by nlinarith) ((le_div_iff₀ hδ).2 (by linarith))

/-- The leaf `ℓ ≥ 0` is at least `8 √(r² - δ²)`, for `0 ≤ δ`. -/
theorem eight_mul_sqrt_le_sqrtAddLeaf (L : ℝ) (hδ : 0 ≤ δ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (r : ℝ) :
    8 * √(r ^ 2 - δ ^ 2) ≤ sqrtAddLeaf L δ ℓ r := by
  set H := smoothTransition ((r - 2 * δ) / (L * δ))
  have hH₀ : 0 ≤ H := smoothTransition.nonneg _
  have hH₁ : H ≤ 1 := smoothTransition.le_one _
  have h8 : 8 * √(r ^ 2 - δ ^ 2) = √(64 * (r ^ 2 - δ ^ 2)) := by
    rw [sqrt_mul (by norm_num), show (64 : ℝ) = 8 ^ 2 by norm_num, sqrt_sq (by norm_num)]
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
  have e : Function.uncurry (sqrtAddLeaf L δ) = fun p : ℝ × ℝ ↦
      (δ / 8 + p.1) * (1 - smoothTransition ((p.2 - 2 * δ) / (L * δ))) +
        √(64 * (p.2 ^ 2 - δ ^ 2) +
          (64 * δ ^ 2 + p.1 ^ 2) * smoothTransition ((p.2 - 2 * δ) / (L * δ))) := by
    ext ⟨ℓ, r⟩
    rw [Function.uncurry_apply_pair, sqrtAddLeaf_def]
  have hH : ContDiff ℝ ∞ fun p : ℝ × ℝ ↦ smoothTransition ((p.2 - 2 * δ) / (L * δ)) :=
    smoothTransition.contDiff.comp ((contDiff_snd.sub contDiff_const).div_const _)
  rintro ⟨ℓ, r⟩ ⟨-, hr⟩
  rw [mem_Ioi] at hr
  have hrδ : δ ^ 2 < r ^ 2 := by gcongr
  have hrad : 0 < 64 * (r ^ 2 - δ ^ 2) +
      (64 * δ ^ 2 + ℓ ^ 2) * smoothTransition ((r - 2 * δ) / (L * δ)) := by
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 64 * δ ^ 2 + ℓ ^ 2)
      (smoothTransition.nonneg ((r - 2 * δ) / (L * δ)))]
  rw [e]
  exact ((contDiff_const.add contDiff_fst).mul (contDiff_const.sub hH)).contDiffAt.add
    (((contDiff_const.mul ((contDiff_snd.pow 2).sub contDiff_const)).add
      ((contDiff_const.add (contDiff_fst.pow 2)).mul hH)).contDiffAt.sqrt
      hrad.ne') |>.contDiffWithinAt

/-- The slope of every leaf tends to `+∞` at `δ`, where the leaves meet the cylinder. -/
theorem tendsto_deriv_sqrtAddLeaf {L : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ) (ℓ : ℝ) :
    Tendsto (deriv (sqrtAddLeaf L δ ℓ)) (𝓝[>] δ) atTop := by
  refine (tendsto_deriv_sqrt_sub (a := 64) (by norm_num) hδ).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (by linarith : δ < 2 * δ)] with r hr
  have he : sqrtAddLeaf L δ ℓ =ᶠ[𝓝 r]
      fun x ↦ √(64 * x ^ 2 - 64 * δ ^ 2) + (δ / 8 + ℓ) := by
    filter_upwards [gt_mem_nhds hr.2] with x hx using sqrtAddLeaf_of_le hL hδ.le hx.le
  rw [he.deriv_eq, deriv_add_const]

/-- For `0 ≤ δ`, at each `r > δ`, the leaves `ℓ ≥ 0` are strictly increasing in `ℓ`: both
terms of `sqrtAddLeaf` are nondecreasing in `ℓ ≥ 0`, the first strictly where the cutoff is
below `1` and the second where it is positive. -/
theorem strictMonoOn_sqrtAddLeaf (L : ℝ) (hδ : 0 ≤ δ) {r : ℝ} (hr : δ < r) :
    StrictMonoOn (fun ℓ ↦ sqrtAddLeaf L δ ℓ r) (Ici 0) := by
  intro ℓ₁ hℓ₁ ℓ₂ hℓ₂ h
  rw [mem_Ici] at hℓ₁ hℓ₂
  simp only [sqrtAddLeaf_def]
  set H := smoothTransition ((r - 2 * δ) / (L * δ))
  have hH₀ : 0 ≤ H := smoothTransition.nonneg _
  have hH₁ : H ≤ 1 := smoothTransition.le_one _
  have hrδ : δ ^ 2 < r ^ 2 := by gcongr
  have hsq : ℓ₁ ^ 2 < ℓ₂ ^ 2 := by nlinarith
  rcases hH₁.lt_or_eq with hH | hH
  · exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_right (by linarith) (by linarith))
      (sqrt_le_sqrt (by nlinarith))
  · simp only [hH, sub_self, mul_zero, zero_add, mul_one]
    exact sqrt_lt_sqrt (by nlinarith) (by linarith)

end SymplecticGeometry

end
