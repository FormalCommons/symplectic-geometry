/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.SpecialShape

import Mathlib.Analysis.Complex.ExponentialBounds
import SymplecticGeometry.Analysis.Calculus.IteratedDeriv.Prod
import SymplecticGeometry.Analysis.SpecialFunctions.SmoothTransition.Deriv
import TauCeti.Analysis.SpecialFunctions.SmoothTransition

/-!
# Families of special `i`-convex shapes

The families of `i`-convex shapes (`SymplecticGeometry.IsConvexShapeAt`) of Cieliebak and
Eliashberg's §4.6, which sweep out the neighbourhood of the corner of the surrounding shape.

* `SymplecticGeometry.isConvexShapeAt_struweShape_two`: for `0 < δ` and `4 ≤ d`, Struwe's
  shape with value `2 d δ` at `2 δ` is an `i`-convex shape at every point of `(δ, 2 δ]`. Since
  `exp (4 / 9) ≤ 2`, `SymplecticGeometry.sub_le_struweShape` bounds its value at `δ` below by
  `(2 d - 3) δ ≥ 5 δ`, while `log 2 < 1`, so that `2 δ √(log 2)` and `4 δ √(log 2)³` are at
  most `4 δ`, and `SymplecticGeometry.isConvexShapeAt_struweShape_of_le_of_mem_Ioc` applies.

Its slope at `2 δ` is `1 / √(log 2)` (`SymplecticGeometry.deriv_struweShape_mul`), and its slope
tends to `+∞` at `δ` (`SymplecticGeometry.tendsto_deriv_struweShape`).

* `SymplecticGeometry.exists_convexShapeFamily_sqrt`: for `1 < a` and `0 < γ`, a family `χ ℓ`,
  `ℓ ≥ 0`, of smooth `i`-convex shapes on `(0, ∞)` that starts at the cone `χ 0 r = √a r`, is
  linear, `ℓ + d r`, for `r ≤ ℓ β`, and is the standard shape `√(ℓ² + a r²)` for `r ≥ ℓ γ`,
  smooth in `(ℓ, r)` and strictly increasing in `ℓ`. For `ℓ > 0` the
  member is the shape `ψ` of `SymplecticGeometry.exists_isConvexShapeAt_eq_linear_eq_sqrt`
  rescaled by `IsConvexShapeAt.rescale` to `r ↦ ℓ ψ (r / ℓ)`. Near `ℓ = 0` and `r > 0` every
  member is standard, which is smooth in `(ℓ, r)`, so the `r`-derivatives of every order are
  jointly continuous by `ContDiffAt.continuousAt_iteratedDeriv_prod_right`. The `ℓ`-derivative
  of `ℓ ψ (r / ℓ)` is `ψ s - s ψ' s` at `s = r / ℓ`, which is positive since every tangent of
  `ψ` at `s ≥ 0` meets the vertical axis above `0`.

* `SymplecticGeometry.sqrtSubLeaf` and `SymplecticGeometry.exists_isConvexShapeAt_sqrtSubLeaf`:
  the leaves `ℓ ∈ [-8 δ, 0]` of the family over the cylinder of radius `δ`. They do not come from
  bending linear shapes, as in Cieliebak and Eliashberg's Lemma 4.25, but have a closed form:
  with the cutoff `h r = smoothTransition ((r - 2 δ) / (L δ))`, the leaf `ℓ` is
  `(ℓ + 8 δ) / 64 (1 - h r) + √(64 (r² - δ²) + (64 δ² - ℓ²) h r)`. For `L` large enough, every
  leaf is an `i`-convex shape at every `r > δ`. The leaves for `δ` are those for `δ = 1` rescaled
  (`SymplecticGeometry.sqrtSubLeaf_eq_mul_sqrtSubLeaf_one`, `IsConvexShapeAt.rescale`). For `δ = 1`
  and `r < 2` a leaf is, near `r`, the shape `√(64 r² - 64)` of
  `SymplecticGeometry.isConvexShapeAt_sqrt_sub` plus a constant `≥ 0`
  (`SymplecticGeometry.sqrtSubLeaf_of_le`). For `r ≥ 2`, if `L` is large compared with bounds on
  `smoothTransition'`, `smoothTransition''` (Tau Ceti's
  `Real.smoothTransition.exists_forall_norm_deriv_le` and
  `Real.smoothTransition.exists_forall_norm_deriv_deriv_le`) and on `x smoothTransition'' x`
  (`Real.smoothTransition.exists_forall_norm_mul_deriv_deriv_le`), then `|h'| ≤ 1 / 64` and
  `|r h''| ≤ 1 / 64`. Then the square root `S` of the radicand lies in `[6 r, 8 r]`, the slope is at
  least `7`, and the second derivative is at least `-21 / r`, so both inequalities of
  `SymplecticGeometry.isConvexShapeAt_iff` hold with a wide margin.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  §4.5: Lemma 4.19; §4.6: Lemma 4.23 and Lemma 4.26.
-/

public section

namespace SymplecticGeometry

open Real Set Filter Topology
open scoped ContDiff

variable {δ : ℝ}

/-- **Struwe's shape on `(δ, 2 δ]`** (Cieliebak–Eliashberg, Lemma 4.23). For `0 < δ` and
`4 ≤ d`, Struwe's shape with value `2 d δ` at `2 δ` is an `i`-convex shape at every point of
`(δ, 2 δ]`. -/
theorem isConvexShapeAt_struweShape_two {d r : ℝ} (hδ : 0 < δ) (hd : 4 ≤ d)
    (hr : r ∈ Ioc δ (2 * δ)) : IsConvexShapeAt (struweShape δ 2 (2 * d * δ)) r := by
  have hexp : exp (4 / 3 ^ 2) ≤ 2 := by
    rw [← le_log_iff_exp_le two_pos]
    linarith [log_two_gt_d9]
  have h := sub_le_struweShape (by norm_num) hδ hexp (2 * d * δ)
  have e : 2 * δ / δ = 2 := mul_div_cancel_right₀ _ hδ.ne'
  have ht₀ : 0 ≤ √(log 2) := sqrt_nonneg _
  have ht : √(log 2) ≤ 1 := sqrt_le_one.2 (by linarith [log_two_lt_d9])
  have ht₃ : √(log 2) ^ 3 ≤ 1 := pow_le_one₀ ht₀ ht
  refine isConvexShapeAt_struweShape_of_le_of_mem_Ioc (m := (2 * d - 3) * δ) hδ one_le_two
    (by linarith) ?_ ?_ hr <;> rw [e] <;> nlinarith

/-- **The square-root family** (Cieliebak–Eliashberg, Lemma 4.26). For `1 < a` and `0 < γ` there
are `d ∈ (0, 1)`, `β ∈ (0, γ)` and a family `χ ℓ` of smooth functions such that, for every
`ℓ ≥ 0`:
* `χ ℓ` is an `i`-convex shape at every `r > 0`;
* `χ ℓ r` is the standard shape `√(ℓ² + a r²)` for `r ≥ ℓ γ`, so for `r ≥ γ` when `ℓ ≤ 1`;
* for `ℓ > 0`, `χ ℓ r = ℓ + d r` for `r ≤ ℓ β`;
* `χ 0` is the cone `r ↦ √a r`;

and, on `[0, ∞) × (0, ∞)`, `(ℓ, r) ↦ χ ℓ r` is smooth at every point, so that each
`iteratedDeriv k (χ ℓ) r` is jointly continuous in `(ℓ, r)` there, and is strictly increasing
in `ℓ` for each `r > 0`: the members do not cross. -/
theorem exists_convexShapeFamily_sqrt {a γ : ℝ} (ha : 1 < a) (hγ : 0 < γ) :
    ∃ d ∈ Ioo 0 1, ∃ β ∈ Ioo 0 γ, ∃ χ : ℝ → ℝ → ℝ, (∀ ℓ, ContDiff ℝ ∞ (χ ℓ)) ∧
      (∀ ℓ, 0 ≤ ℓ → ∀ r, 0 < r → IsConvexShapeAt (χ ℓ) r) ∧
      (∀ q ∈ Ici 0 ×ˢ Ioi 0, ContDiffAt ℝ ∞ (Function.uncurry χ) q) ∧
      (∀ k : ℕ, ContinuousOn (fun q : ℝ × ℝ ↦ iteratedDeriv k (χ q.1) q.2) (Ici 0 ×ˢ Ioi 0)) ∧
      (∀ ℓ₁ ℓ₂, 0 ≤ ℓ₁ → ℓ₁ < ℓ₂ → ∀ r, 0 < r → χ ℓ₁ r < χ ℓ₂ r) ∧
      (∀ ℓ, 0 ≤ ℓ → ∀ r, ℓ * γ ≤ r → χ ℓ r = √(ℓ ^ 2 + a * r ^ 2)) ∧
      (∀ ℓ, 0 < ℓ → ∀ r ≤ ℓ * β, χ ℓ r = ℓ + d * r) ∧ ∀ r, χ 0 r = √a * r := by
  obtain ⟨d, hd, β, hβ, ψ, hψs, hψc, hψS, hψL, hψI⟩ :=
    exists_isConvexShapeAt_eq_linear_eq_sqrt ha hγ
  -- The member `ℓ ≠ 0` is `ψ` rescaled by `|ℓ|`, so that the family is smooth across `ℓ = 0`.
  set χ : ℝ → ℝ → ℝ := fun ℓ r ↦ if ℓ = 0 then √a * r else |ℓ| * ψ (r / |ℓ|) with hχ
  have hχ₀ (r : ℝ) : χ 0 r = √a * r := by simp [hχ]
  have hχne' {ℓ : ℝ} (hℓ : ℓ ≠ 0) (r : ℝ) : χ ℓ r = |ℓ| * ψ (r / |ℓ|) := by
    simp [hχ, hℓ]
  have hχne {ℓ : ℝ} (hℓ : ℓ ≠ 0) : χ ℓ = fun r ↦ |ℓ| * ψ (r / |ℓ|) := funext (hχne' hℓ)
  -- Near a point with `ℓ > 0`, the family is `ℓ ψ (r / ℓ)`.
  have hχpos {ℓ : ℝ} (hℓ : 0 < ℓ) (r : ℝ) :
      (fun q : ℝ × ℝ ↦ χ q.1 q.2) =ᶠ[𝓝 (ℓ, r)] fun q ↦ q.1 * ψ (q.2 / q.1) := by
    filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hℓ] with q hq
    rw [hχne' hq.ne', abs_of_pos hq]
  -- The standard part, for every `ℓ`.
  have hstd (ℓ r : ℝ) (hr : |ℓ| * γ ≤ r) : χ ℓ r = √(ℓ ^ 2 + a * r ^ 2) := by
    rcases eq_or_ne ℓ 0 with rfl | hℓ
    · have hr : 0 ≤ r := by simpa using hr
      rw [hχ₀, zero_pow two_ne_zero, zero_add, sqrt_mul (by linarith), sqrt_sq hr]
    · have hℓ' : 0 < |ℓ| := abs_pos.2 hℓ
      rw [hχne' hℓ, hψS _ ((le_div_iff₀ hℓ').2 (by linarith))]
      nth_rw 1 [← sqrt_sq hℓ'.le]
      rw [← sqrt_mul (sq_nonneg _), div_pow, sq_abs]
      congr 1
      field_simp
  -- `χ` is jointly smooth near each point of `[0, ∞) × (0, ∞)`.
  have hsm : ∀ q ∈ Ici 0 ×ˢ Ioi 0, ContDiffAt ℝ ∞ (Function.uncurry χ) q := by
    rintro ⟨ℓ, r⟩ ⟨hℓ, hr⟩
    rw [mem_Ici] at hℓ
    rw [mem_Ioi] at hr
    rcases hℓ.eq_or_lt with rfl | hℓ
    · -- Near `(0, r)` the family is the standard one.
      have h : ∀ᶠ q : ℝ × ℝ in 𝓝 (0, r), |q.1| * γ < q.2 :=
        ((continuous_abs.comp continuous_fst).mul continuous_const).continuousAt.eventually_lt
          continuous_snd.continuousAt (by simpa using hr)
      refine ContDiffAt.congr_of_eventuallyEq ?_ (h.mono fun q hq ↦ hstd q.1 q.2 hq.le)
      refine ContDiffAt.sqrt (by fun_prop) ?_
      simp only
      positivity
    · exact ContDiffAt.congr_of_eventuallyEq (contDiffAt_fst.mul
        (hψs.contDiffAt.comp _ (contDiffAt_snd.div contDiffAt_fst hℓ.ne'))) (hχpos hℓ r)
  refine ⟨d, hd, β, hβ, χ, fun ℓ ↦ ?_, fun ℓ hℓ r hr ↦ ?_, hsm, fun k q hq ↦ ?_,
    fun ℓ₁ ℓ₂ hℓ₁ hℓ₁₂ r hr ↦ ?_, fun ℓ hℓ r hr ↦ hstd ℓ r (by rwa [abs_of_nonneg hℓ]),
    fun ℓ hℓ r hr ↦ ?_, hχ₀⟩
  · rcases eq_or_ne ℓ 0 with rfl | hℓ
    · rw [show χ 0 = fun r ↦ √a * r from funext hχ₀]
      fun_prop
    · rw [hχne hℓ]
      exact contDiff_const.mul (hψs.comp (contDiff_id.div_const _))
  · rcases hℓ.eq_or_lt with rfl | hℓ
    · refine (isConvexShapeAt_sqrt (ℓ := 0) ha hr).congr_of_eventuallyEq ?_
      filter_upwards [lt_mem_nhds hr] with r hr
      exact hstd 0 r (by simpa using hr.le)
    · have h := (hψc (r / ℓ) (div_pos hr hℓ)).rescale hℓ
      rwa [mul_div_cancel₀ r hℓ.ne', ← abs_of_pos hℓ, ← hχne hℓ.ne'] at h
  · exact ((hsm q hq).continuousAt_iteratedDeriv_prod_right
      (by exact_mod_cast le_top)).continuousWithinAt
  · -- `ℓ ↦ χ ℓ r` is continuous on `[0, ∞)`, with derivative `ψ s - s ψ' s > 0`, `s = r / ℓ`,
    -- at each `ℓ > 0`.
    refine strictMonoOn_of_deriv_pos (f := fun ℓ ↦ χ ℓ r) (convex_Ici 0) (fun ℓ hℓ ↦ ?_)
      (fun ℓ hℓ ↦ ?_)
      (mem_Ici.2 hℓ₁) (mem_Ici.2 (hℓ₁.trans hℓ₁₂.le)) hℓ₁₂
    · exact ((hsm (ℓ, r) ⟨hℓ, hr⟩).continuousAt.comp (f := fun x ↦ (x, r))
        (by fun_prop)).continuousWithinAt
    · rw [interior_Ici, mem_Ioi] at hℓ
      have hs : 0 < r / ℓ := div_pos hr hℓ
      have hdiv := (hasDerivAt_const ℓ r).div (hasDerivAt_id' ℓ) hℓ.ne'
      have h := (hasDerivAt_id' ℓ).fun_mul
        (((hψs.differentiable (by simp)) (r / ℓ)).hasDerivAt.comp ℓ hdiv)
      have he : (fun x ↦ χ x r) =ᶠ[𝓝 ℓ] fun x ↦ x * (ψ ∘ fun x ↦ r / x) x := by
        filter_upwards [lt_mem_nhds hℓ] with x hx
        rw [hχne' hx.ne', abs_of_pos hx, Function.comp_apply]
      rw [(h.congr_of_eventuallyEq he).deriv]
      have hI := hψI (r / ℓ) hs.le
      have e : ℓ * (deriv ψ (r / ℓ) * ((0 * ℓ - r * 1) / ℓ ^ 2)) =
          -(r / ℓ * deriv ψ (r / ℓ)) := by
        field_simp
        ring
      rw [one_mul, Function.comp_apply, e]
      linarith
  · have hr' : r / ℓ ≤ β := (div_le_iff₀ hℓ).2 (by linarith)
    rw [hχne' hℓ.ne', abs_of_pos hℓ, hψL _ hr']
    field_simp

/-! ### The explicit leaves below the cone -/

/-- The leaf `ℓ` of the explicit family of `i`-convex shapes over the cylinder of radius `δ`,
with a cutoff of width `L δ` starting at `2 δ`: with `h r = smoothTransition ((r - 2 δ) / (L δ))`,
`r ↦ (ℓ + 8 δ) / 64 (1 - h r) + √(64 (r² - δ²) + (64 δ² - ℓ²) h r)`. It is the bottom leaf
`√(64 r² - 64 δ²)` raised by `(ℓ + 8 δ) / 64` for `r ≤ 2 δ` (when `L, δ ≥ 0`), and, when
`L, δ > 0`, the standard shape `√(64 r² - ℓ²)` for `r ≥ (2 + L) δ`. -/
noncomputable def sqrtSubLeaf (L δ ℓ r : ℝ) : ℝ :=
  (ℓ + 8 * δ) / 64 * (1 - smoothTransition ((r - 2 * δ) / (L * δ))) +
    √(64 * (r ^ 2 - δ ^ 2) + (64 * δ ^ 2 - ℓ ^ 2) * smoothTransition ((r - 2 * δ) / (L * δ)))

theorem sqrtSubLeaf_def (L δ ℓ r : ℝ) : sqrtSubLeaf L δ ℓ r =
    (ℓ + 8 * δ) / 64 * (1 - smoothTransition ((r - 2 * δ) / (L * δ))) +
      √(64 * (r ^ 2 - δ ^ 2) + (64 * δ ^ 2 - ℓ ^ 2) * smoothTransition ((r - 2 * δ) / (L * δ))) :=
  (rfl)

/-- The leaves for the radius `δ` are those for the radius `1`, rescaled by `δ`. -/
theorem sqrtSubLeaf_eq_mul_sqrtSubLeaf_one (hδ : 0 < δ) (L ℓ : ℝ) :
    sqrtSubLeaf L δ ℓ = fun r ↦ δ * sqrtSubLeaf L 1 (ℓ / δ) (r / δ) := by
  ext r
  have e : (r / δ - 2 * 1) / (L * 1) = (r - 2 * δ) / (L * δ) := by
    rcases eq_or_ne L 0 with rfl | hL
    · simp
    · field_simp
  have hm (X : ℝ) : δ * √X = √(δ ^ 2 * X) := by rw [sqrt_mul (sq_nonneg _), sqrt_sq hδ.le]
  rw [sqrtSubLeaf_def, sqrtSubLeaf_def, e, mul_add, hm]
  congr 1
  · field_simp
  · congr 1
    field_simp

/-- Up to `2 δ`, the leaf `ℓ` is the bottom leaf `√(64 r² - 64 δ²)` raised by `(ℓ + 8 δ) / 64`. -/
theorem sqrtSubLeaf_of_le {L ℓ r : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ) (hr : r ≤ 2 * δ) :
    sqrtSubLeaf L δ ℓ r = √(64 * r ^ 2 - 64 * δ ^ 2) + (ℓ + 8 * δ) / 64 := by
  rw [sqrtSubLeaf_def, smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))]
  ring_nf

/-- The estimate behind `isConvexShapeAt_sqrtSubLeaf_one_of_two_le`, for `δ = 1` and `2 ≤ r`,
in terms of the cutoff `H`, its derivatives `p` and `q` at `r` and the square root `S` of the
radicand at `r`. -/
private theorem isConvexShapeAt_of_bounds {χ : ℝ → ℝ} {b c r H p q S : ℝ} (hb₀ : 0 ≤ b)
    (hb : b ≤ 1 / 8) (hc₀ : 0 ≤ c) (hc : c ≤ 64) (hH₀ : 0 ≤ H) (hH : H ≤ 1) (hp : |p| ≤ 1 / 64)
    (hq : |r * q| ≤ 1 / 64) (hr : 2 ≤ r) (hS₀ : 0 ≤ S) (hS : S ^ 2 = 64 * r ^ 2 - 64 + c * H)
    (h₀ : χ r = b * (1 - H) + S) (h₁ : deriv χ r = -b * p + (128 * r + c * p) / (2 * S))
    (h₂ : iteratedDeriv 2 χ r =
      -b * q + (128 + c * q) / (2 * S) - (128 * r + c * p) ^ 2 / (4 * S ^ 3)) :
    IsConvexShapeAt χ r := by
  have hr₀ : 0 < r := by linarith
  have hq₂ : r * |q| ≤ 1 / 64 := by rwa [abs_mul, abs_of_pos hr₀] at hq
  have : c * H ≤ 64 := by nlinarith
  have hS6 : 6 * r ≤ S := by nlinarith
  have hS8 : S ≤ 8 * r := by nlinarith
  have hSpos : 0 < S := by linarith
  have hcp : |c * p| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hc₀]; nlinarith [abs_nonneg p]
  have hcp' := abs_le.1 hcp
  have hbp : |b * p| ≤ 1 / 512 := by
    rw [abs_mul, abs_of_nonneg hb₀]; nlinarith [abs_nonneg p]
  have hbp' := abs_le.1 hbp
  have hχ : S ≤ χ r := by rw [h₀]; nlinarith
  have hinv : 1 / χ r ≤ 1 / 6 * (1 / r) := by
    rw [one_div_mul_one_div]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  -- The slope is at least `7`.
  have hF₁ : 0 < 128 * r + c * p := by linarith
  have hd : 7 ≤ deriv χ r := by
    have : (128 * r + c * p) / (16 * r) ≤ (128 * r + c * p) / (2 * S) :=
      div_le_div_of_nonneg_left hF₁.le (by positivity) (by linarith)
    have : 7 + 1 / 512 ≤ (128 * r + c * p) / (16 * r) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    rw [h₁]; linarith
  -- The negative terms of the second derivative are at most `21 / r`.
  have hq' : |b * q| ≤ 1 / 512 * (1 / r) := by
    rw [abs_mul, abs_of_nonneg hb₀, mul_one_div, le_div_iff₀ hr₀]
    nlinarith [abs_nonneg q]
  have hT : (128 * r + c * p) ^ 2 / (4 * S ^ 3) ≤ 20 * (1 / r) := by
    rw [div_le_iff₀ (by positivity)]
    have : (128 * r + c * p) ^ 2 ≤ (130 * r) ^ 2 := by nlinarith
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

/-- The leaves for `δ = 1` are `i`-convex shapes at `r ≥ 2`, where the cutoff acts, once `L` is
large compared with the bounds `A` of `smoothTransition'`, `B` of `smoothTransition''` and `M`
of `x smoothTransition'' x`. -/
private theorem isConvexShapeAt_sqrtSubLeaf_one_of_two_le {A B M L m r : ℝ}
    (hA : ∀ x, |deriv smoothTransition x| ≤ A)
    (hB : ∀ x, |deriv (deriv smoothTransition) x| ≤ B)
    (hM : ∀ x, |x * deriv (deriv smoothTransition) x| ≤ M)
    (hL₁ : 1 ≤ L) (hL : 64 * (A + 2 * B + M) ≤ L) (hm : m ∈ Icc (-8) 0) (hr : 2 ≤ r) :
    IsConvexShapeAt (sqrtSubLeaf L 1 m) r := by
  obtain ⟨hm₀, hm₁⟩ := hm
  have hL₀ : 0 < L := by linarith
  have hA₀ : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  have hB₀ : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hM₀ : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set s₁ := deriv smoothTransition
  set s₂ := deriv s₁ with hs₂
  set b := (m + 8) / 64 with hb
  set c := 64 - m ^ 2 with hc
  set H : ℝ → ℝ := fun x ↦ smoothTransition ((x - 2) / L) with hH
  set H₁ : ℝ → ℝ := fun x ↦ s₁ ((x - 2) / L) / L with hH₁
  set H₂ : ℝ → ℝ := fun x ↦ s₂ ((x - 2) / L) / L ^ 2 with hH₂
  set F : ℝ → ℝ := fun x ↦ 64 * x ^ 2 - 64 + c * H x with hF
  have e : sqrtSubLeaf L 1 m = fun x ↦ b * (1 - H x) + √(F x) := by
    ext x
    simp only [sqrtSubLeaf_def, hb, hc, hH, hF, one_pow, mul_one]
    ring_nf
  have hHd (x : ℝ) : HasDerivAt H (H₁ x) x := by
    have := ((smoothTransition.contDiff (n := 1)).differentiable (by simp) _).hasDerivAt.comp x
      (((hasDerivAt_id' x).sub_const 2).div_const L)
    exact this.congr_deriv (by simp only [hH₁]; ring)
  have hH₁d (x : ℝ) : HasDerivAt H₁ (H₂ x) x := by
    have := ((smoothTransition.differentiable_deriv _).hasDerivAt.comp x
      (((hasDerivAt_id' x).sub_const 2).div_const L)).div_const L
    exact this.congr_deriv (by simp only [hH₂, hs₂]; ring)
  have hFd (x : ℝ) : HasDerivAt F (128 * x + c * H₁ x) x :=
    ((((hasDerivAt_pow 2 x).const_mul 64).sub_const 64).add ((hHd x).const_mul c)).congr_deriv
      (by ring)
  have hHnn (x : ℝ) : 0 ≤ H x := smoothTransition.nonneg _
  have hc₀ : 0 ≤ c := by nlinarith
  have hFpos {x : ℝ} (hx : 1 < x) : 0 < F x := by
    have := mul_nonneg hc₀ (hHnn x)
    simp only [hF]
    nlinarith
  set χ₁ : ℝ → ℝ := fun x ↦ -b * H₁ x + (128 * x + c * H₁ x) / (2 * √(F x)) with hχ₁
  have hχd {x : ℝ} (hx : 1 < x) : HasDerivAt (fun x ↦ b * (1 - H x) + √(F x)) (χ₁ x) x :=
    ((((hHd x).const_sub 1).const_mul b).add ((hFd x).sqrt (hFpos hx).ne')).congr_deriv
      (by simp only [hχ₁]; ring)
  have hF₁d : HasDerivAt (fun x ↦ 128 * x + c * H₁ x) (128 + c * H₂ r) r :=
    (((hasDerivAt_id' r).const_mul 128).add ((hH₁d r).const_mul c)).congr_deriv (by ring)
  have hr₁ : 1 < r := by linarith
  have hS := sqrt_pos.2 (hFpos hr₁)
  have hχ₁d := ((hH₁d r).const_mul (-b)).add
    (hF₁d.div (((hFd r).sqrt (hFpos hr₁).ne').const_mul 2) (by positivity))
  have hχ₁d' : HasDerivAt χ₁ _ r := hχ₁d
  have hev : deriv (fun x ↦ b * (1 - H x) + √(F x)) =ᶠ[𝓝 r] χ₁ := by
    filter_upwards [lt_mem_nhds hr₁] with x hx using (hχd hx).deriv
  -- The bounds on `H'` and `H''` at `r`.
  set y := (r - 2) / L with hy
  have hry : r = 2 + L * y := by rw [hy]; field_simp; ring
  have hp : |H₁ r| ≤ 1 / 64 := by
    simp only [hH₁]
    rw [← hy, abs_div, abs_of_pos hL₀, div_le_iff₀ hL₀]
    nlinarith [hA y]
  have hq : |r * H₂ r| ≤ 1 / 64 := by
    have e' : r * H₂ r = (2 * s₂ y + L * (y * s₂ y)) / L ^ 2 := by
      simp only [hH₂]
      rw [← hy]
      nth_rw 1 [hry]
      field_simp
    rw [e', abs_div, abs_of_pos (pow_pos hL₀ 2), div_le_iff₀ (pow_pos hL₀ 2)]
    have h1 := abs_add_le (2 * s₂ y) (L * (y * s₂ y))
    rw [abs_mul, abs_mul, abs_of_pos hL₀, abs_two] at h1
    have h2 := hB y
    have h3 := hM y
    refine h1.trans ?_
    nlinarith
  refine isConvexShapeAt_of_bounds (b := b) (c := c) (H := H r) (p := H₁ r) (q := H₂ r)
    (S := √(F r))
    (by rw [hb]; linarith) (by rw [hb]; linarith) hc₀ (by nlinarith) (hHnn r)
    (smoothTransition.le_one _) hp hq hr (sqrt_nonneg _) (sq_sqrt (hFpos hr₁).le)
    (by rw [e]) (by rw [e, (hχd hr₁).deriv]) ?_
  rw [e, iteratedDeriv_succ, iteratedDeriv_one, hev.deriv_eq, hχ₁d'.deriv]
  field_simp
  ring

/-- **The explicit leaves below the cone are `i`-convex shapes.** There is `L₀ ≥ 1` such that for
every `L ≥ L₀`, `δ > 0` and `ℓ ∈ [-8 δ, 0]`, the leaf `sqrtSubLeaf L δ ℓ` is an `i`-convex shape
at every `r > δ`. -/
theorem exists_isConvexShapeAt_sqrtSubLeaf :
    ∃ L₀, 1 ≤ L₀ ∧ ∀ L, L₀ ≤ L → ∀ δ, 0 < δ → ∀ ℓ ∈ Icc (-8 * δ) 0, ∀ r, δ < r →
      IsConvexShapeAt (sqrtSubLeaf L δ ℓ) r := by
  obtain ⟨A, hA⟩ := smoothTransition.exists_forall_norm_deriv_le
  obtain ⟨B, hB⟩ := smoothTransition.exists_forall_norm_deriv_deriv_le
  obtain ⟨M, hM⟩ := smoothTransition.exists_forall_norm_mul_deriv_deriv_le
  simp only [Real.norm_eq_abs] at hA hB hM
  refine ⟨max 1 (64 * (A + 2 * B + M)), le_max_left _ _, fun L hL δ hδ ℓ hℓ r hr ↦ ?_⟩
  have hL₁ : 1 ≤ L := (le_max_left _ _).trans hL
  have hm : ℓ / δ ∈ Icc (-8) 0 :=
    ⟨(le_div_iff₀ hδ).2 (by linarith [hℓ.1]), div_nonpos_of_nonpos_of_nonneg hℓ.2 hδ.le⟩
  have hr' : 1 < r / δ := (one_lt_div hδ).2 hr
  -- The case `δ = 1`, rescaled by `δ`.
  have h₁ : IsConvexShapeAt (sqrtSubLeaf L 1 (ℓ / δ)) (r / δ) := by
    rcases lt_or_ge (r / δ) 2 with h | h
    · have hb : 0 ≤ (ℓ / δ + 8 * 1) / 64 := by linarith [hm.1]
      refine ((isConvexShapeAt_sqrt_sub (a := 64) (c := 64 * 1 ^ 2) (by norm_num)
        (by linarith) (by nlinarith)).add_const hb).congr_of_eventuallyEq ?_
      filter_upwards [gt_mem_nhds h] with x hx
      exact sqrtSubLeaf_of_le (by linarith) zero_le_one (by linarith)
    · exact isConvexShapeAt_sqrtSubLeaf_one_of_two_le hA hB hM hL₁
        ((le_max_right _ _).trans hL) hm h
  have h := h₁.rescale hδ
  rwa [mul_div_cancel₀ r hδ.ne', ← sqrtSubLeaf_eq_mul_sqrtSubLeaf_one hδ] at h


end SymplecticGeometry

end
