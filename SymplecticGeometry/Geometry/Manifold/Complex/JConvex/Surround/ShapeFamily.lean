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
import SymplecticGeometry.Analysis.SpecialFunctions.Sqrt
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

* `SymplecticGeometry.exists_convexShapeFamily_struweShape`: given a family `φ` with the
  properties of the previous one, linear of slope `d` for `r ≤ ℓ β`, and `K ≥ exp (4 / d²)`,
  `K > 4`, the leaves `ℓ ≥ ℓ₁` over the cylinder of radius `δ`, for `ℓ₁ ≥ C δ`. The leaf `ℓ₁` is
  the function of `SymplecticGeometry.exists_isConvexShapeAt_eq_struweShape_eq_linear`, a
  Struwe shape near the cylinder joined to the line `ℓ₁ + d r`, up to `2 K δ`, and `φ ℓ₁` beyond;
  the leaf `ℓ` is that leaf raised by `ℓ - ℓ₁` up to `2 K δ` and `φ ℓ` beyond. The two pieces
  are both the line `ℓ + d r` on `[3 K δ / 2, 2 K δ]`, so that the family is smooth in
  `(ℓ, r)`; near the cylinder every leaf is a Struwe shape
  (`SymplecticGeometry.struweShape_add`).

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
  From `(2 + L) δ` on, the leaf `ℓ` is `√(64 r² - ℓ²)` (`SymplecticGeometry.sqrtSubLeaf_of_ge`).

* `SymplecticGeometry.exists_convexShapeFamily_sqrt_sub`: these leaves, for `L` as above and
  `K = 2 + L`, as the part `ℓ ∈ [-8 δ, 0]` of the family over the cylinder. The leaf `-8 δ` is
  `√(64 r² - 64 δ²)` (`SymplecticGeometry.sqrtSubLeaf_neg_eight_mul`); the family is jointly
  smooth where `δ < r` and `|ℓ| < 8 r`, since there the radicand is a convex combination of
  `64 (r² - δ²)` and `64 r² - ℓ²` (`SymplecticGeometry.contDiffOn_uncurry_sqrtSubLeaf`); the
  slope of each leaf tends to `+∞` at `δ` (`SymplecticGeometry.tendsto_deriv_sqrtSubLeaf`); and
  at each `r > δ` the leaves increase strictly with `ℓ`
  (`SymplecticGeometry.strictMonoOn_sqrtSubLeaf`).

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  §4.5: Lemma 4.19; §4.6: Lemma 4.23, Lemma 4.26 and Proposition 4.27.
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

/-- **Struwe shapes on the square-root family** (the leaves `ℓ ≥ ℓ₁` of Cieliebak–Eliashberg's
family of Proposition 4.27). Let `0 < d`, `exp (4 / d²) ≤ K`, `4 < K`, `0 < β`, and let `φ` be a
family as in `exists_convexShapeFamily_sqrt`: jointly smooth on `[0, ∞) × (0, ∞)`, with
`i`-convex members `φ ℓ`, `ℓ ≥ 0`, strictly increasing in `ℓ ≥ 0`, and with `φ ℓ r = ℓ + d r` for
`ℓ > 0` and `r ≤ ℓ β`. Then there is `C > 0` such that for all `δ > 0` and `ℓ₁ ≥ C δ` there is a
family `F` with:
* `(ℓ, r) ↦ F ℓ r` smooth at every point of `[ℓ₁, ∞) × (δ, ∞)`;
* each `F ℓ`, `ℓ ≥ ℓ₁`, an `i`-convex shape at every `r > δ`;
* at each `r > δ`, `F ℓ r` strictly increasing in `ℓ ≥ ℓ₁`;
* for every `ℓ`, `F ℓ` the Struwe shape `ℓ + struweShape δ K (d K δ)` on `(-∞, 3 K δ / 4]`, so
  that its slope tends to `+∞` at `δ`;
* for every `ℓ`, `F ℓ r = F ℓ₁ r + (ℓ - ℓ₁)` for `r < 2 K δ`;
* for `ℓ ≥ ℓ₁`, `F ℓ = φ ℓ` on `[3 K δ / 2, ∞)`. -/
theorem exists_convexShapeFamily_struweShape {d K β : ℝ} (hd : 0 < d)
    (hK : exp (4 / d ^ 2) ≤ K) (hK₄ : 4 < K) (hβ : 0 < β) {φ : ℝ → ℝ → ℝ}
    (hφs : ∀ q ∈ Ici 0 ×ˢ Ioi 0, ContDiffAt ℝ ∞ (Function.uncurry φ) q)
    (hφc : ∀ ℓ, 0 ≤ ℓ → ∀ r, 0 < r → IsConvexShapeAt (φ ℓ) r)
    (hφm : ∀ ℓ₁ ℓ₂, 0 ≤ ℓ₁ → ℓ₁ < ℓ₂ → ∀ r, 0 < r → φ ℓ₁ r < φ ℓ₂ r)
    (hφL : ∀ ℓ, 0 < ℓ → ∀ r ≤ ℓ * β, φ ℓ r = ℓ + d * r) :
    ∃ C, 0 < C ∧ ∀ δ, 0 < δ → ∀ ℓ₁, C * δ ≤ ℓ₁ → ∃ F : ℝ → ℝ → ℝ,
      (∀ q ∈ Ici ℓ₁ ×ˢ Ioi δ, ContDiffAt ℝ ∞ (Function.uncurry F) q) ∧
      (∀ ℓ, ℓ₁ ≤ ℓ → ∀ r, δ < r → IsConvexShapeAt (F ℓ) r) ∧
      (∀ r, δ < r → StrictMonoOn (fun ℓ ↦ F ℓ r) (Ici ℓ₁)) ∧
      (∀ ℓ, ∀ r ≤ 3 * K * δ / 4, F ℓ r = ℓ + struweShape δ K (d * K * δ) r) ∧
      (∀ ℓ, Tendsto (deriv (F ℓ)) (𝓝[>] δ) atTop) ∧
      (∀ ℓ r, r < 2 * K * δ → F ℓ r = F ℓ₁ r + (ℓ - ℓ₁)) ∧
      ∀ ℓ, ℓ₁ ≤ ℓ → ∀ r, 3 * K * δ / 2 ≤ r → F ℓ r = φ ℓ r := by
  have hK₁ : 1 < K := by linarith
  set s := √(log (2 * K))
  have hd3 : 0 < d ^ 3 := pow_pos hd 3
  set C := 2 * K * s + 4 * K * s ^ 3 + 2 * K / d ^ 3 + 2 * K / β + 1
  have hC₁ : 2 * K * s ≤ C := by
    have : 0 ≤ 4 * K * s ^ 3 := by positivity
    have : 0 ≤ 2 * K / d ^ 3 := by positivity
    have : 0 ≤ 2 * K / β := by positivity
    linarith
  have hC₂ : 4 * K * s ^ 3 ≤ C := by
    have : 0 ≤ 2 * K * s := by positivity
    have : 0 ≤ 2 * K / d ^ 3 := by positivity
    have : 0 ≤ 2 * K / β := by positivity
    linarith
  have hC₃ : 2 * K < C * d ^ 3 := by
    have : 0 ≤ 2 * K * s + 4 * K * s ^ 3 + 2 * K / β := by positivity
    have e : 2 * K / d ^ 3 * d ^ 3 = 2 * K := div_mul_cancel₀ _ hd3.ne'
    nlinarith
  have hC₄ : 2 * K < C * β := by
    have : 0 ≤ 2 * K * s + 4 * K * s ^ 3 + 2 * K / d ^ 3 := by positivity
    have e : 2 * K / β * β = 2 * K := div_mul_cancel₀ _ hβ.ne'
    nlinarith
  refine ⟨C, pos_of_mul_pos_left (by linarith) hβ.le, fun δ hδ ℓ₁ hℓ₁ ↦ ?_⟩
  obtain ⟨G, hGs, hGc, hGS, hGL⟩ := exists_isConvexShapeAt_eq_struweShape_eq_linear hd hδ hK hK₄
    (ℓ := ℓ₁) (by nlinarith) (by nlinarith) (by nlinarith)
  have hℓ₁β : 2 * K * δ < ℓ₁ * β := by nlinarith
  have hℓβ {ℓ : ℝ} (hℓ : ℓ₁ ≤ ℓ) : 2 * K * δ < ℓ * β :=
    hℓ₁β.trans_le (mul_le_mul_of_nonneg_right hℓ hβ.le)
  have hℓ₀ {ℓ : ℝ} (hℓ : ℓ₁ ≤ ℓ) : 0 ≤ ℓ := by
    have := pos_of_mul_pos_left ((by positivity : 0 < 2 * K * δ).trans hℓ₁β) hβ.le
    linarith
  have hKδ : 0 < K * δ := by positivity
  -- Below `2 K δ` the leaf `ℓ` is `G` raised by `ℓ - ℓ₁`; from there on it is `φ ℓ`.
  set F : ℝ → ℝ → ℝ := fun ℓ r ↦ if r < 2 * K * δ then G r + (ℓ - ℓ₁) else φ ℓ r
  have hFG {ℓ r : ℝ} (hr : r < 2 * K * δ) : F ℓ r = G r + (ℓ - ℓ₁) := by
    simp [F, hr]
  -- Where both pieces are lines, they agree.
  have hFφ {ℓ r : ℝ} (hℓ : 2 * K * δ < ℓ * β) (hr : 3 * K * δ / 2 ≤ r) : F ℓ r = φ ℓ r := by
    have hℓ0 : 0 < ℓ := pos_of_mul_pos_left (by linarith) hβ.le
    by_cases h : r < 2 * K * δ
    · rw [hFG h, hGL r hr, hφL ℓ hℓ0 r (by linarith)]
      ring
    · simp [F, h]
  have hFS (ℓ : ℝ) {r : ℝ} (hr : r ≤ 3 * K * δ / 4) :
      F ℓ r = struweShape δ K (ℓ + d * K * δ) r := by
    rw [hFG (by linarith), hGS r hr, struweShape_add, struweShape_add]
    ring
  have hFφ' {ℓ r : ℝ} (hℓ : ℓ₁ ≤ ℓ) (hr : 2 * K * δ ≤ r) :
      F ℓ =ᶠ[𝓝 r] φ ℓ := by
    filter_upwards [Ioi_mem_nhds (show 3 * K * δ / 2 < r by linarith)] with y hy
    exact hFφ (hℓβ hℓ) (mem_Ioi.1 hy).le
  refine ⟨F, ?_, fun ℓ hℓ r hr ↦ ?_, fun r hr ↦ ?_, fun ℓ r hr ↦ ?_, fun ℓ ↦ ?_,
    fun ℓ r hr ↦ by rw [hFG hr, hFG hr]; ring, fun ℓ hℓ r hr ↦ hFφ (hℓβ hℓ) hr⟩
  · rintro ⟨ℓ, r⟩ ⟨hℓ, hr⟩
    rw [mem_Ici] at hℓ
    rw [mem_Ioi] at hr
    rcases lt_or_ge r (2 * K * δ) with h | h
    · -- Near `(ℓ, r)` the family is `G r + (ℓ - ℓ₁)`.
      have he : Function.uncurry F =ᶠ[𝓝 (ℓ, r)] fun q ↦ G q.2 + (q.1 - ℓ₁) := by
        filter_upwards [(isOpen_lt continuous_snd continuous_const).mem_nhds h] with q hq
        exact hFG hq
      refine ContDiffAt.congr_of_eventuallyEq ?_ he
      exact ((hGs.contDiffAt (Ioi_mem_nhds hr)).comp _ contDiffAt_snd).add
        (contDiffAt_fst.sub contDiffAt_const)
    · -- Near `(ℓ, r)` the family is `φ`.
      have he : Function.uncurry F =ᶠ[𝓝 (ℓ, r)] Function.uncurry φ := by
        filter_upwards [(isOpen_lt continuous_const (continuous_fst.mul continuous_const)).mem_nhds
          (hℓβ hℓ), (isOpen_lt continuous_const continuous_snd).mem_nhds
          (show 3 * K * δ / 2 < r by linarith)] with q hq hq'
        exact hFφ hq hq'.le
      exact (hφs (ℓ, r) ⟨mem_Ici.2 (hℓ₀ hℓ), mem_Ioi.2 (by linarith)⟩).congr_of_eventuallyEq
        he
  · rcases lt_or_ge r (2 * K * δ) with h | h
    · refine ((hGc r ⟨hr, h.le⟩).add_const (sub_nonneg.2 hℓ)).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds h] with y hy
      exact hFG hy
    · exact (hφc ℓ (hℓ₀ hℓ) r (by linarith)).congr_of_eventuallyEq (hFφ' hℓ h)
  · intro ℓ hℓ ℓ' hℓ' hlt
    rw [mem_Ici] at hℓ hℓ'
    rcases lt_or_ge r (2 * K * δ) with h | h
    · simp only [hFG h]
      linarith
    · simp only [(hFφ' hℓ h).eq_of_nhds, (hFφ' hℓ' h).eq_of_nhds]
      exact hφm ℓ ℓ' (hℓ₀ hℓ) hlt r (by linarith)
  · rw [hFS ℓ hr, struweShape_add]
  · refine (tendsto_deriv_struweShape hδ hK₁.le (ℓ + d * K * δ)).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show δ < 3 * K * δ / 4 by nlinarith)] with x hx
    refine (Filter.EventuallyEq.deriv_eq ?_).symm
    filter_upwards [Iio_mem_nhds hx.2] with y hy
    exact hFS ℓ (mem_Iio.1 hy).le

/-! ### The explicit leaves below the cone -/

/-- The leaf `ℓ` of the explicit family of `i`-convex shapes over the cylinder of radius `δ`,
with a cutoff of width `L δ` starting at `2 δ`: with `h r = smoothTransition ((r - 2 δ) / (L δ))`,
`r ↦ (ℓ + 8 δ) / 64 (1 - h r) + √(64 (r² - δ²) + (64 δ² - ℓ²) h r)`. It is the bottom leaf
`√(64 r² - 64 δ²)` raised by `(ℓ + 8 δ) / 64` for `r ≤ 2 δ` (when `L, δ ≥ 0`), and, when
`L, δ > 0`, `√(64 r² - ℓ²)` for `r ≥ (2 + L) δ`, the standard shape when `ℓ ≤ 0`. -/
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

/-- From `(2 + L) δ` on, the leaf `ℓ` is `√(64 r² - ℓ²)`, the standard shape when `ℓ ≤ 0`. -/
theorem sqrtSubLeaf_of_ge {L ℓ r : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hr : (2 + L) * δ ≤ r) :
    sqrtSubLeaf L δ ℓ r = √(64 * r ^ 2 - ℓ ^ 2) := by
  rw [sqrtSubLeaf_def,
    smoothTransition.one_of_one_le ((one_le_div (by positivity)).2 (by linarith))]
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

/-- The leaf `m` for `δ = 1`, with the cutoff `smoothTransition ((x - 2) / L)` written out. -/
private theorem sqrtSubLeaf_one_eq (L m : ℝ) : sqrtSubLeaf L 1 m = fun x ↦
    (m + 8) / 64 * (1 - smoothTransition ((x - 2) / L)) +
      √(64 * x ^ 2 - 64 + (64 - m ^ 2) * smoothTransition ((x - 2) / L)) := by
  ext x
  simp only [sqrtSubLeaf_def, one_pow, mul_one]
  ring_nf

/-- The radicand of the leaf `ℓ` is positive at each `r` with `δ² < r²` and `ℓ² < 64 r²`: it is
`64 (r² - δ²) (1 - H) + (64 r² - ℓ²) H` for the cutoff `H ∈ [0, 1]`, a convex combination of two
positive numbers. -/
theorem sqrtSubLeaf_radicand_pos (L : ℝ) {ℓ r : ℝ} (hr : δ ^ 2 < r ^ 2)
    (hℓ : ℓ ^ 2 < 64 * r ^ 2) :
    0 < 64 * (r ^ 2 - δ ^ 2) +
      (64 * δ ^ 2 - ℓ ^ 2) * smoothTransition ((r - 2 * δ) / (L * δ)) := by
  have hH₀ := smoothTransition.nonneg ((r - 2 * δ) / (L * δ))
  rcases (smoothTransition.le_one ((r - 2 * δ) / (L * δ))).lt_or_eq with h | h
  · nlinarith [mul_nonneg hH₀ (sub_nonneg.2 hℓ.le)]
  · rw [h]; linarith

/-- For `m ^ 2 ≤ 64`, the radicand of the leaf `m` for `δ = 1` is positive at `x > 1`. -/
private theorem sqrtSubLeaf_one_radicand_pos {L m x : ℝ} (hm : m ^ 2 ≤ 64) (hx : 1 < x) :
    0 < 64 * x ^ 2 - 64 + (64 - m ^ 2) * smoothTransition ((x - 2) / L) := by
  simpa only [one_pow, mul_one, mul_sub] using
    sqrtSubLeaf_radicand_pos (δ := 1) L (by nlinarith) (by nlinarith)

/-- The slope of the leaf `m` for `δ = 1` at `x > 1`, for `m ^ 2 ≤ 64`. -/
private theorem deriv_sqrtSubLeaf_one {L m x : ℝ} (hm : m ^ 2 ≤ 64) (hx : 1 < x) :
    deriv (sqrtSubLeaf L 1 m) x =
      -((m + 8) / 64) * (deriv smoothTransition ((x - 2) / L) / L) +
        (128 * x + (64 - m ^ 2) * (deriv smoothTransition ((x - 2) / L) / L)) /
          (2 * √(64 * x ^ 2 - 64 + (64 - m ^ 2) * smoothTransition ((x - 2) / L))) := by
  have hH := (((hasDerivAt_id' x).sub_const 2).div_const L).smoothTransition
  have hF := (((hasDerivAt_pow 2 x).const_mul 64).sub_const 64).add (hH.const_mul (64 - m ^ 2))
  rw [sqrtSubLeaf_one_eq]
  refine HasDerivAt.deriv ?_
  refine (((hH.const_sub 1).const_mul _).add
    (hF.sqrt (sqrtSubLeaf_one_radicand_pos hm hx).ne')).congr_deriv ?_
  simp only [Pi.add_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  ring

/-- The second derivative of the leaf `m` for `δ = 1` at `x > 1`, for `m ^ 2 ≤ 64`. -/
private theorem iteratedDeriv_two_sqrtSubLeaf_one {L m x : ℝ} (hm : m ^ 2 ≤ 64) (hx : 1 < x) :
    iteratedDeriv 2 (sqrtSubLeaf L 1 m) x =
      -((m + 8) / 64) * (deriv (deriv smoothTransition) ((x - 2) / L) / L ^ 2) +
        (128 + (64 - m ^ 2) * (deriv (deriv smoothTransition) ((x - 2) / L) / L ^ 2)) /
          (2 * √(64 * x ^ 2 - 64 + (64 - m ^ 2) * smoothTransition ((x - 2) / L))) -
        (128 * x + (64 - m ^ 2) * (deriv smoothTransition ((x - 2) / L) / L)) ^ 2 /
          (4 * √(64 * x ^ 2 - 64 + (64 - m ^ 2) * smoothTransition ((x - 2) / L)) ^ 3) := by
  have hev : deriv (sqrtSubLeaf L 1 m) =ᶠ[𝓝 x] fun y ↦
      -((m + 8) / 64) * (deriv smoothTransition ((y - 2) / L) / L) +
        (128 * y + (64 - m ^ 2) * (deriv smoothTransition ((y - 2) / L) / L)) /
          (2 * √(64 * y ^ 2 - 64 + (64 - m ^ 2) * smoothTransition ((y - 2) / L))) := by
    filter_upwards [lt_mem_nhds hx] with y hy using deriv_sqrtSubLeaf_one hm hy
  have hu := ((hasDerivAt_id' x).sub_const 2).div_const L
  have hH₁ := hu.deriv_smoothTransition.div_const L
  have hF := (((hasDerivAt_pow 2 x).const_mul 64).sub_const 64).add
    (hu.smoothTransition.const_mul (64 - m ^ 2))
  have hS := sqrt_pos.2 (sqrtSubLeaf_one_radicand_pos (L := L) hm hx)
  have hd := (hH₁.const_mul (-((m + 8) / 64))).add
    ((((hasDerivAt_id' x).const_mul 128).add (hH₁.const_mul (64 - m ^ 2))).div
      ((hF.sqrt (sqrtSubLeaf_one_radicand_pos hm hx).ne').const_mul 2) (mul_pos two_pos hS).ne')
  rw [iteratedDeriv_succ, iteratedDeriv_one, hev.deriv_eq]
  refine HasDerivAt.deriv ?_
  refine hd.congr_deriv ?_
  simp only [Pi.add_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  generalize √(64 * x ^ 2 - 64 + (64 - m ^ 2) * smoothTransition ((x - 2) / L)) = S at hS ⊢
  have hS₀ := hS.ne'
  field_simp
  ring

/-- For `L ≥ 1` large compared with the bounds `A` of `smoothTransition'`, `B` of
`smoothTransition''` and `M` of `x smoothTransition'' x`, the first derivative of the cutoff
`x ↦ smoothTransition ((x - 2) / L)` is at most `1 / 64` in absolute value, and so is its second
derivative times `x`. -/
private theorem abs_deriv_cutoff_le {A B M L : ℝ} (hA : ∀ x, |deriv smoothTransition x| ≤ A)
    (hB : ∀ x, |deriv (deriv smoothTransition) x| ≤ B)
    (hM : ∀ x, |x * deriv (deriv smoothTransition) x| ≤ M)
    (hL₁ : 1 ≤ L) (hL : 64 * (A + 2 * B + M) ≤ L) (x : ℝ) :
    |deriv smoothTransition ((x - 2) / L) / L| ≤ 1 / 64 ∧
      |x * (deriv (deriv smoothTransition) ((x - 2) / L) / L ^ 2)| ≤ 1 / 64 := by
  have hL₀ : 0 < L := by linarith
  have hA₀ : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  have hB₀ : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hM₀ : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set y := (x - 2) / L with hy
  have hxy : x = 2 + L * y := by rw [hy]; field_simp; ring
  refine ⟨?_, ?_⟩
  · rw [abs_div, abs_of_pos hL₀, div_le_iff₀ hL₀]
    nlinarith [hA y]
  · set s := deriv (deriv smoothTransition) y
    have e : x * (s / L ^ 2) = (2 * s + L * (y * s)) / L ^ 2 := by
      rw [hxy]
      field_simp
    rw [e, abs_div, abs_of_pos (pow_pos hL₀ 2), div_le_iff₀ (pow_pos hL₀ 2)]
    have h1 := abs_add_le (2 * s) (L * (y * s))
    rw [abs_mul, abs_mul, abs_of_pos hL₀, abs_two] at h1
    have h2 := hB y
    have h3 := hM y
    refine h1.trans ?_
    nlinarith

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
  have hm₂ : m ^ 2 ≤ 64 := by nlinarith
  have hr₁ : 1 < r := by linarith
  obtain ⟨hp, hq⟩ := abs_deriv_cutoff_le hA hB hM hL₁ hL r
  exact isConvexShapeAt_of_bounds (by linarith) (by linarith) (by linarith) (by nlinarith)
    (smoothTransition.nonneg _) (smoothTransition.le_one _) hp hq hr (sqrt_nonneg _)
    (sq_sqrt (sqrtSubLeaf_one_radicand_pos hm₂ hr₁).le) (congrFun (sqrtSubLeaf_one_eq L m) r)
    (deriv_sqrtSubLeaf_one hm₂ hr₁) (iteratedDeriv_two_sqrtSubLeaf_one hm₂ hr₁)

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

/-- The bottom leaf: the leaf `-8 δ` is `√(64 r² - 64 δ²)` at every `r`. -/
theorem sqrtSubLeaf_neg_eight_mul (L δ r : ℝ) :
    sqrtSubLeaf L δ (-8 * δ) r = √(64 * r ^ 2 - 64 * δ ^ 2) := by
  rw [sqrtSubLeaf_def]; ring_nf

/-- The family `(ℓ, r) ↦ sqrtSubLeaf L δ ℓ r` is smooth where `δ < r` and `|ℓ| < 8 r`, for
`0 ≤ δ`: there the radicand is positive. -/
theorem contDiffOn_uncurry_sqrtSubLeaf (L : ℝ) (hδ : 0 ≤ δ) :
    ContDiffOn ℝ ∞ (Function.uncurry (sqrtSubLeaf L δ)) {p | δ < p.2 ∧ |p.1| < 8 * p.2} := by
  have e : Function.uncurry (sqrtSubLeaf L δ) = fun p : ℝ × ℝ ↦
      (p.1 + 8 * δ) / 64 * (1 - smoothTransition ((p.2 - 2 * δ) / (L * δ))) +
        √(64 * (p.2 ^ 2 - δ ^ 2) +
          (64 * δ ^ 2 - p.1 ^ 2) * smoothTransition ((p.2 - 2 * δ) / (L * δ))) := by
    ext ⟨ℓ, r⟩
    rw [Function.uncurry_apply_pair, sqrtSubLeaf_def]
  have hH : ContDiff ℝ ∞ fun p : ℝ × ℝ ↦ smoothTransition ((p.2 - 2 * δ) / (L * δ)) :=
    smoothTransition.contDiff.comp ((contDiff_snd.sub contDiff_const).div_const _)
  rintro ⟨ℓ, r⟩ ⟨hr, hℓ⟩
  dsimp only at hr hℓ
  have hrδ : δ ^ 2 < r ^ 2 := by gcongr
  have hℓr : ℓ ^ 2 < 64 * r ^ 2 := by
    have := sq_lt_sq' (by linarith [abs_nonneg ℓ]) hℓ
    rw [sq_abs] at this
    linarith
  have hrad := sqrtSubLeaf_radicand_pos L hrδ hℓr
  rw [e]
  exact (((contDiff_fst.add contDiff_const).div_const 64).mul
    (contDiff_const.sub hH)).contDiffAt.add
    (((contDiff_const.mul ((contDiff_snd.pow 2).sub contDiff_const)).add
      ((contDiff_const.sub (contDiff_fst.pow 2)).mul hH)).contDiffAt.sqrt
      hrad.ne') |>.contDiffWithinAt

/-- The slope of every leaf tends to `+∞` at `δ`, where the leaves meet the cylinder. -/
theorem tendsto_deriv_sqrtSubLeaf {L : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ) (ℓ : ℝ) :
    Tendsto (deriv (sqrtSubLeaf L δ ℓ)) (𝓝[>] δ) atTop := by
  refine (tendsto_deriv_sqrt_sub (a := 64) (by norm_num) hδ).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (by linarith : δ < 2 * δ)] with r hr
  have he : sqrtSubLeaf L δ ℓ =ᶠ[𝓝 r]
      fun x ↦ √(64 * x ^ 2 - 64 * δ ^ 2) + (ℓ + 8 * δ) / 64 := by
    filter_upwards [gt_mem_nhds hr.2] with x hx using sqrtSubLeaf_of_le hL hδ.le hx.le
  rw [he.deriv_eq, deriv_add_const]

/-- For `0 ≤ δ`, at each `r > δ`, the leaves `ℓ ∈ [-8 δ, 0]` are strictly increasing in `ℓ`:
both terms of `sqrtSubLeaf` are nondecreasing in `ℓ ≤ 0`, the first strictly where the cutoff
is below `1` and the second where it is positive. -/
theorem strictMonoOn_sqrtSubLeaf (L : ℝ) (hδ : 0 ≤ δ) {r : ℝ} (hr : δ < r) :
    StrictMonoOn (fun ℓ ↦ sqrtSubLeaf L δ ℓ r) (Icc (-8 * δ) 0) := by
  intro ℓ₁ hℓ₁ ℓ₂ hℓ₂ h
  simp only [sqrtSubLeaf_def]
  set H := smoothTransition ((r - 2 * δ) / (L * δ))
  have hH₀ : 0 ≤ H := smoothTransition.nonneg _
  have hH₁ : H ≤ 1 := smoothTransition.le_one _
  have hrδ : δ ^ 2 < r ^ 2 := by gcongr
  have hsq : ℓ₂ ^ 2 < ℓ₁ ^ 2 := by nlinarith [hℓ₂.2]
  rcases hH₁.lt_or_eq with hH | hH
  · exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_right (by linarith) (by linarith))
      (sqrt_le_sqrt (by nlinarith))
  · simp only [hH, sub_self, mul_zero, zero_add, mul_one]
    exact sqrt_lt_sqrt (by nlinarith [hℓ₁.1, hℓ₁.2]) (by linarith)

/-- **The leaves `ℓ ∈ [-8 δ, 0]` of the family over the cylinder of radius `δ`**
(the part `ℓ ≤ 0` of Cieliebak–Eliashberg's family of §4.6). There is `K > 2` such that for
every `δ > 0` there is a family `χ ℓ` of functions with:
* `(ℓ, r) ↦ χ ℓ r` smooth on a neighbourhood of `[-8 δ, 0] × (δ, ∞)`;
* each `χ ℓ`, `ℓ ∈ [-8 δ, 0]`, an `i`-convex shape at every `r > δ`;
* the bottom leaf `χ (-8 δ) r = √(64 r² - 64 δ²)`;
* on `[δ, 2 δ]`, `χ ℓ` the bottom leaf raised by `(ℓ + 8 δ) / 64`, so that its slope tends to
  `+∞` at `δ`;
* from `K δ` on, `χ ℓ` the standard shape `√(64 r² + ℓ |ℓ|)`;
* at each `r > δ`, `χ ℓ r` strictly increasing in `ℓ ∈ [-8 δ, 0]`.

The family is explicit, `sqrtSubLeaf`, rather than the book's bending of linear shapes
(Lemma 4.25). -/
theorem exists_convexShapeFamily_sqrt_sub :
    ∃ K, 2 < K ∧ ∀ δ, 0 < δ → ∃ χ : ℝ → ℝ → ℝ,
      (∃ U ∈ 𝓝ˢ (Icc (-8 * δ) 0 ×ˢ Ioi δ), ContDiffOn ℝ ∞ (Function.uncurry χ) U) ∧
      (∀ ℓ ∈ Icc (-8 * δ) 0, ∀ r, δ < r → IsConvexShapeAt (χ ℓ) r) ∧
      (∀ r, χ (-8 * δ) r = √(64 * r ^ 2 - 64 * δ ^ 2)) ∧
      (∀ ℓ ∈ Icc (-8 * δ) 0, ∀ r ∈ Icc δ (2 * δ),
        χ ℓ r = (ℓ + 8 * δ) / 64 + √(64 * r ^ 2 - 64 * δ ^ 2)) ∧
      (∀ ℓ ∈ Icc (-8 * δ) 0, Tendsto (deriv (χ ℓ)) (𝓝[>] δ) atTop) ∧
      (∀ ℓ ∈ Icc (-8 * δ) 0, ∀ r, K * δ ≤ r → χ ℓ r = √(64 * r ^ 2 + ℓ * |ℓ|)) ∧
      ∀ r, δ < r → StrictMonoOn (fun ℓ ↦ χ ℓ r) (Icc (-8 * δ) 0) := by
  obtain ⟨L, hL, hconv⟩ := exists_isConvexShapeAt_sqrtSubLeaf
  refine ⟨2 + L, by linarith, fun δ hδ ↦ ⟨sqrtSubLeaf L δ,
    ⟨_, ?_, contDiffOn_uncurry_sqrtSubLeaf L hδ.le⟩,
    fun ℓ hℓ r hr ↦ hconv L le_rfl δ hδ ℓ hℓ r hr, sqrtSubLeaf_neg_eight_mul L δ,
    fun ℓ _ r hr ↦ ?_, fun ℓ _ ↦ tendsto_deriv_sqrtSubLeaf (by linarith) hδ ℓ,
    fun ℓ hℓ r hr ↦ ?_, fun r hr ↦ strictMonoOn_sqrtSubLeaf L hδ.le hr⟩⟩
  · refine ((isOpen_lt continuous_const continuous_snd).inter
      (isOpen_lt (by fun_prop : Continuous fun p : ℝ × ℝ ↦ |p.1|)
        (by fun_prop : Continuous fun p : ℝ × ℝ ↦ 8 * p.2))).mem_nhdsSet.2 ?_
    rintro ⟨ℓ, r⟩ ⟨hℓ, hr⟩
    rw [mem_Ioi] at hr
    exact ⟨hr, (abs_of_nonpos hℓ.2).trans_lt (by linarith [hℓ.1])⟩
  · rw [sqrtSubLeaf_of_le (by linarith) hδ.le hr.2, add_comm]
  · rw [sqrtSubLeaf_of_ge (by linarith) hδ hr, abs_of_nonpos hℓ.2]
    ring_nf

end SymplecticGeometry

end
