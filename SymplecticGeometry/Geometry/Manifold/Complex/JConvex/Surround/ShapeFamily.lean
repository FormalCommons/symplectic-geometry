/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.SpecialShape

import Mathlib.Analysis.Complex.ExponentialBounds
import SymplecticGeometry.Analysis.Calculus.IteratedDeriv.Prod

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

end SymplecticGeometry

end
