/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.SpecialShape
public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.CutoffLeaf
public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.BridgeLeaf

import Mathlib.Analysis.Complex.ExponentialBounds
import SymplecticGeometry.Analysis.Calculus.IteratedDeriv.Prod
import SymplecticGeometry.Analysis.SpecialFunctions.SmoothTransition.Deriv
import SymplecticGeometry.Order.Interval.Set.Piecewise
import SymplecticGeometry.Topology.ContinuousOn
import SymplecticGeometry.Topology.Order.Piecewise
import TauCeti.Analysis.Calculus.ContDiff.Prod
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

* `SymplecticGeometry.exists_convexShapeFamily_struweShape_sqrt`: the previous construction on
  the square-root family with `a = 64` and `γ' = min γ (1 / 16)`, for `K = exp (4 / d²)` and the
  base point `ℓ₀ = C δ`, with what the bridge family of `Surround/BridgeLeaf.lean` and the
  leaves `ℓ ≥ 2 ℓ₀` of Proposition 4.27 use: every leaf is a constant plus `struweShape δ 4 0`
  up to `9 δ / 2` (`SymplecticGeometry.struweShape_eq_struweShape_apply_mul`), each leaf
  `ℓ ≥ ℓ₀` lies above `ℓ` and is standard from `ℓ γ'` on, the slopes of the leaves
  `ℓ ∈ [ℓ₀, 2 ℓ₀]` are bounded on `[3 δ, ℓ / 4]` (a continuous function on a compact set), and
  the top leaf has height between `1` and `1 + γ`.

* `SymplecticGeometry.sqrtSubLeaf` and `SymplecticGeometry.exists_isConvexShapeAt_sqrtSubLeaf`:
  the leaves `ℓ ∈ [-8 δ, 0]` of the family over the cylinder of radius `δ`. They do not come from
  bending linear shapes, as in Cieliebak and Eliashberg's Lemma 4.25, but have a closed form: the
  leaf `ℓ` is the cutoff leaf `SymplecticGeometry.cutoffLeaf L δ b c` of `Surround/CutoffLeaf.lean`
  with `b = (ℓ + 8 δ) / 64` and `c = 64 δ² - ℓ²`, that is, with the cutoff
  `h r = smoothTransition ((r - 2 δ) / (L δ))`,
  `(ℓ + 8 δ) / 64 (1 - h r) + √(64 (r² - δ²) + (64 δ² - ℓ²) h r)`. Since `0 ≤ b ≤ δ / 8` and
  `0 ≤ c ≤ 64 δ²`, for `L` large enough every leaf is an `i`-convex shape at every `r > δ`
  (`SymplecticGeometry.exists_isConvexShapeAt_cutoffLeaf`). The rescaling to `δ = 1`
  (`SymplecticGeometry.sqrtSubLeaf_eq_mul_sqrtSubLeaf_one`), the form up to `2 δ`
  (`SymplecticGeometry.sqrtSubLeaf_of_le`) and the slope at `δ` are those of `cutoffLeaf`.
  From `(2 + L) δ` on, the leaf `ℓ` is `√(64 r² - ℓ²)` (`SymplecticGeometry.sqrtSubLeaf_of_ge`).
  Its leaf `0` is the leaf `0` of `SymplecticGeometry.sqrtAddLeaf`
  (`SymplecticGeometry.sqrtAddLeaf_zero`).

* `SymplecticGeometry.exists_convexShapeFamily_sqrt_sub`: these leaves, for `L` as above and
  `K = 2 + L`, as the part `ℓ ∈ [-8 δ, 0]` of the family over the cylinder. The leaf `-8 δ` is
  `√(64 r² - 64 δ²)` (`SymplecticGeometry.sqrtSubLeaf_neg_eight_mul`); the family is jointly
  smooth where `δ < r` and `|ℓ| < 8 r`, since there the radicand is a convex combination of
  `64 (r² - δ²)` and `64 r² - ℓ²` (`SymplecticGeometry.contDiffOn_uncurry_sqrtSubLeaf`); the
  slope of each leaf tends to `+∞` at `δ` (`SymplecticGeometry.tendsto_deriv_sqrtSubLeaf`); and
  at each `r > δ` the leaves increase strictly with `ℓ`
  (`SymplecticGeometry.strictMonoOn_sqrtSubLeaf`).

* `SymplecticGeometry.surroundFamily`: the family of Proposition 4.27 over the cylinder of
  radius `δ`, glued from four pieces along `ℓ`: `sqrtSubLeaf` for `ℓ ≤ 0`, the Struwe switch
  leaves `struweSwitchLeaf` (`Surround/CutoffLeaf.lean`) up to `7 δ`, the bridge family
  `bridgeFamily` (`Surround/BridgeLeaf.lean`) up to `2 ℓ₀`, and a given family `F` beyond. On
  `(δ, ∞)` neighbouring pieces agree at the junctions `0`, `7 δ` and `2 ℓ₀`
  (`SymplecticGeometry.surroundFamily_eq_struweSwitchLeaf`,
  `SymplecticGeometry.surroundFamily_eqOn_bridgeFamily`,
  `SymplecticGeometry.surroundFamily_eqOn_of_ge`). Leaf by leaf, for `ℓ ∈ [-8 δ, ℓₜ]` and `F`
  with the properties that the bridge family asks of it on `[ℓ₀, ℓₜ]`, each leaf is an
  `i`-convex shape at every `r > δ` (`SymplecticGeometry.isConvexShapeAt_surroundFamily`),
  smooth on `(δ, ∞)`, continuous on `[δ, ∞)` with slope tending to `+∞` at `δ`, and strictly
  increasing on `[δ, ∞)` (`SymplecticGeometry.strictMonoOn_surroundFamily`); its leaf `-8 δ` is
  `√(64 r² - 64 δ²)` (`SymplecticGeometry.surroundFamily_neg_eight_mul`). Across the leaves,
  once `(ℓ, r) ↦ F ℓ r` is smooth on `[ℓ₀, ℓₜ] × (δ, ∞)`, every `r`-derivative of the family is
  jointly continuous on `[-8 δ, ℓₜ] × (δ, ∞)`
  (`SymplecticGeometry.continuousOn_iteratedDeriv_surroundFamily`): on each of the closed pieces
  `[-8 δ, 0]`, `[0, 7 δ]`, the three stages of the bridge family and `[2 ℓ₀, ℓₜ]`, the leaves
  agree on `(δ, ∞)` with a formula smooth in `(ℓ, r)`
  (`continuousOn_iteratedDeriv_prod_right_of_eqOn`), and the pieces are glued with
  `ContinuousOn.union_prod_of_isClosed`.
  Far out every leaf is the standard leaf `√(64 r² + ℓ |ℓ|)`: the leaves `ℓ ≤ 7 δ` from
  `(2 + L) δ` on (`SymplecticGeometry.surroundFamily_eq_sqrt_of_le`), and all leaves from
  `(t₁ + 2 δ) / 6` and the radius where `F` is standard on
  (`SymplecticGeometry.surroundFamily_eq_sqrt`), for `t₁ = bridgeHeight L δ ℓ₀`. When `t₁` and
  `ℓ₀` are small and `F 1` lies above `1` and above the other leaves `F ℓ`, every leaf lies below
  the leaf `1` (`SymplecticGeometry.surroundFamily_le_surroundFamily_one`): near the cylinder the
  bridge leaves are below `1` or equal to `F ℓ` (`SymplecticGeometry.bridgeFamily_le_or_eq`), and
  further out below the standard leaf `ℓ` or equal to `F ℓ`
  (`SymplecticGeometry.bridgeFamily_le_sqrt_or_eq`).

* `SymplecticGeometry.exists_convexShapeFamily_surround` (Proposition 4.27): for `0 < γ` and
  every small enough `δ > 0`, the glued family with `L` large, `F` and `ℓ₀ = C δ` from
  `SymplecticGeometry.exists_convexShapeFamily_struweShape_sqrt`, and `ℓₜ = 1`. Its leaves are
  standard from `γ` on once `t₁ + 2 δ ≤ 6 γ`, lie below the top leaf once `2 t₁ + 18 ℓ₀ ≤ 1`,
  and the leaves near the bottom one are standard from `(2 + L) δ` on; both bounds on `t₁` hold
  for small `δ`, as `t₁ ≤ 6 ℓ₀ + (30 + 8 L) δ` (`SymplecticGeometry.bridgeHeight_le`).

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
  -- Where both pieces are lines, they agree.
  have hGφ {ℓ : ℝ} (hℓ : 2 * K * δ < ℓ * β) :
      EqOn (fun r ↦ G r + (ℓ - ℓ₁)) (φ ℓ) (Icc (3 * K * δ / 2) (ℓ * β)) := fun r hr ↦ by
    dsimp only
    rw [hGL r hr.1, hφL ℓ (pos_of_mul_pos_left (by linarith) hβ.le) r hr.2]
    ring
  -- Up to `2 K δ` the leaf `ℓ` is `G` raised by `ℓ - ℓ₁`; after it, it is `φ ℓ`.
  set F : ℝ → ℝ → ℝ := fun ℓ r ↦ if r ≤ 2 * K * δ then G r + (ℓ - ℓ₁) else φ ℓ r
  have hFG {ℓ r : ℝ} (hr : r ≤ 2 * K * δ) : F ℓ r = G r + (ℓ - ℓ₁) := by
    simp [F, hr]
  have hFφ {ℓ r : ℝ} (hℓ : 2 * K * δ < ℓ * β) (hr : 3 * K * δ / 2 ≤ r) : F ℓ r = φ ℓ r :=
    EqOn.eqOn_ite_le_right (s := Ici (3 * K * δ / 2))
      ((hGφ hℓ).mono fun y hy ↦ mem_Icc.2 ⟨mem_Ici.1 hy.1, by linarith [mem_Iic.1 hy.2]⟩) hr
  have hFS (ℓ : ℝ) {r : ℝ} (hr : r ≤ 3 * K * δ / 4) :
      F ℓ r = struweShape δ K (ℓ + d * K * δ) r := by
    rw [hFG (by linarith), hGS r hr, struweShape_add, struweShape_add]
    ring
  have hFG' {ℓ r : ℝ} (hℓ : ℓ₁ ≤ ℓ) (hr : r < ℓ * β) :
      F ℓ =ᶠ[𝓝 r] fun y ↦ G y + (ℓ - ℓ₁) :=
    ((hGφ (hℓβ hℓ)).mono Ioo_subset_Icc_self).eventuallyEq_ite_le_left (by linarith) hr
  have hFφ' {ℓ r : ℝ} (hℓ : ℓ₁ ≤ ℓ) (hr : 2 * K * δ ≤ r) : F ℓ =ᶠ[𝓝 r] φ ℓ :=
    ((hGφ (hℓβ hℓ)).mono Ioo_subset_Icc_self).eventuallyEq_ite_le_right (hℓβ hℓ)
      (by linarith)
  refine ⟨F, ?_, fun ℓ hℓ r hr ↦ ?_, fun r hr ↦ ?_, fun ℓ r hr ↦ ?_, fun ℓ ↦ ?_,
    fun ℓ r hr ↦ by rw [hFG hr.le, hFG hr.le]; ring, fun ℓ hℓ r hr ↦ hFφ (hℓβ hℓ) hr⟩
  · rintro ⟨ℓ, r⟩ ⟨hℓ, hr⟩
    rw [mem_Ici] at hℓ
    rw [mem_Ioi] at hr
    rcases lt_or_ge r (2 * K * δ) with h | h
    · -- Near `(ℓ, r)` the family is `G r + (ℓ - ℓ₁)`.
      have he : Function.uncurry F =ᶠ[𝓝 (ℓ, r)] fun q ↦ G q.2 + (q.1 - ℓ₁) := by
        filter_upwards [(isOpen_lt continuous_snd continuous_const).mem_nhds h] with q hq
        exact hFG hq.le
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
    · exact ((hGc r ⟨hr, h.le⟩).add_const (sub_nonneg.2 hℓ)).congr_of_eventuallyEq
        (hFG' hℓ (h.trans (hℓβ hℓ)))
    · exact (hφc ℓ (hℓ₀ hℓ) r (by linarith)).congr_of_eventuallyEq (hFφ' hℓ h)
  · intro ℓ hℓ ℓ' hℓ' hlt
    rw [mem_Ici] at hℓ hℓ'
    rcases lt_or_ge r (2 * K * δ) with h | h
    · simp only [hFG h.le]
      linarith
    · simp only [(hFφ' hℓ h).eq_of_nhds, (hFφ' hℓ' h).eq_of_nhds]
      exact hφm ℓ ℓ' (hℓ₀ hℓ) hlt r (by linarith)
  · rw [hFS ℓ hr, struweShape_add]
  · exact tendsto_deriv_of_eqOn_struweShape hδ hK₁.le (show δ < 3 * K * δ / 4 by nlinarith)
      fun x hx ↦ hFS ℓ hx.2.le

/-- **The leaves `ℓ ≥ ℓ₀` of the surrounding family** (Cieliebak–Eliashberg, Proposition 4.27).
For `0 < γ` there is `C ≥ 24` such that for every `δ > 0` with `2 C δ ≤ 1`, writing
`ℓ₀ = C δ` and `γ' = min γ (1 / 16)`, there are a family `F` and a bound `M ≥ 8` with:
* `(ℓ, r) ↦ F ℓ r` smooth at every point of `[ℓ₀, ∞) × (δ, ∞)`, so each `F ℓ`, `ℓ ≥ ℓ₀`,
  smooth on `(δ, ∞)`;
* each `F ℓ`, `ℓ ≥ ℓ₀`, an `i`-convex shape at every `r > δ`, and, at each `r > δ`, `F ℓ r`
  strictly increasing in `ℓ ≥ ℓ₀`;
* every `F ℓ` a constant plus `struweShape δ 4 0` on `[δ, 9 δ / 2]`, with slope tending to `+∞`
  at `δ`;
* each `F ℓ`, `ℓ ≥ ℓ₀`, continuous on `[δ, ∞)` and above `ℓ` there;
* each `F ℓ`, `ℓ ≥ ℓ₀`, the standard leaf `√(64 r² + ℓ²)` for `r ≥ ℓ γ'`, hence for `r ≥ ℓ / 4`;
* `|∂F/∂r| ≤ M` on the leaves `ℓ ∈ [ℓ₀, 2 ℓ₀]` over `[3 δ, ℓ / 4]`;
* the top leaf has height `1 < F 1 δ < 1 + γ`.

The family is that of `exists_convexShapeFamily_struweShape` on the square-root family
`exists_convexShapeFamily_sqrt` with `a = 64` and `γ'`, for `K = exp (4 / d²)` and the base
point `ℓ₀`. -/
theorem exists_convexShapeFamily_struweShape_sqrt {γ : ℝ} (hγ : 0 < γ) :
    ∃ C, 24 ≤ C ∧ ∀ δ, 0 < δ → 2 * C * δ ≤ 1 → ∃ F : ℝ → ℝ → ℝ, ∃ M, 8 ≤ M ∧
      (∀ q ∈ Ici (C * δ) ×ˢ Ioi δ, ContDiffAt ℝ ∞ (Function.uncurry F) q) ∧
      (∀ ℓ, C * δ ≤ ℓ → ContDiffOn ℝ ∞ (F ℓ) (Ioi δ)) ∧
      (∀ ℓ, C * δ ≤ ℓ → ∀ r, δ < r → IsConvexShapeAt (F ℓ) r) ∧
      (∀ r, δ < r → StrictMonoOn (fun ℓ ↦ F ℓ r) (Ici (C * δ))) ∧
      (∀ ℓ, ∃ c, ∀ r ∈ Icc δ (9 * δ / 2), F ℓ r = c + struweShape δ 4 0 r) ∧
      (∀ ℓ, Tendsto (deriv (F ℓ)) (𝓝[>] δ) atTop) ∧
      (∀ ℓ, C * δ ≤ ℓ → ContinuousOn (F ℓ) (Ici δ)) ∧
      (∀ ℓ, C * δ ≤ ℓ → ∀ r, δ ≤ r → ℓ < F ℓ r) ∧
      (∀ ℓ, C * δ ≤ ℓ → ∀ r, ℓ * min γ (1 / 16) ≤ r → F ℓ r = √(64 * r ^ 2 + ℓ ^ 2)) ∧
      (∀ ℓ, C * δ ≤ ℓ → ∀ r, ℓ / 4 ≤ r → F ℓ r = √(64 * r ^ 2 + ℓ ^ 2)) ∧
      (∀ ℓ ∈ Icc (C * δ) (2 * (C * δ)), ∀ r ∈ Icc (3 * δ) (ℓ / 4), |deriv (F ℓ) r| ≤ M) ∧
      1 < F 1 δ ∧ F 1 δ < 1 + γ := by
  set γ' := min γ (1 / 16)
  have hγ'₀ : 0 < γ' := lt_min hγ (by norm_num)
  have hγ'γ : γ' ≤ γ := min_le_left _ _
  have hγ'16 : γ' ≤ 1 / 16 := min_le_right _ _
  obtain ⟨d, ⟨hd₀, hd₁⟩, β, ⟨hβ₀, -⟩, φ, -, hφc, hφs, -, hφm, hφS, hφL, -⟩ :=
    exists_convexShapeFamily_sqrt (a := 64) (by norm_num) hγ'₀
  set K := exp (4 / d ^ 2)
  -- `K ≥ exp 4 = exp 2 ^ 2 ≥ 9`.
  have hK₉ : 9 ≤ K := by
    have h2 : 3 ≤ exp 2 := by linarith [add_one_le_exp (2 : ℝ)]
    have h4 : (4 : ℝ) ≤ 4 / d ^ 2 :=
      (le_div_iff₀ (by positivity)).2 (by nlinarith [mul_pos hd₀ hd₀])
    calc (9 : ℝ) ≤ exp 2 * exp 2 := by nlinarith
      _ = exp 4 := by rw [← exp_add]; norm_num
      _ ≤ K := exp_le_exp.2 h4
  obtain ⟨C₀, hC₀, hF⟩ := exists_convexShapeFamily_struweShape hd₀ le_rfl (by linarith) hβ₀
    hφs hφc hφm hφL
  set C := max C₀ (max 24 (3 * K / (2 * γ')))
  have hC₀C : C₀ ≤ C := le_max_left _ _
  have hC24 : 24 ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCK : 3 * K / (2 * γ') ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, hC24, fun δ hδ hCδ ↦ ?_⟩
  set ℓ₀ := C * δ with hℓ₀
  have hℓ₀pos : 0 < ℓ₀ := by positivity
  -- The far part of every leaf `ℓ ≥ ℓ₀` starts before `ℓ γ'`.
  have hKℓ : 3 * K * δ / 2 ≤ ℓ₀ * γ' := by
    have := mul_le_mul_of_nonneg_right hCK (by positivity : 0 ≤ δ * γ')
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at this
    rw [hℓ₀]
    nlinarith
  obtain ⟨F, hFs, hFc, hFm, hFS, hFt, -, hFφ⟩ :=
    hF δ hδ ℓ₀ (mul_le_mul_of_nonneg_right hC₀C hδ.le)
  have hS₀ : d * δ ≤ struweShape δ K (d * K * δ) δ := by
    have := sub_le_struweShape hd₀ hδ le_rfl (d * K * δ)
    linarith
  -- Near the cylinder every leaf is `ℓ` plus `S₀ = struweShape δ K (d K δ)`.
  have hFδ (ℓ : ℝ) : F ℓ δ = ℓ + struweShape δ K (d * K * δ) δ := hFS ℓ δ (by nlinarith)
  have hcont {ℓ : ℝ} (hℓ : ℓ₀ ≤ ℓ) : ContDiffOn ℝ ∞ (F ℓ) (Ioi δ) := fun r hr ↦
    ((hFs (ℓ, r) ⟨hℓ, hr⟩).comp r (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt
  have hcontI {ℓ : ℝ} (hℓ : ℓ₀ ≤ ℓ) : ContinuousOn (F ℓ) (Ici δ) := by
    refine continuousOn_Ici_of_eqOn_struweShape hδ (K := K) (c := ℓ + d * K * δ) (by linarith)
      (hcont hℓ).continuousOn (show δ < 3 * K * δ / 4 by nlinarith) fun r hr ↦ ?_
    rw [hFS ℓ r hr.2.le, struweShape_add]
  have hstd {ℓ : ℝ} (hℓ : ℓ₀ ≤ ℓ) {r : ℝ} (hr : ℓ * γ' ≤ r) :
      F ℓ r = √(64 * r ^ 2 + ℓ ^ 2) := by
    have : ℓ₀ * γ' ≤ ℓ * γ' := mul_le_mul_of_nonneg_right hℓ hγ'₀.le
    rw [hFφ ℓ hℓ r (by linarith), hφS ℓ (by linarith) r hr, add_comm]
  -- A bound of `∂F/∂r` on a compact set inside `[ℓ₀, ∞) × (δ, ∞)`.
  have hd : ContinuousOn (fun q : ℝ × ℝ ↦ iteratedDeriv 1 (fun y ↦ Function.uncurry F (q.1, y)) q.2)
      (Icc ℓ₀ (2 * ℓ₀) ×ˢ Icc (3 * δ) (2 * ℓ₀ / 4)) := fun q hq ↦ by
    have hq₂ : δ < q.2 := by linarith [hq.2.1]
    exact ((hFs q ⟨hq.1.1, hq₂⟩).continuousAt_iteratedDeriv_prod_right
      (by exact_mod_cast le_top)).continuousWithinAt
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hd
  refine ⟨F, max 8 B, le_max_left _ _, hFs, fun ℓ hℓ ↦ hcont hℓ, hFc, hFm, fun ℓ ↦ ?_, hFt,
    fun ℓ hℓ ↦ hcontI hℓ, fun ℓ hℓ r hr ↦ ?_, fun ℓ hℓ r hr ↦ hstd hℓ hr,
    fun ℓ hℓ r hr ↦ hstd hℓ ?_, fun ℓ hℓ r hr ↦ ?_, ?_, ?_⟩
  · -- All Struwe shapes at `δ` differ by constants.
    refine ⟨ℓ + struweShape δ K (d * K * δ) (4 * δ), fun r hr ↦ ?_⟩
    rw [hFS ℓ r (by nlinarith [hr.2]), struweShape_eq_struweShape_apply_mul hδ (by linarith)
      (by norm_num : (1 : ℝ) ≤ 4) _ hr.1, ← add_zero (struweShape δ K (d * K * δ) (4 * δ)),
      struweShape_add, add_zero, add_assoc]
  · have h := hFδ ℓ
    rcases hr.eq_or_lt with rfl | hr
    · nlinarith
    · have := strictMonoOn_Ici_of_isConvexShapeAt (hcontI hℓ) (hFc ℓ hℓ) self_mem_Ici
        (mem_Ici.2 hr.le) hr
      nlinarith
  · have : 0 ≤ ℓ := by linarith
    nlinarith
  · have hle := hB (ℓ, r) ⟨hℓ, hr.1, by linarith [hr.2, hℓ.2]⟩
    rw [Real.norm_eq_abs] at hle
    simp only [Function.uncurry_apply_pair, iteratedDeriv_one] at hle
    exact hle.trans (le_max_right _ _)
  · have h := hFδ 1
    nlinarith
  · -- `S₀ δ < S₀ (K δ) = d K δ < 3 K δ / 2 ≤ ℓ₀ γ' ≤ γ / 2`.
    have hlt := strictMonoOn_struweShape hδ (K := K) (by linarith) (d * K * δ) self_mem_Ici
      (mem_Ici.2 (by nlinarith : δ ≤ K * δ)) (by nlinarith)
    rw [struweShape_apply_mul] at hlt
    have h := hFδ 1
    have : ℓ₀ ≤ 1 / 2 := by rw [hℓ₀]; linarith
    have : ℓ₀ * γ' ≤ γ' / 2 := by nlinarith
    nlinarith

/-! ### The explicit leaves below the cone -/

/-- The leaf `ℓ` of the explicit family of `i`-convex shapes over the cylinder of radius `δ`,
with a cutoff of width `L δ` starting at `2 δ`: the cutoff leaf with `b = (ℓ + 8 δ) / 64` and
`c = 64 δ² - ℓ²`, that is, with `h r = smoothTransition ((r - 2 δ) / (L δ))`,
`r ↦ (ℓ + 8 δ) / 64 (1 - h r) + √(64 (r² - δ²) + (64 δ² - ℓ²) h r)`. It is the bottom leaf
`√(64 r² - 64 δ²)` raised by `(ℓ + 8 δ) / 64` for `r ≤ 2 δ` (when `L, δ ≥ 0`), and, when
`L, δ > 0`, `√(64 r² - ℓ²)` for `r ≥ (2 + L) δ`, the standard shape when `ℓ ≤ 0`. -/
noncomputable def sqrtSubLeaf (L δ ℓ r : ℝ) : ℝ :=
  cutoffLeaf L δ ((ℓ + 8 * δ) / 64) (64 * δ ^ 2 - ℓ ^ 2) r

/-- `sqrtSubLeaf` is the cutoff leaf with `b = (ℓ + 8 δ) / 64` and `c = 64 δ² - ℓ²`. -/
theorem sqrtSubLeaf_eq_cutoffLeaf (L δ ℓ : ℝ) :
    sqrtSubLeaf L δ ℓ = cutoffLeaf L δ ((ℓ + 8 * δ) / 64) (64 * δ ^ 2 - ℓ ^ 2) :=
  (rfl)

theorem sqrtSubLeaf_def (L δ ℓ r : ℝ) : sqrtSubLeaf L δ ℓ r =
    (ℓ + 8 * δ) / 64 * (1 - smoothTransition ((r - 2 * δ) / (L * δ))) +
      √(64 * (r ^ 2 - δ ^ 2) + (64 * δ ^ 2 - ℓ ^ 2) * smoothTransition ((r - 2 * δ) / (L * δ))) :=
  by rw [sqrtSubLeaf_eq_cutoffLeaf, cutoffLeaf_def]

/-- The leaves for the radius `δ` are those for the radius `1`, rescaled by `δ`. -/
theorem sqrtSubLeaf_eq_mul_sqrtSubLeaf_one (hδ : 0 < δ) (L ℓ : ℝ) :
    sqrtSubLeaf L δ ℓ = fun r ↦ δ * sqrtSubLeaf L 1 (ℓ / δ) (r / δ) := by
  rw [sqrtSubLeaf_eq_cutoffLeaf, cutoffLeaf_eq_mul_cutoffLeaf_one hδ, sqrtSubLeaf_eq_cutoffLeaf]
  ext r
  congr 2 <;> field_simp

/-- Up to `2 δ`, the leaf `ℓ` is the bottom leaf `√(64 r² - 64 δ²)` raised by `(ℓ + 8 δ) / 64`. -/
theorem sqrtSubLeaf_of_le {L ℓ r : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ) (hr : r ≤ 2 * δ) :
    sqrtSubLeaf L δ ℓ r = √(64 * r ^ 2 - 64 * δ ^ 2) + (ℓ + 8 * δ) / 64 := by
  rw [sqrtSubLeaf_eq_cutoffLeaf, cutoffLeaf_of_le hL hδ hr]

/-- From `(2 + L) δ` on, the leaf `ℓ` is `√(64 r² - ℓ²)`, the standard shape when `ℓ ≤ 0`. -/
theorem sqrtSubLeaf_of_ge {L ℓ r : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hr : (2 + L) * δ ≤ r) :
    sqrtSubLeaf L δ ℓ r = √(64 * r ^ 2 - ℓ ^ 2) := by
  rw [sqrtSubLeaf_eq_cutoffLeaf, cutoffLeaf_of_ge hL hδ hr]
  ring_nf

/-- The radicand of the leaf `ℓ` is positive at each `r` with `δ² < r²` and `ℓ² < 64 r²`: it is
`64 (r² - δ²) (1 - H) + (64 r² - ℓ²) H` for the cutoff `H ∈ [0, 1]`, a convex combination of two
positive numbers. -/
theorem sqrtSubLeaf_radicand_pos (L : ℝ) {ℓ r : ℝ} (hr : δ ^ 2 < r ^ 2)
    (hℓ : ℓ ^ 2 < 64 * r ^ 2) :
    0 < 64 * (r ^ 2 - δ ^ 2) +
      (64 * δ ^ 2 - ℓ ^ 2) * smoothTransition ((r - 2 * δ) / (L * δ)) :=
  cutoffLeaf_radicand_pos L hr (by linarith)

/-- **The explicit leaves below the cone are `i`-convex shapes.** There is `L₀ ≥ 1` such that for
every `L ≥ L₀`, `δ > 0` and `ℓ ∈ [-8 δ, 0]`, the leaf `sqrtSubLeaf L δ ℓ` is an `i`-convex shape
at every `r > δ`. -/
theorem exists_isConvexShapeAt_sqrtSubLeaf :
    ∃ L₀, 1 ≤ L₀ ∧ ∀ L, L₀ ≤ L → ∀ δ, 0 < δ → ∀ ℓ ∈ Icc (-8 * δ) 0, ∀ r, δ < r →
      IsConvexShapeAt (sqrtSubLeaf L δ ℓ) r := by
  obtain ⟨L₀, hL₀, h⟩ := exists_isConvexShapeAt_cutoffLeaf
  refine ⟨L₀, hL₀, fun L hL δ hδ ℓ ⟨hℓ₀, hℓ₁⟩ r hr ↦ ?_⟩
  -- The coefficients are `(ℓ + 8 δ) / 64 ≤ δ / 8` and `64 δ² - ℓ² ≤ 64 δ²`.
  exact h L hL δ hδ _ ⟨by linarith, by linarith⟩ _ ⟨by nlinarith, by nlinarith⟩ r hr

/-- The bottom leaf: the leaf `-8 δ` is `√(64 r² - 64 δ²)` at every `r`. -/
theorem sqrtSubLeaf_neg_eight_mul (L δ r : ℝ) :
    sqrtSubLeaf L δ (-8 * δ) r = √(64 * r ^ 2 - 64 * δ ^ 2) := by
  rw [sqrtSubLeaf_def]; ring_nf

/-- The leaf `0` of `sqrtAddLeaf` is the leaf `0` of `sqrtSubLeaf`: the leaves `ℓ ≥ 0` start
where the leaves `ℓ ≤ 0` end. -/
theorem sqrtAddLeaf_zero (L δ : ℝ) : sqrtAddLeaf L δ 0 = sqrtSubLeaf L δ 0 := by
  ext r
  rw [sqrtAddLeaf_def, sqrtSubLeaf_def]
  ring_nf

/-- The family `(ℓ, r) ↦ sqrtSubLeaf L δ ℓ r` is smooth where `δ < r` and `|ℓ| < 8 r`, for
`0 ≤ δ`: there the radicand is positive. -/
theorem contDiffOn_uncurry_sqrtSubLeaf (L : ℝ) (hδ : 0 ≤ δ) :
    ContDiffOn ℝ ∞ (Function.uncurry (sqrtSubLeaf L δ)) {p | δ < p.2 ∧ |p.1| < 8 * p.2} := by
  have e : Function.uncurry (sqrtSubLeaf L δ) =
      fun p : ℝ × ℝ ↦ cutoffLeaf L δ ((p.1 + 8 * δ) / 64) (64 * δ ^ 2 - p.1 ^ 2) p.2 := by
    ext ⟨ℓ, r⟩
    rw [Function.uncurry_apply_pair, sqrtSubLeaf_eq_cutoffLeaf]
  rintro ⟨ℓ, r⟩ ⟨hr, hℓ⟩
  dsimp only at hr hℓ
  have hrδ : δ ^ 2 < r ^ 2 := by gcongr
  have hℓr : ℓ ^ 2 < 64 * r ^ 2 := by
    have := sq_lt_sq' (by linarith [abs_nonneg ℓ]) hℓ
    rw [sq_abs] at this
    linarith
  have hrad := sqrtSubLeaf_radicand_pos L hrδ hℓr
  rw [e]
  exact (((contDiffAt_fst.add contDiffAt_const).div_const 64).cutoffLeaf
    (contDiffAt_const.sub (contDiffAt_fst.pow 2)) contDiffAt_snd hrad.ne').contDiffWithinAt

/-- The domain `δ < r`, `|ℓ| < 8 r` of `contDiffOn_uncurry_sqrtSubLeaf` is open. -/
theorem isOpen_setOf_lt_snd_and_abs_fst_lt (δ : ℝ) :
    IsOpen {p : ℝ × ℝ | δ < p.2 ∧ |p.1| < 8 * p.2} :=
  (isOpen_lt continuous_const continuous_snd).inter
    (isOpen_lt continuous_fst.abs (continuous_const.mul continuous_snd))

/-- The family `(ℓ, r) ↦ sqrtSubLeaf L δ ℓ r` is smooth at every `(ℓ, r)` with `δ < r` and
`|ℓ| < 8 r`, for `0 ≤ δ`. -/
theorem contDiffAt_uncurry_sqrtSubLeaf (L : ℝ) (hδ : 0 ≤ δ) {q : ℝ × ℝ}
    (hq : δ < q.2 ∧ |q.1| < 8 * q.2) :
    ContDiffAt ℝ ∞ (Function.uncurry (sqrtSubLeaf L δ)) q :=
  (contDiffOn_uncurry_sqrtSubLeaf L hδ).contDiffAt
    ((isOpen_setOf_lt_snd_and_abs_fst_lt δ).mem_nhds hq)

/-- Each leaf `sqrtSubLeaf L δ ℓ` is continuous. -/
theorem continuous_sqrtSubLeaf (L δ ℓ : ℝ) : Continuous (sqrtSubLeaf L δ ℓ) := by
  rw [sqrtSubLeaf_eq_cutoffLeaf]
  exact continuous_cutoffLeaf _ _ _ _

/-- For `0 ≤ δ` and `|ℓ| ≤ 8 δ`, the leaf `sqrtSubLeaf L δ ℓ` is `Cⁿ` on `(δ, ∞)`. -/
theorem contDiffOn_sqrtSubLeaf {n : ℕ∞} (L : ℝ) (hδ : 0 ≤ δ) {ℓ : ℝ} (hℓ : |ℓ| ≤ 8 * δ) :
    ContDiffOn ℝ n (sqrtSubLeaf L δ ℓ) (Ioi δ) := fun r hr ↦
  ((contDiffAt_uncurry_sqrtSubLeaf L hδ (q := (ℓ, r))
    ⟨hr, by dsimp only; linarith [mem_Ioi.1 hr]⟩).uncurry_left.of_le
      (by exact_mod_cast le_top)).contDiffWithinAt

/-- The slope of every leaf tends to `+∞` at `δ`, where the leaves meet the cylinder. -/
theorem tendsto_deriv_sqrtSubLeaf {L : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ) (ℓ : ℝ) :
    Tendsto (deriv (sqrtSubLeaf L δ ℓ)) (𝓝[>] δ) atTop := by
  rw [sqrtSubLeaf_eq_cutoffLeaf]
  exact tendsto_deriv_cutoffLeaf hL hδ _ _

/-- For `0 ≤ δ`, at each `r > δ`, the leaves `ℓ ∈ [-8 δ, 0]` are strictly increasing in `ℓ`:
both terms of `sqrtSubLeaf` are nondecreasing in `ℓ ≤ 0`, the first strictly where the cutoff
is below `1` and the second where it is positive. -/
theorem strictMonoOn_sqrtSubLeaf (L : ℝ) (hδ : 0 ≤ δ) {r : ℝ} (hr : δ < r) :
    StrictMonoOn (fun ℓ ↦ sqrtSubLeaf L δ ℓ r) (Icc (-8 * δ) 0) := by
  intro ℓ₁ hℓ₁ ℓ₂ hℓ₂ h
  simp only [sqrtSubLeaf_eq_cutoffLeaf]
  exact cutoffLeaf_lt_cutoffLeaf (by linarith) (by nlinarith [hℓ₂.2])
    (by nlinarith [hℓ₁.1, hℓ₁.2]) (by gcongr)

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
  · refine (isOpen_setOf_lt_snd_and_abs_fst_lt δ).mem_nhdsSet.2 ?_
    rintro ⟨ℓ, r⟩ ⟨hℓ, hr⟩
    rw [mem_Ioi] at hr
    exact ⟨hr, (abs_of_nonpos hℓ.2).trans_lt (by linarith [hℓ.1])⟩
  · rw [sqrtSubLeaf_of_le (by linarith) hδ.le hr.2, add_comm]
  · rw [sqrtSubLeaf_of_ge (by linarith) hδ hr, abs_of_nonpos hℓ.2]
    ring_nf

/-! ### The glued family over the cylinder -/

/-- **The glued family over the cylinder of radius `δ`** (Cieliebak–Eliashberg, Proposition 4.27),
for a cutoff parameter `L`, the parameters `ℓ₀` and `M` of the bridge family and a family `F` of
leaves beyond `2 ℓ₀`. Its leaf `ℓ` is
* `sqrtSubLeaf L δ ℓ` for `ℓ ≤ 0`;
* `struweSwitchLeaf L δ ℓ` for `0 < ℓ ≤ 7 δ`;
* the leaf `ℓ` of `bridgeFamily L δ ℓ₀ M F` for `7 δ < ℓ ≤ 2 ℓ₀`;
* `F ℓ` for `2 ℓ₀ < ℓ`. -/
noncomputable def surroundFamily (L δ ℓ₀ M : ℝ) (F : ℝ → ℝ → ℝ) (ℓ : ℝ) : ℝ → ℝ :=
  if ℓ ≤ 0 then sqrtSubLeaf L δ ℓ
  else if ℓ ≤ 7 * δ then struweSwitchLeaf L δ ℓ
  else if ℓ ≤ 2 * ℓ₀ then bridgeFamily L δ ℓ₀ M F ℓ
  else F ℓ

theorem surroundFamily_def (L δ ℓ₀ M : ℝ) (F : ℝ → ℝ → ℝ) (ℓ : ℝ) :
    surroundFamily L δ ℓ₀ M F ℓ =
      if ℓ ≤ 0 then sqrtSubLeaf L δ ℓ
      else if ℓ ≤ 7 * δ then struweSwitchLeaf L δ ℓ
      else if ℓ ≤ 2 * ℓ₀ then bridgeFamily L δ ℓ₀ M F ℓ
      else F ℓ :=
  (rfl)

section surroundFamily

variable {L ℓ₀ M ℓ : ℝ} {F : ℝ → ℝ → ℝ}

/-- The leaves `ℓ ≤ 0` of the glued family are the leaves `sqrtSubLeaf L δ ℓ`. -/
theorem surroundFamily_of_nonpos (hℓ : ℓ ≤ 0) :
    surroundFamily L δ ℓ₀ M F ℓ = sqrtSubLeaf L δ ℓ := by
  rw [surroundFamily_def, ite_eq_left hℓ]

/-- The leaves `0 < ℓ ≤ 7 δ` of the glued family are the Struwe switch leaves. -/
theorem surroundFamily_of_pos_of_le (hℓ₁ : 0 < ℓ) (hℓ₂ : ℓ ≤ 7 * δ) :
    surroundFamily L δ ℓ₀ M F ℓ = struweSwitchLeaf L δ ℓ := by
  rw [surroundFamily_def, ite_eq_right hℓ₁.not_ge, ite_eq_left hℓ₂]

/-- The leaves `7 δ < ℓ ≤ 2 ℓ₀` of the glued family, for `0 ≤ δ`, are those of the bridge
family. -/
theorem surroundFamily_of_lt_of_le (hδ : 0 ≤ δ) (hℓ₁ : 7 * δ < ℓ) (hℓ₂ : ℓ ≤ 2 * ℓ₀) :
    surroundFamily L δ ℓ₀ M F ℓ = bridgeFamily L δ ℓ₀ M F ℓ := by
  rw [surroundFamily_def, ite_eq_right (by linarith), ite_eq_right hℓ₁.not_ge, ite_eq_left hℓ₂]

/-- The leaves `ℓ > max (7 δ) (2 ℓ₀)` of the glued family, for `0 ≤ δ`, are the leaves `F ℓ`. -/
theorem surroundFamily_of_lt (hδ : 0 ≤ δ) (hℓ₁ : 7 * δ < ℓ) (hℓ₂ : 2 * ℓ₀ < ℓ) :
    surroundFamily L δ ℓ₀ M F ℓ = F ℓ := by
  rw [surroundFamily_def, ite_eq_right (by linarith), ite_eq_right hℓ₁.not_ge,
    ite_eq_right hℓ₂.not_ge]

/-- For `0 ≤ δ`, the leaves `ℓ ∈ [0, 7 δ]` of the glued family are the Struwe switch leaves: at
`ℓ = 0` the leaf `sqrtSubLeaf L δ 0` is `sqrtAddLeaf L δ 0`, which is
`struweSwitchLeaf L δ 0`. -/
theorem surroundFamily_eq_struweSwitchLeaf (hδ : 0 ≤ δ) (hℓ : ℓ ∈ Icc 0 (7 * δ)) :
    surroundFamily L δ ℓ₀ M F ℓ = struweSwitchLeaf L δ ℓ := by
  rcases hℓ.1.eq_or_lt with rfl | hℓ₀
  · rw [surroundFamily_of_nonpos le_rfl, ← sqrtAddLeaf_zero, struweSwitchLeaf_of_le (by linarith)]
  · exact surroundFamily_of_pos_of_le hℓ₀ hℓ.2

/-- For `0 < δ`, the leaves `ℓ ∈ [7 δ, 2 ℓ₀]` of the glued family are those of the bridge family
on `(δ, ∞)`: at `ℓ = 7 δ` by `SymplecticGeometry.bridgeFamily_seven_mul_eqOn`. -/
theorem surroundFamily_eqOn_bridgeFamily (hδ : 0 < δ) (hℓ : ℓ ∈ Icc (7 * δ) (2 * ℓ₀)) :
    EqOn (surroundFamily L δ ℓ₀ M F ℓ) (bridgeFamily L δ ℓ₀ M F ℓ) (Ioi δ) := by
  rcases hℓ.1.eq_or_lt with rfl | h7
  · rw [surroundFamily_eq_struweSwitchLeaf hδ.le ⟨by linarith, le_rfl⟩]
    exact (bridgeFamily_seven_mul_eqOn L hδ ℓ₀ M F).symm
  · rw [surroundFamily_of_lt_of_le hδ.le h7 hℓ.2]
    exact eqOn_refl _ _

/-- For `0 < δ`, `24 δ ≤ ℓ₀` and `0 ≤ M`, the leaves `ℓ ≥ 2 ℓ₀` of the glued family are the
leaves `F ℓ` on `(δ, ∞)`, once `F (2 ℓ₀) ≥ 2 ℓ₀` on `(δ, ∞)` and `F (2 ℓ₀)` is the standard
leaf `r ↦ √(64 r² + (2 ℓ₀)²)` from `2 ℓ₀ / 4` on: at `ℓ = 2 ℓ₀` by
`SymplecticGeometry.bridgeFamily_two_mul_eqOn`. -/
theorem surroundFamily_eqOn_of_ge (hδ : 0 < δ) (hℓ₀ : 24 * δ ≤ ℓ₀) (hM : 0 ≤ M)
    (hFℓ : ∀ r, δ < r → 2 * ℓ₀ ≤ F (2 * ℓ₀) r)
    (hFs : ∀ r, 2 * ℓ₀ / 4 ≤ r → F (2 * ℓ₀) r = √(64 * r ^ 2 + (2 * ℓ₀) ^ 2))
    (hℓ : 2 * ℓ₀ ≤ ℓ) : EqOn (surroundFamily L δ ℓ₀ M F ℓ) (F ℓ) (Ioi δ) := by
  rcases hℓ.eq_or_lt with rfl | h
  · rw [surroundFamily_of_lt_of_le hδ.le (by linarith) le_rfl]
    exact bridgeFamily_two_mul_eqOn L hδ hℓ₀ hM hFℓ hFs
  · rw [surroundFamily_of_lt hδ.le (by linarith) h]
    exact eqOn_refl _ _

/-- The bottom leaf of the glued family: for `0 ≤ δ`, the leaf `-8 δ` is `√(64 r² - 64 δ²)`. -/
theorem surroundFamily_neg_eight_mul (hδ : 0 ≤ δ) (r : ℝ) :
    surroundFamily L δ ℓ₀ M F (-8 * δ) r = √(64 * r ^ 2 - 64 * δ ^ 2) := by
  rw [surroundFamily_of_nonpos (by linarith), sqrtSubLeaf_neg_eight_mul]

/-- **The leaves of the glued family are `i`-convex shapes.** Let `δ > 0`, `24 δ ≤ ℓ₀ ≤ ℓₜ / 2`
and `M ≥ 8`, let `L ≥ 1` be large compared with bounds `A` of `smoothTransition'`, `B` of
`smoothTransition''` and `N` of `x smoothTransition'' x`, let every `F ℓ`, `ℓ ∈ [ℓ₀, ℓₜ]`, be an
`i`-convex shape at every `r > δ`, `C²` on `(δ, ∞)` and a constant plus `struweShape δ 4 0` on
`[δ, 9 δ / 2]`, and let every `F ℓ`, `ℓ ∈ [ℓ₀, 2 ℓ₀]`, be at least `ℓ` on `(δ, ∞)`, the standard
leaf `r ↦ √(64 r² + ℓ²)` from `ℓ / 4` on, and of slope at most `M` in absolute value on
`[3 δ, ℓ / 4]`. Then for `ℓ ∈ [-8 δ, ℓₜ]` the leaf `ℓ` of the glued family is an `i`-convex
shape at every `r > δ`. -/
theorem isConvexShapeAt_surroundFamily {A B N ℓₜ r : ℝ}
    (hA : ∀ x, |deriv smoothTransition x| ≤ A)
    (hB : ∀ x, |deriv (deriv smoothTransition) x| ≤ B)
    (hN : ∀ x, |x * deriv (deriv smoothTransition) x| ≤ N)
    (hL₁ : 1 ≤ L) (hL : 1024 * (A + 2 * B + N) ≤ L) (hδ : 0 < δ) (hℓ₀ : 24 * δ ≤ ℓ₀)
    (hM : 8 ≤ M) (hℓₜ : 2 * ℓ₀ ≤ ℓₜ)
    (hFc : ∀ ℓ ∈ Icc ℓ₀ ℓₜ, ∀ r, δ < r → IsConvexShapeAt (F ℓ) r)
    (hF2 : ∀ ℓ ∈ Icc ℓ₀ ℓₜ, ContDiffOn ℝ 2 (F ℓ) (Ioi δ))
    (hFS : ∀ ℓ ∈ Icc ℓ₀ ℓₜ, ∃ c, ∀ r ∈ Icc δ (9 * δ / 2), F ℓ r = c + struweShape δ 4 0 r)
    (hFℓ : ∀ ℓ ∈ Icc ℓ₀ (2 * ℓ₀), ∀ r, δ < r → ℓ ≤ F ℓ r)
    (hFs : ∀ ℓ ∈ Icc ℓ₀ (2 * ℓ₀), ∀ r, ℓ / 4 ≤ r → F ℓ r = √(64 * r ^ 2 + ℓ ^ 2))
    (hFd : ∀ ℓ ∈ Icc ℓ₀ (2 * ℓ₀), ∀ r ∈ Icc (3 * δ) (ℓ / 4), |deriv (F ℓ) r| ≤ M)
    (hℓ : ℓ ∈ Icc (-8 * δ) ℓₜ) (hr : δ < r) :
    IsConvexShapeAt (surroundFamily L δ ℓ₀ M F ℓ) r := by
  obtain ⟨hℓ₁, hℓ₂⟩ := hℓ
  have hsub : Icc ℓ₀ (2 * ℓ₀) ⊆ Icc ℓ₀ ℓₜ := Icc_subset_Icc_right hℓₜ
  rcases le_or_gt ℓ 0 with h0 | h0
  · -- The cutoff leaf with `b = (ℓ + 8 δ) / 64 ∈ [0, δ / 8]` and `c = 64 δ² - ℓ² ∈ [0, 64 δ²]`.
    rw [surroundFamily_of_nonpos h0, sqrtSubLeaf_eq_cutoffLeaf]
    exact isConvexShapeAt_cutoffLeaf hA hB hN hL₁ hL hδ (by linarith) (by linarith)
      (by nlinarith) (by nlinarith) hr
  rcases le_or_gt ℓ (7 * δ) with h7 | h7
  · rw [surroundFamily_of_pos_of_le h0 h7]
    exact isConvexShapeAt_struweSwitchLeaf hA hB hN hL₁ hL hδ ⟨h0.le, h7⟩ hr
  rcases le_or_gt ℓ (2 * ℓ₀) with h2 | h2
  · rw [surroundFamily_of_lt_of_le hδ.le h7 h2]
    exact isConvexShapeAt_bridgeFamily hA hB hN hL₁ hL hδ hℓ₀ hM (fun ℓ h ↦ hFc ℓ (hsub h))
      (fun ℓ h ↦ hF2 ℓ (hsub h))
      (fun ℓ h ↦ (hFS ℓ (hsub h)).imp fun _ hc r hr ↦ hc r ⟨hr.1.le, hr.2⟩)
      hFℓ hFs hFd ⟨h7.le, h2⟩ hr
  · rw [surroundFamily_of_lt hδ.le h7 h2]
    exact hFc ℓ ⟨by linarith, hℓ₂⟩ r hr

/-- **The leaves of the glued family are `Cⁿ`.** For `0 ≤ L`, `0 < δ` and `2 ℓ₀ ≤ ℓₜ`, if
every `F ℓ`, `ℓ ∈ [ℓ₀, ℓₜ]`, is `Cⁿ` on `(δ, ∞)`, then so is each leaf `ℓ ∈ [-8 δ, ℓₜ]` of the
glued family. -/
theorem contDiffOn_surroundFamily {n : ℕ∞} {ℓₜ : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ)
    (hℓₜ : 2 * ℓ₀ ≤ ℓₜ) (hF : ∀ ℓ ∈ Icc ℓ₀ ℓₜ, ContDiffOn ℝ n (F ℓ) (Ioi δ))
    (hℓ : ℓ ∈ Icc (-8 * δ) ℓₜ) : ContDiffOn ℝ n (surroundFamily L δ ℓ₀ M F ℓ) (Ioi δ) := by
  obtain ⟨hℓ₁, hℓ₂⟩ := hℓ
  rcases le_or_gt ℓ 0 with h0 | h0
  · rw [surroundFamily_of_nonpos h0]
    exact contDiffOn_sqrtSubLeaf L hδ.le (by rw [abs_of_nonpos h0]; linarith)
  rcases le_or_gt ℓ (7 * δ) with h7 | h7
  · rw [surroundFamily_of_pos_of_le h0 h7]
    exact contDiffOn_struweSwitchLeaf hL hδ ℓ
  rcases le_or_gt ℓ (2 * ℓ₀) with h2 | h2
  · rw [surroundFamily_of_lt_of_le hδ.le h7 h2]
    exact contDiffOn_bridgeFamily hδ (fun ℓ h ↦ hF ℓ (Icc_subset_Icc_right hℓₜ h)) h2
  · rw [surroundFamily_of_lt hδ.le h7 h2]
    exact hF ℓ ⟨by linarith, hℓ₂⟩

/-- **The leaves of the glued family are continuous up to the cylinder.** Let `0 ≤ L`, `0 < δ`,
`15 δ / 2 < ℓ₀`, `0 ≤ M` and `2 ℓ₀ ≤ ℓₜ`, and let every `F ℓ`, `ℓ ∈ [ℓ₀, ℓₜ]`, be continuous on
`(δ, ∞)` and a constant plus `struweShape δ 4 0` on `[δ, 9 δ / 2]`. Then each leaf `ℓ ≤ ℓₜ` of
the glued family is continuous on `[δ, ∞)`. -/
theorem continuousOn_surroundFamily {ℓₜ : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ)
    (hℓ₀ : 15 * δ / 2 < ℓ₀) (hM : 0 ≤ M) (hℓₜ : 2 * ℓ₀ ≤ ℓₜ)
    (hFS : ∀ ℓ ∈ Icc ℓ₀ ℓₜ, ∃ c, ∀ r ∈ Icc δ (9 * δ / 2), F ℓ r = c + struweShape δ 4 0 r)
    (hFc : ∀ ℓ ∈ Icc ℓ₀ ℓₜ, ContinuousOn (F ℓ) (Ioi δ)) (hℓ : ℓ ≤ ℓₜ) :
    ContinuousOn (surroundFamily L δ ℓ₀ M F ℓ) (Ici δ) := by
  have hsub : Icc ℓ₀ (2 * ℓ₀) ⊆ Icc ℓ₀ ℓₜ := Icc_subset_Icc_right hℓₜ
  rcases le_or_gt ℓ 0 with h0 | h0
  · rw [surroundFamily_of_nonpos h0]
    exact (continuous_sqrtSubLeaf L δ ℓ).continuousOn
  rcases le_or_gt ℓ (7 * δ) with h7 | h7
  · rw [surroundFamily_of_pos_of_le h0 h7]
    exact continuousOn_struweSwitchLeaf L hδ ℓ
  rcases le_or_gt ℓ (2 * ℓ₀) with h2 | h2
  · rw [surroundFamily_of_lt_of_le hδ.le h7 h2]
    exact continuousOn_bridgeFamily hL hδ hℓ₀ hM (fun ℓ h ↦ hFS ℓ (hsub h))
      (fun ℓ h ↦ hFc ℓ (hsub h)) ⟨h0.le, h2⟩
  · -- Near the cylinder `F ℓ` is a Struwe shape.
    rw [surroundFamily_of_lt hδ.le h7 h2]
    have hmem : ℓ ∈ Icc ℓ₀ ℓₜ := ⟨by linarith, hℓ⟩
    obtain ⟨c, hc⟩ := hFS ℓ hmem
    exact continuousOn_Ici_of_eqOn_struweShape hδ (K := 4) (by norm_num) (hFc ℓ hmem)
      (by linarith : δ < 9 * δ / 2) fun r hr ↦ by
        rw [hc r ⟨hr.1, hr.2.le⟩, ← struweShape_add, add_zero]

/-- **The leaves of the glued family meet the cylinder vertically.** Let `0 ≤ L`, `0 < δ`,
`15 δ / 2 < ℓ₀`, `0 ≤ M` and `2 ℓ₀ ≤ ℓₜ`, and let every `F ℓ`, `ℓ ∈ [ℓ₀, ℓₜ]`, be a constant
plus `struweShape δ 4 0` on `[δ, 9 δ / 2]`. Then the slope of each leaf `ℓ ≤ ℓₜ` of the glued
family tends to `+∞` at `δ`. -/
theorem tendsto_deriv_surroundFamily {ℓₜ : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ)
    (hℓ₀ : 15 * δ / 2 < ℓ₀) (hM : 0 ≤ M) (hℓₜ : 2 * ℓ₀ ≤ ℓₜ)
    (hFS : ∀ ℓ ∈ Icc ℓ₀ ℓₜ, ∃ c, ∀ r ∈ Icc δ (9 * δ / 2), F ℓ r = c + struweShape δ 4 0 r)
    (hℓ : ℓ ≤ ℓₜ) : Tendsto (deriv (surroundFamily L δ ℓ₀ M F ℓ)) (𝓝[>] δ) atTop := by
  rcases le_or_gt ℓ 0 with h0 | h0
  · rw [surroundFamily_of_nonpos h0]
    exact tendsto_deriv_sqrtSubLeaf hL hδ ℓ
  rcases le_or_gt ℓ (7 * δ) with h7 | h7
  · rw [surroundFamily_of_pos_of_le h0 h7]
    exact tendsto_deriv_struweSwitchLeaf hL hδ ℓ
  rcases le_or_gt ℓ (2 * ℓ₀) with h2 | h2
  · rw [surroundFamily_of_lt_of_le hδ.le h7 h2]
    exact tendsto_deriv_bridgeFamily hL hδ hℓ₀ hM
      (fun ℓ h ↦ hFS ℓ (Icc_subset_Icc_right hℓₜ h)) ⟨h0.le, h2⟩
  · -- Near the cylinder `F ℓ` is a Struwe shape.
    rw [surroundFamily_of_lt hδ.le h7 h2]
    obtain ⟨c, hc⟩ := hFS ℓ ⟨by linarith, hℓ⟩
    exact tendsto_deriv_of_eqOn_struweShape hδ (K := 4) (by norm_num)
      (by linarith : δ < 9 * δ / 2)
      fun r hr ↦ by rw [hc r ⟨hr.1.le, hr.2.le⟩, ← struweShape_add, add_zero]

/-- **The leaves of the glued family are increasing.** Under the hypotheses of
`SymplecticGeometry.isConvexShapeAt_surroundFamily`, each leaf `ℓ ∈ [-8 δ, ℓₜ]` of the glued
family is strictly increasing on `[δ, ∞)`. -/
theorem strictMonoOn_surroundFamily {A B N ℓₜ : ℝ}
    (hA : ∀ x, |deriv smoothTransition x| ≤ A)
    (hB : ∀ x, |deriv (deriv smoothTransition) x| ≤ B)
    (hN : ∀ x, |x * deriv (deriv smoothTransition) x| ≤ N)
    (hL₁ : 1 ≤ L) (hL : 1024 * (A + 2 * B + N) ≤ L) (hδ : 0 < δ) (hℓ₀ : 24 * δ ≤ ℓ₀)
    (hM : 8 ≤ M) (hℓₜ : 2 * ℓ₀ ≤ ℓₜ)
    (hFc : ∀ ℓ ∈ Icc ℓ₀ ℓₜ, ∀ r, δ < r → IsConvexShapeAt (F ℓ) r)
    (hF2 : ∀ ℓ ∈ Icc ℓ₀ ℓₜ, ContDiffOn ℝ 2 (F ℓ) (Ioi δ))
    (hFS : ∀ ℓ ∈ Icc ℓ₀ ℓₜ, ∃ c, ∀ r ∈ Icc δ (9 * δ / 2), F ℓ r = c + struweShape δ 4 0 r)
    (hFℓ : ∀ ℓ ∈ Icc ℓ₀ (2 * ℓ₀), ∀ r, δ < r → ℓ ≤ F ℓ r)
    (hFs : ∀ ℓ ∈ Icc ℓ₀ (2 * ℓ₀), ∀ r, ℓ / 4 ≤ r → F ℓ r = √(64 * r ^ 2 + ℓ ^ 2))
    (hFd : ∀ ℓ ∈ Icc ℓ₀ (2 * ℓ₀), ∀ r ∈ Icc (3 * δ) (ℓ / 4), |deriv (F ℓ) r| ≤ M)
    (hℓ : ℓ ∈ Icc (-8 * δ) ℓₜ) : StrictMonoOn (surroundFamily L δ ℓ₀ M F ℓ) (Ici δ) :=
  strictMonoOn_Ici_of_isConvexShapeAt
    (continuousOn_surroundFamily (by linarith) hδ (by linarith) (by linarith) hℓₜ hFS
      (fun ℓ h ↦ (hF2 ℓ h).continuousOn) hℓ.2)
    fun _ hr ↦ isConvexShapeAt_surroundFamily hA hB hN hL₁ hL hδ hℓ₀ hM hℓₜ hFc hF2 hFS
      hFℓ hFs hFd hℓ hr

/-- **The glued family and its `r`-derivatives are jointly continuous.** Let `0 < L`, `0 < δ`,
`24 δ ≤ ℓ₀`, `0 ≤ M` and `2 ℓ₀ ≤ ℓₜ`, let `(ℓ, r) ↦ F ℓ r` be smooth at every point of
`[ℓ₀, ℓₜ] × (δ, ∞)`, let `F ℓ₀` be an `i`-convex shape at every `r > δ` and the standard leaf
`r ↦ √(64 r² + ℓ₀²)` from `ℓ₀ / 4` on, and let `F (2 ℓ₀)` be at least `2 ℓ₀` on `(δ, ∞)` and the
standard leaf from `2 ℓ₀ / 4` on. Then for every `k` the `k`-th `r`-derivative
`(ℓ, r) ↦ ∂ᵏχ/∂rᵏ (ℓ, r)` of the glued family `χ` is continuous on `[-8 δ, ℓₜ] × (δ, ∞)`. -/
theorem continuousOn_iteratedDeriv_surroundFamily {ℓₜ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hℓ₀ : 24 * δ ≤ ℓ₀) (hM : 0 ≤ M) (hℓₜ : 2 * ℓ₀ ≤ ℓₜ)
    (hF : ∀ q ∈ Icc ℓ₀ ℓₜ ×ˢ Ioi δ, ContDiffAt ℝ ∞ (Function.uncurry F) q)
    (hFc : ∀ r, δ < r → IsConvexShapeAt (F ℓ₀) r)
    (hFs : ∀ r, ℓ₀ / 4 ≤ r → F ℓ₀ r = √(64 * r ^ 2 + ℓ₀ ^ 2))
    (hFℓ : ∀ r, δ < r → 2 * ℓ₀ ≤ F (2 * ℓ₀) r)
    (hFs₂ : ∀ r, 2 * ℓ₀ / 4 ≤ r → F (2 * ℓ₀) r = √(64 * r ^ 2 + (2 * ℓ₀) ^ 2)) (k : ℕ) :
    ContinuousOn (fun q : ℝ × ℝ ↦ iteratedDeriv k (surroundFamily L δ ℓ₀ M F q.1) q.2)
      (Icc (-8 * δ) ℓₜ ×ˢ Ioi δ) := by
  -- On each closed piece of `ℓ`, the leaves agree on `(δ, ∞)` with a formula smooth in `(ℓ, r)`.
  have piece {a b : ℝ} (g : ℝ × ℝ → ℝ)
      (hG : ∀ ℓ ∈ Icc a b, EqOn (surroundFamily L δ ℓ₀ M F ℓ) (fun r ↦ g (ℓ, r)) (Ioi δ))
      (hg : ∀ q ∈ Icc a b ×ˢ Ioi δ, ContDiffAt ℝ ∞ g q) :
      ContinuousOn (fun q : ℝ × ℝ ↦ iteratedDeriv k (surroundFamily L δ ℓ₀ M F q.1) q.2)
        (Icc a b ×ˢ Ioi δ) :=
    continuousOn_iteratedDeriv_prod_right_of_eqOn isOpen_Ioi hG hg (by exact_mod_cast le_top)
  have glue {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
      (h₁ : ContinuousOn (fun q : ℝ × ℝ ↦ iteratedDeriv k (surroundFamily L δ ℓ₀ M F q.1) q.2)
        (Icc a b ×ˢ Ioi δ))
      (h₂ : ContinuousOn (fun q : ℝ × ℝ ↦ iteratedDeriv k (surroundFamily L δ ℓ₀ M F q.1) q.2)
        (Icc b c ×ˢ Ioi δ)) :
      ContinuousOn (fun q : ℝ × ℝ ↦ iteratedDeriv k (surroundFamily L δ ℓ₀ M F q.1) q.2)
        (Icc a c ×ˢ Ioi δ) := by
    rw [← Icc_union_Icc_eq_Icc hab hbc]
    exact h₁.union_prod_of_isClosed h₂ isClosed_Icc isClosed_Icc
  have hbridge {ℓ : ℝ} (hℓ₁ : 7 * δ ≤ ℓ) (hℓ₂ : ℓ ≤ 2 * ℓ₀) :=
    surroundFamily_eqOn_bridgeFamily (L := L) (M := M) (F := F) hδ ⟨hℓ₁, hℓ₂⟩
  -- The leaves `ℓ ≤ 0`.
  have h₁ := piece (a := -8 * δ) (b := 0) (Function.uncurry (sqrtSubLeaf L δ))
    (fun ℓ hℓ r _ ↦ by dsimp only; rw [surroundFamily_of_nonpos hℓ.2, Function.uncurry_apply_pair])
    fun q hq ↦ contDiffAt_uncurry_sqrtSubLeaf L hδ.le
      ⟨hq.2, abs_lt.2 ⟨by linarith [hq.1.1, mem_Ioi.1 hq.2], by linarith [hq.1.2, mem_Ioi.1 hq.2]⟩⟩
  -- The Struwe switch leaves.
  have h₂ := piece (a := 0) (b := 7 * δ) (Function.uncurry (struweSwitchLeaf L δ))
    (fun ℓ hℓ r _ ↦ by
      dsimp only; rw [surroundFamily_eq_struweSwitchLeaf hδ.le hℓ, Function.uncurry_apply_pair])
    fun q hq ↦ contDiffAt_uncurry_struweSwitchLeaf hL.le hδ hq.2
  -- The three stages of the bridge family.
  have h₃ := piece (a := 7 * δ) (b := 15 * δ / 2) _
    (fun ℓ hℓ ↦ (hbridge hℓ.1 (by linarith [hℓ.2])).trans
      (by rw [bridgeFamily_of_le hℓ.2]; exact eqOn_refl _ _))
    fun q hq ↦ contDiffAt_bridgeLeaf_sqrtAddLeaf L hδ ℓ₀ hq.2
  have h₄ := piece (a := 15 * δ / 2) (b := ℓ₀) _
    (fun ℓ hℓ ↦ (hbridge (by linarith [hℓ.1]) (by linarith [hℓ.2])).trans
      (bridgeFamily_eqOn_sqrt hL hδ M F hℓ))
    fun q hq ↦ contDiffAt_bridgeLeaf_sqrt L hδ ℓ₀ hM hq.2
  have h₅ := piece (a := ℓ₀) (b := 2 * ℓ₀) _
    (fun ℓ hℓ ↦ (hbridge (by linarith [hℓ.1]) hℓ.2).trans
      (bridgeFamily_eqOn_of_ge hL.le hδ (by linarith) hM hFc hFs hℓ.1))
    fun q hq ↦ contDiffAt_bridgeLeaf_bridgeWidth L hδ hM
      (hF q ⟨⟨hq.1.1, by linarith [hq.1.2]⟩, hq.2⟩) hq.2
  -- The leaves `F ℓ`.
  have h₆ := piece (a := 2 * ℓ₀) (b := ℓₜ) (Function.uncurry F)
    (fun ℓ hℓ r hr ↦ by
      dsimp only
      rw [surroundFamily_eqOn_of_ge hδ hℓ₀ hM hFℓ hFs₂ hℓ.1 hr, Function.uncurry_apply_pair])
    fun q hq ↦ hF q ⟨⟨by linarith [hq.1.1], hq.1.2⟩, hq.2⟩
  exact glue (by linarith) (by linarith) h₁ <| glue (by linarith) (by linarith) h₂ <|
    glue (by linarith) (by linarith) h₃ <| glue (by linarith) (by linarith) h₄ <|
    glue (by linarith) hℓₜ h₅ h₆

/-- **The low leaves of the glued family are standard far out.** For `L, δ > 0`, from `(2 + L) δ`
on, every leaf `ℓ ≤ 7 δ` of the glued family is the standard leaf `√(64 r² + ℓ |ℓ|)`, whatever
`ℓ₀`, `M` and `F` are. In particular the leaves near the bottom leaf `-8 δ`, on both sides of it,
are standard from `(2 + L) δ` on. -/
theorem surroundFamily_eq_sqrt_of_le (hL : 0 < L) (hδ : 0 < δ) (hℓ : ℓ ≤ 7 * δ) {r : ℝ}
    (hr : (2 + L) * δ ≤ r) : surroundFamily L δ ℓ₀ M F ℓ r = √(64 * r ^ 2 + ℓ * |ℓ|) := by
  rcases le_or_gt ℓ 0 with h0 | h0
  · rw [surroundFamily_of_nonpos h0, sqrtSubLeaf_of_ge hL hδ hr, abs_of_nonpos h0]
    ring_nf
  · rw [surroundFamily_of_pos_of_le h0 hℓ, struweSwitchLeaf_of_ge hL hδ ⟨h0.le, hℓ⟩ hr,
      abs_of_pos h0, ← sq]

/-- **The far part of the glued family is standard.** Let `L, δ > 0`, `15 δ / 2 < ℓ₀`, `M ≥ 0`,
`2 ℓ₀ ≤ ℓₜ` and `t₁ = bridgeHeight L δ ℓ₀`, and let every `F ℓ`, `ℓ ∈ [ℓ₀, ℓₜ]`, be the
standard leaf `r ↦ √(64 r² + ℓ²)` from `R` on. Then for `ℓ ≤ ℓₜ` and
`r ≥ max R ((t₁ + 2 δ) / 6)` the leaf `ℓ` of the glued family is `√(64 r² + ℓ |ℓ|)` at `r`.
(The cutoff region `r < (2 + L) δ` of the leaves `ℓ ≤ 7 δ` ends below `(t₁ + 2 δ) / 6`.) -/
theorem surroundFamily_eq_sqrt {R ℓₜ r : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hℓ₀ : 15 * δ / 2 < ℓ₀)
    (hM : 0 ≤ M) (hℓₜ : 2 * ℓ₀ ≤ ℓₜ)
    (hFs : ∀ ℓ ∈ Icc ℓ₀ ℓₜ, ∀ r, R ≤ r → F ℓ r = √(64 * r ^ 2 + ℓ ^ 2)) (hℓ : ℓ ≤ ℓₜ)
    (hr : max R ((bridgeHeight L δ ℓ₀ + 2 * δ) / 6) ≤ r) :
    surroundFamily L δ ℓ₀ M F ℓ r = √(64 * r ^ 2 + ℓ * |ℓ|) := by
  have ht₁ := add_le_bridgeHeight L hδ ℓ₀
  have hLδ : 0 ≤ L * δ := by positivity
  have hr₁ := (le_max_right _ _).trans hr
  rcases le_or_gt ℓ (7 * δ) with h7 | h7
  · exact surroundFamily_eq_sqrt_of_le hL hδ h7 (by linarith)
  rw [abs_of_pos (by linarith), ← sq]
  rcases le_or_gt ℓ (2 * ℓ₀) with h2 | h2
  · rw [surroundFamily_of_lt_of_le hδ.le h7 h2]
    exact bridgeFamily_eq_sqrt hL hδ hℓ₀ hM (fun ℓ h ↦ hFs ℓ (Icc_subset_Icc_right hℓₜ h)) h2 hr
  · rw [surroundFamily_of_lt hδ.le h7 h2]
    exact hFs ℓ ⟨by linarith, hℓ⟩ r ((le_max_left _ _).trans hr)

/-- **The leaves of the glued family lie below its top leaf.** Let `L, δ > 0`, `15 δ / 2 < ℓ₀`,
`M ≥ 0` and `t₁ = bridgeHeight L δ ℓ₀` with `2 t₁ + 9 (2 ℓ₀) ≤ 1`, and let `γ' ≤ 1 / 16`.
Let `F 1` be at least `1` on `(δ, ∞)` and the standard leaf `r ↦ √(64 r² + 1)` from `γ'` on, and
let `F ℓ ≤ F 1` on `(δ, ∞)` for `ℓ ∈ [ℓ₀, 1]`. Then for `ℓ ∈ [-8 δ, 1]` and `r > δ` the leaf `ℓ`
of the glued family is at most its leaf `1` at `r`.

The leaves `ℓ ≤ 7 δ` lie below the leaf `7 δ`, which is a bridge leaf. Below `(t₁ + 2 δ) / 6`
each bridge leaf is at most `2 t₁ + 9 (2 ℓ₀) ≤ 1` or equal to `F ℓ`; beyond, it is at most the
standard leaf `ℓ` or equal to `F ℓ`; and the standard leaf `ℓ ≤ 2 ℓ₀ ≤ 1 / 9` lies below `F 1`,
which is the standard leaf `1` from `γ'` on and at least `1 > √(1 / 4 + ℓ²)` before. -/
theorem surroundFamily_le_surroundFamily_one {γ' r : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hℓ₀ : 15 * δ / 2 < ℓ₀) (hM : 0 ≤ M)
    (hsmall : 2 * bridgeHeight L δ ℓ₀ + 9 * (2 * ℓ₀) ≤ 1) (hγ' : γ' ≤ 1 / 16)
    (hF₁ : ∀ r, δ < r → 1 ≤ F 1 r) (hF₁s : ∀ r, γ' ≤ r → F 1 r = √(64 * r ^ 2 + 1))
    (hFle : ∀ ℓ ∈ Icc ℓ₀ 1, ∀ r, δ < r → F ℓ r ≤ F 1 r) (hℓ : ℓ ∈ Icc (-8 * δ) 1)
    (hr : δ < r) : surroundFamily L δ ℓ₀ M F ℓ r ≤ surroundFamily L δ ℓ₀ M F 1 r := by
  have ht₁ := add_le_bridgeHeight L hδ ℓ₀
  have hLδ : 0 ≤ L * δ := by positivity
  rw [surroundFamily_of_lt (ℓ := 1) hδ.le (by linarith) (by linarith)]
  -- The standard leaf `ℓ ∈ [0, 2 ℓ₀]` lies below `F 1` at `r`.
  have hstd {ℓ : ℝ} (hℓ : ℓ ∈ Icc 0 (2 * ℓ₀)) : √(64 * r ^ 2 + ℓ ^ 2) ≤ F 1 r := by
    have hℓ1 : ℓ ^ 2 ≤ 1 := by nlinarith [hℓ.1, hℓ.2]
    rcases le_or_gt γ' r with hγr | hγr
    · rw [hF₁s r hγr]
      exact sqrt_le_sqrt (by linarith)
    · exact (sqrt_le_one.2 (by nlinarith [hℓ.1, hℓ.2])).trans (hF₁ r hr)
  -- So does each bridge leaf.
  have hbridge {ℓ : ℝ} (hℓ : ℓ ∈ Icc (7 * δ) (2 * ℓ₀)) : bridgeFamily L δ ℓ₀ M F ℓ r ≤ F 1 r := by
    have hFℓ {ℓ : ℝ} (h : ℓ₀ < ℓ ∧ bridgeFamily L δ ℓ₀ M F ℓ r = F ℓ r) (h2 : ℓ ≤ 2 * ℓ₀) :
        bridgeFamily L δ ℓ₀ M F ℓ r ≤ F 1 r :=
      h.2 ▸ hFle ℓ ⟨h.1.le, by linarith⟩ r hr
    rcases lt_or_ge r ((bridgeHeight L δ ℓ₀ + 2 * δ) / 6) with h | h
    · rcases bridgeFamily_le_or_eq hL.le hδ hℓ₀ hM F ⟨by linarith [hℓ.1], hℓ.2⟩ hr.le h with
        h' | h'
      · linarith [hF₁ r hr]
      · exact hFℓ h' hℓ.2
    · rcases bridgeFamily_le_sqrt_or_eq (ℓ := ℓ) hL hδ hℓ₀ hM F h with h' | h'
      · exact h'.trans (hstd ⟨by linarith [hℓ.1], hℓ.2⟩)
      · exact hFℓ h' hℓ.2
  -- The leaves `ℓ ∈ [0, 7 δ]` lie below the leaf `7 δ`, a bridge leaf.
  have hsw {ℓ : ℝ} (hℓ : ℓ ∈ Icc 0 (7 * δ)) : surroundFamily L δ ℓ₀ M F ℓ r ≤ F 1 r := by
    rw [surroundFamily_eq_struweSwitchLeaf hδ.le hℓ]
    calc struweSwitchLeaf L δ ℓ r ≤ struweSwitchLeaf L δ (7 * δ) r :=
          (strictMonoOn_struweSwitchLeaf L hδ.le hr).monotoneOn hℓ.1
            (mem_Ici.2 (by linarith)) hℓ.2
      _ = bridgeFamily L δ ℓ₀ M F (7 * δ) r := (bridgeFamily_seven_mul_eqOn L hδ ℓ₀ M F hr).symm
      _ ≤ F 1 r := hbridge ⟨le_rfl, by linarith⟩
  obtain ⟨hℓ₁, hℓ₂⟩ := hℓ
  rcases le_or_gt ℓ 0 with h0 | h0
  · -- The leaves `ℓ ∈ [-8 δ, 0]` lie below the leaf `0`.
    rw [surroundFamily_of_nonpos h0]
    calc sqrtSubLeaf L δ ℓ r ≤ sqrtSubLeaf L δ 0 r :=
          (strictMonoOn_sqrtSubLeaf L hδ.le hr).monotoneOn ⟨hℓ₁, h0⟩
            ⟨by linarith, le_rfl⟩ h0
      _ = surroundFamily L δ ℓ₀ M F 0 r := by rw [surroundFamily_of_nonpos le_rfl]
      _ ≤ F 1 r := hsw ⟨le_rfl, by linarith⟩
  rcases le_or_gt ℓ (7 * δ) with h7 | h7
  · exact hsw ⟨h0.le, h7⟩
  rcases le_or_gt ℓ (2 * ℓ₀) with h2 | h2
  · rw [surroundFamily_eqOn_bridgeFamily hδ ⟨h7.le, h2⟩ hr]
    exact hbridge ⟨h7.le, h2⟩
  · rw [surroundFamily_of_lt hδ.le h7 h2]
    exact hFle ℓ ⟨by linarith, hℓ₂⟩ r hr

end surroundFamily

/-- **The surrounding family** (Cieliebak–Eliashberg, Proposition 4.27). For `0 < γ` and every
small enough `δ > 0` there is a family `χ ℓ`, `ℓ ∈ [-8 δ, 1]`, of shapes over the cylinder of
radius `δ` such that
* every `r`-derivative `(ℓ, r) ↦ ∂ᵏχ/∂rᵏ (ℓ, r)`, `χ` itself included, is jointly continuous
  on `[-8 δ, 1] × (δ, ∞)`;
* each leaf `χ ℓ` is smooth on `(δ, ∞)`, continuous and strictly increasing on `[δ, ∞)`, an
  `i`-convex shape at every `r > δ`, and its slope tends to `+∞` at `δ`;
* the bottom leaf is `χ (-8 δ) r = √(64 r² - 64 δ²)`;
* every leaf is the standard leaf `√(64 r² + ℓ |ℓ|)` from `γ` on, and, for some `r₀ ∈ (δ, γ)`,
  every leaf with `ℓ` close to `-8 δ` from above is standard from `r₀` on;
* every leaf lies below the top leaf `χ 1` on `(δ, ∞)`, and `1 < χ 1 δ < 1 + γ`.

The family is `SymplecticGeometry.surroundFamily L δ ℓ₀ M F` for a cutoff parameter `L` large
compared with bounds of the first two derivatives of `smoothTransition`, the family `F`, base
point `ℓ₀ = C δ` and slope bound `M` of
`SymplecticGeometry.exists_convexShapeFamily_struweShape_sqrt`, and `δ` so small that
`2 t₁ + 18 ℓ₀ ≤ 1` and `t₁ + 2 δ ≤ 6 γ` for the height `t₁ = bridgeHeight L δ ℓ₀` of its
bridge leaves. The leaves near `-8 δ` are standard from `r₀ = (2 + L) δ` on. -/
theorem exists_convexShapeFamily_surround {γ : ℝ} (hγ : 0 < γ) :
    ∀ᶠ δ in 𝓝[>] 0, ∃ χ : ℝ → ℝ → ℝ,
      (∀ k : ℕ, ContinuousOn (fun q : ℝ × ℝ ↦ iteratedDeriv k (χ q.1) q.2)
        (Icc (-8 * δ) 1 ×ˢ Ioi δ)) ∧
      (∀ ℓ ∈ Icc (-8 * δ) 1, ContDiffOn ℝ ∞ (χ ℓ) (Ioi δ)) ∧
      (∀ ℓ ∈ Icc (-8 * δ) 1, ContinuousOn (χ ℓ) (Ici δ)) ∧
      (∀ ℓ ∈ Icc (-8 * δ) 1, StrictMonoOn (χ ℓ) (Ici δ)) ∧
      (∀ ℓ ∈ Icc (-8 * δ) 1, ∀ r, δ < r → IsConvexShapeAt (χ ℓ) r) ∧
      (∀ r, χ (-8 * δ) r = √(64 * r ^ 2 - 64 * δ ^ 2)) ∧
      (∀ ℓ ∈ Icc (-8 * δ) 1, ∀ r, γ ≤ r → χ ℓ r = √(64 * r ^ 2 + ℓ * |ℓ|)) ∧
      (∃ r₀ ∈ Ioo δ γ, ∀ᶠ ℓ in 𝓝[≥] (-8 * δ), ∀ r, r₀ ≤ r →
        χ ℓ r = √(64 * r ^ 2 + ℓ * |ℓ|)) ∧
      (∀ ℓ ∈ Icc (-8 * δ) 1, Tendsto (deriv (χ ℓ)) (𝓝[>] δ) atTop) ∧
      (∀ ℓ ∈ Icc (-8 * δ) 1, ∀ r, δ < r → χ ℓ r ≤ χ 1 r) ∧
      1 < χ 1 δ ∧ χ 1 δ < 1 + γ := by
  obtain ⟨A, B, N, L, hA, hB, hN, hL₁, hL⟩ := exists_smoothTransition_bounds
  have hL₀ : 0 < L := by linarith
  obtain ⟨C, hC, hF⟩ := exists_convexShapeFamily_struweShape_sqrt hγ
  -- The bounds on `δ`: `(6 C + 32 + 8 L) δ < 6 γ` and `(30 C + 60 + 16 L) δ < 1`.
  have hP : 0 < 6 * C + 32 + 8 * L := by linarith
  have hQ : 0 < 30 * C + 60 + 16 * L := by linarith
  filter_upwards [Ioo_mem_nhdsGT (lt_min (div_pos (mul_pos (by norm_num : (0 : ℝ) < 6) hγ) hP)
    (one_div_pos.2 hQ))] with δ ⟨hδ, hδ'⟩
  have h₁ : (6 * C + 32 + 8 * L) * δ < 6 * γ := by
    rw [mul_comm]; exact (lt_div_iff₀ hP).1 (hδ'.trans_le (min_le_left _ _))
  have h₂ : (30 * C + 60 + 16 * L) * δ < 1 := by
    rw [mul_comm, ← lt_div_iff₀ hQ]; exact hδ'.trans_le (min_le_right _ _)
  set ℓ₀ := C * δ with hℓ₀def
  have hℓ₀ : 24 * δ ≤ ℓ₀ := mul_le_mul_of_nonneg_right hC hδ.le
  have hℓ₀₁ : 2 * ℓ₀ < 1 := by nlinarith
  have ht₁ := bridgeHeight_le L hδ ℓ₀
  have hsmall : 2 * bridgeHeight L δ ℓ₀ + 9 * (2 * ℓ₀) ≤ 1 := by nlinarith
  have hfar : (bridgeHeight L δ ℓ₀ + 2 * δ) / 6 ≤ γ := by
    rw [div_le_iff₀ (by norm_num)]
    nlinarith
  obtain ⟨F, M, hM, hFs, hFsm, hFc, hFm, hFS, -, -, hFℓ, hFγ, hF4, hFd, hF1, hF1γ⟩ :=
    hF δ hδ (by linarith [hℓ₀def])
  have hM₀ : 0 ≤ M := by linarith
  have hℓ₀' : 15 * δ / 2 < ℓ₀ := by linarith
  have hℓₜ : 2 * ℓ₀ ≤ 1 := hℓ₀₁.le
  have hℓ₀1 : ℓ₀ ≤ 1 := by linarith
  have hFc' : ∀ ℓ ∈ Icc ℓ₀ 1, ∀ r, δ < r → IsConvexShapeAt (F ℓ) r := fun ℓ h ↦ hFc ℓ h.1
  have hF2 : ∀ ℓ ∈ Icc ℓ₀ 1, ContDiffOn ℝ 2 (F ℓ) (Ioi δ) := fun ℓ h ↦
    (hFsm ℓ h.1).of_le (by simp)
  have hFS' : ∀ ℓ ∈ Icc ℓ₀ 1, ∃ c, ∀ r ∈ Icc δ (9 * δ / 2), F ℓ r = c + struweShape δ 4 0 r :=
    fun ℓ _ ↦ hFS ℓ
  have hFℓ₂ : ∀ ℓ ∈ Icc ℓ₀ (2 * ℓ₀), ∀ r, δ < r → ℓ ≤ F ℓ r :=
    fun ℓ h r hr ↦ (hFℓ ℓ h.1 r hr.le).le
  have hF4₂ : ∀ ℓ ∈ Icc ℓ₀ (2 * ℓ₀), ∀ r, ℓ / 4 ≤ r → F ℓ r = √(64 * r ^ 2 + ℓ ^ 2) :=
    fun ℓ h ↦ hF4 ℓ h.1
  refine ⟨surroundFamily L δ ℓ₀ M F, fun k ↦ ?_, fun ℓ hℓ ↦ ?_, fun ℓ hℓ ↦ ?_, fun ℓ hℓ ↦ ?_,
    fun ℓ hℓ r hr ↦ ?_, surroundFamily_neg_eight_mul hδ.le, fun ℓ hℓ r hr ↦ ?_,
    ⟨(2 + L) * δ, ⟨by nlinarith, by nlinarith⟩, ?_⟩, fun ℓ hℓ ↦ ?_, fun ℓ hℓ r hr ↦ ?_, ?_⟩
  · exact continuousOn_iteratedDeriv_surroundFamily hL₀ hδ hℓ₀ hM₀ hℓₜ
      (fun q hq ↦ hFs q ⟨hq.1.1, hq.2⟩) (hFc ℓ₀ le_rfl) (hF4 ℓ₀ le_rfl)
      (fun r hr ↦ (hFℓ _ (by linarith) r hr.le).le) (hF4 _ (by linarith)) k
  · exact contDiffOn_surroundFamily (n := ⊤) hL₀.le hδ hℓₜ (fun ℓ h ↦ hFsm ℓ h.1) hℓ
  · exact continuousOn_surroundFamily hL₀.le hδ hℓ₀' hM₀ hℓₜ hFS'
      (fun ℓ h ↦ (hFsm ℓ h.1).continuousOn) hℓ.2
  · exact strictMonoOn_surroundFamily hA hB hN hL₁ hL hδ hℓ₀ hM hℓₜ hFc' hF2 hFS' hFℓ₂ hF4₂
      hFd hℓ
  · exact isConvexShapeAt_surroundFamily hA hB hN hL₁ hL hδ hℓ₀ hM hℓₜ hFc' hF2 hFS' hFℓ₂ hF4₂
      hFd hℓ hr
  · -- The leaves `F ℓ`, `ℓ ≤ 1`, are standard from `ℓ γ' ≤ γ` on.
    refine surroundFamily_eq_sqrt (R := γ) hL₀ hδ hℓ₀' hM₀ hℓₜ (fun ℓ h r hr ↦ ?_) hℓ.2
      (max_le hr (hfar.trans hr))
    have : ℓ * min γ (1 / 16) ≤ γ := (mul_le_of_le_one_left
      (lt_min hγ (by norm_num : (0 : ℝ) < 1 / 16)).le h.2).trans (min_le_left _ _)
    exact hFγ ℓ h.1 r (this.trans hr)
  · filter_upwards [Ico_mem_nhdsGE (by linarith : -8 * δ < 7 * δ)] with ℓ hℓ r hr
    exact surroundFamily_eq_sqrt_of_le hL₀ hδ hℓ.2.le hr
  · exact tendsto_deriv_surroundFamily hL₀.le hδ hℓ₀' hM₀ hℓₜ hFS' hℓ.2
  · exact surroundFamily_le_surroundFamily_one hL₀ hδ hℓ₀' hM₀ hsmall (min_le_right _ _)
      (fun r hr ↦ (hFℓ 1 hℓ₀1 r hr.le).le)
      (fun r hr ↦ by rw [hFγ 1 hℓ₀1 r (by rwa [one_mul]), one_pow])
      (fun ℓ h r hr ↦ (hFm r hr).monotoneOn (mem_Ici.2 h.1) (mem_Ici.2 (by linarith)) h.2) hℓ hr
  · rw [surroundFamily_of_lt hδ.le (by linarith) hℓ₀₁]
    exact ⟨hF1, hF1γ⟩

end SymplecticGeometry

end
