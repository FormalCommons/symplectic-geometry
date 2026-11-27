/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.Shape

import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Topology.MetricSpace.Thickening
import SymplecticGeometry.Analysis.Calculus.IteratedDeriv.Comp
import SymplecticGeometry.Analysis.Calculus.IteratedDeriv.Lemmas
import SymplecticGeometry.Analysis.Normed.Group.Prod
import SymplecticGeometry.Analysis.SpecialFunctions.Sqrt
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.IteratedFDeriv.Bilinear
import TauCeti.Analysis.Calculus.SecondDerivative

/-!
# `i`-convex shapes

On `V = ℂᵏ × ℂᵐ`, with the shape coordinates `s = |x|²` and `t = |y|² + |w|²` of
`p = (x + i y, w)` (`SymplecticGeometry.shape`), put `R = √s` and `r = √t`. Cieliebak and
Eliashberg describe the hypersurfaces of their model handle by curves `R = χ(r)` in the quadrant of
`(r, R)`, the *shapes*, and reduce the `i`-convexity of such a hypersurface to two inequalities on
`χ` at each `r`. This file states them and proves that they give `i`-convexity.

* `SymplecticGeometry.IsConvexShapeAt χ r`: the inequalities at `r`. Its field `levi` is the
  book's (4.4), for all `σ, u` with `σ² + u² = r²`; its case `σ = 0`, `u = r` gives the book's
  (4.3), `1 / χ r < χ' r / r` (`SymplecticGeometry.IsConvexShapeAt.one_div_lt_deriv_div`), so
  that this one is not a field. `SymplecticGeometry.isConvexShapeAt_iff` says that (4.4) for all
  `σ, u` amounts to (4.3) together with its case `σ = r`, `u = 0`,
  `1 / χ r < χ'' r + χ' r ³ / r`. Since its slope is positive
  (`SymplecticGeometry.IsConvexShapeAt.deriv_pos`), a function that is an `i`-convex shape at
  every `r > δ` and continuous on `[δ, ∞)` is strictly increasing there
  (`SymplecticGeometry.strictMonoOn_Ici_of_isConvexShapeAt`).
* `SymplecticGeometry.isConvexShapeAt_of_iteratedDeriv_two_nonpos`: a sufficient condition for
  a shape with `χ'' ≤ 0`. `SymplecticGeometry.IsConvexShapeAt.add_const` and
  `SymplecticGeometry.IsConvexShapeAt.rescale`: `χ + c` for `c ≥ 0`, and `ℓ χ (· / ℓ)` at `ℓ r`
  for `ℓ > 0`, are again `i`-convex shapes. The derivatives of the rescaled shape come from
  `iteratedDeriv_comp_div_const`, with no differentiability assumption on `χ`. Lowering a shape
  by `c` lowers both margins of `isConvexShapeAt_iff` by `c / (χ (χ - c))`
  (`SymplecticGeometry.deriv_sub_const_div_sub_one_div_sub_const`,
  `SymplecticGeometry.iteratedDeriv_two_sub_const_add_pow_three_div_sub_one_div_sub_const`), so
  `χ - c` is again an `i`-convex shape while that is less than both
  (`SymplecticGeometry.IsConvexShapeAt.sub_const`).
* `SymplecticGeometry.exists_forall_isConvexShapeAt_of_abs_sub_lt`: being an `i`-convex shape
  is an open condition on `(r, χ r, χ' r, χ'' r)`, so for a compact family of shapes whose
  values and first two derivatives depend continuously on the point, one `η > 0` works for all:
  any function within `η` of a member in value and two derivatives at `r` is a shape at `r`.
  The uniform `η` comes from `IsCompact.exists_thickening_subset_open`. Its one-sided form
  `SymplecticGeometry.exists_forall_isConvexShapeAt_of_sub_lt_iteratedDeriv_two` only asks for
  `φ'' r > χ'' r - η`, since the conditions only get easier as `χ''` grows; the two-sided
  form follows from it.
* `SymplecticGeometry.exists_forall_isConvexShapeAt_mul_add_one_sub_mul`: the same stability for
  the blend `ρ φ + (1 - ρ) χ ℓ` of a shape `χ ℓ` with a nearby `C²` function `φ` by a fixed `C²`
  cutoff `ρ`. The blend is `χ ℓ + ρ (φ - χ ℓ)`, and Tau Ceti's Leibniz bound
  `ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear_of_forall_le`, for the multiplication
  of `ℝ`, bounds the derivatives of the second term by those of `ρ` times those of `φ - χ ℓ`.
  Those of `ρ` over `K` are bounded by `ContDiff.exists_norm_iteratedDeriv_le_of_isCompact`.
  For a cutoff `ρ ≥ 0`,
  `SymplecticGeometry.exists_forall_isConvexShapeAt_mul_add_one_sub_mul_of_sub_lt_iteratedDeriv_two`
  only needs `φ''` bounded below by `χ'' ℓ` up to a small error: by the Leibniz rule
  `iteratedDeriv_mul`, the second derivative of the blend is
  `χ'' + ρ (φ'' - χ'') + 2 ρ' (φ' - χ') + ρ'' (φ - χ)`.
* `SymplecticGeometry.IsConvexShapeAt.congr_of_eventuallyEq`: being an `i`-convex shape at `r`
  only depends on the germ of `χ` at `r`.
* `SymplecticGeometry.shapeGraph χ`: the function `(s, t) ↦ χ (√t) - √s`, whose zero level,
  composed with `shape`, is the hypersurface of the shape. Its partial derivatives use
  `Real.iteratedDeriv_two_sqrt` for the second derivative of `√·`, and
  `SymplecticGeometry.fderiv_shapeGraph_comp_shape_apply` gives the differential of
  `shapeGraph χ ∘ shape`. Over a point `(χ r ², r ²)` of the curve, `shapeGraph χ` vanishes
  (`SymplecticGeometry.shapeGraph_sq_sq`) and that differential does not
  (`SymplecticGeometry.fderiv_shapeGraph_comp_shape_ne_zero`).
* `SymplecticGeometry.IsConvexShapeAt.re_leviForm_pos`: if `χ` is `C²` at `r` and
  `IsConvexShapeAt χ r`, then at every `p` with `shape p = (χ r ², r ²)` the Levi form of
  `shapeGraph χ ∘ shape` is positive on the nonzero complex tangencies of its level set.
* Near the cylinder `r = δ` the shapes have vertical tangents and are graphs `r = ρ(R)` over `R`.
  `SymplecticGeometry.shapeGraphOverR ρ` is the function `(s, t) ↦ √t - ρ (√s)`, which has the
  sign of `shapeGraph χ` when `ρ` is the inverse of an increasing `χ`.
  `SymplecticGeometry.IsConvexShapeOverRAt ρ R` asks that the real part of the Levi form of
  `shapeGraphOverR ρ ∘ shape`, as `re_leviForm_comp_shape_apply_self` writes it on a complex
  tangency, be positive under the two Cauchy–Schwarz bounds on `|σ|²`. `isConvexShapeOverRAt_iff`
  reduces it to `ρ' / R < 1 / ρ`, `ρ'' < 1 / ρ - ρ'³ / R` and `ρ'' < (1 + ρ'²) / ρ` at `R`, the
  last of which follows from the second when `ρ' ≥ -R / ρ`. For the inverse of a shape the first two
  are (4.3) and the case `σ = r` of (4.4). Unlike the slope of a shape, `ρ'` may vanish, as on
  the cylinder itself. `SymplecticGeometry.IsConvexShapeOverRAt.re_leviForm_pos` is its Levi
  theorem, at `R > 0`.

Both Levi theorems rest on
`SymplecticGeometry.re_leviForm_comp_shape_apply_self_of_fderiv_eq_zero`, which evaluates
`SymplecticGeometry.re_leviForm_comp_shape_apply_self` on a complex tangency `v`. There the
Wirtinger derivatives `σ = ∂s v` and `τ = ∂t v` are proportional, `τ = c σ`, with
`c = r / (R χ')` for a shape and `c = r ρ' / R` over `R` (which allows `ρ' = 0`), and a
Cauchy–Schwarz bound for a combination of `σ` and `τ` bounds `|σ|²` by `|v|²`. This takes the
place of the book's splitting of the complex tangency into the two parts on which it computes
the Levi form separately, and of its passage from `k = n` to `k < n`, where the extra directions
only need `χ' > 0`.

The smoothed maximum of two `i`-convex shapes, and the smoothed minimum of two shapes over `R`,
are in `SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.ConvexShape.SmoothedMax`.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  §4.2–4.3: (4.3) and (4.4), Proposition 4.8 (a), (b), Proposition 4.10, Corollary 4.11 (a),
  Lemma 4.13 (a), (b) and Lemma 4.14 (a).
-/

public section

noncomputable section

namespace SymplecticGeometry

open TauCeti Complex ComplexConjugate Topology
open scoped InnerProductSpace

variable {χ : ℝ → ℝ} {r : ℝ}

/-- An **`i`-convex shape at `r`**: `χ : ℝ → ℝ` is positive at `r > 0` and satisfies
Cieliebak–Eliashberg's inequality (4.4): for all `σ, u` with `σ² + u² = r²`,
`(1 + χ'² u² / r²) / χ < χ'' σ² / r² + χ' u² / r³ + χ'³ / r` at `r`. Their (4.3),
`1 / χ < χ' / r`, is its case `σ = 0` (`IsConvexShapeAt.one_div_lt_deriv_div`). -/
structure IsConvexShapeAt (χ : ℝ → ℝ) (r : ℝ) : Prop where
  pos : 0 < r
  pos_value : 0 < χ r
  levi : ∀ σ u : ℝ, σ ^ 2 + u ^ 2 = r ^ 2 →
    1 / χ r * (1 + deriv χ r ^ 2 * u ^ 2 / r ^ 2) <
      iteratedDeriv 2 χ r * σ ^ 2 / r ^ 2 + deriv χ r * u ^ 2 / r ^ 3 + deriv χ r ^ 3 / r

namespace IsConvexShapeAt

/-- Cieliebak–Eliashberg's inequality (4.3), `1 / χ r < χ' r / r`, holds for an `i`-convex
shape. -/
theorem one_div_lt_deriv_div (h : IsConvexShapeAt χ r) : 1 / χ r < deriv χ r / r := by
  have hr := h.pos
  have hl := h.levi 0 r (by ring)
  have hd : 0 < 1 + deriv χ r ^ 2 := by positivity
  have e1 : 1 / χ r * (1 + deriv χ r ^ 2 * r ^ 2 / r ^ 2) = 1 / χ r * (1 + deriv χ r ^ 2) := by
    field_simp
  have e2 : iteratedDeriv 2 χ r * 0 ^ 2 / r ^ 2 + deriv χ r * r ^ 2 / r ^ 3 + deriv χ r ^ 3 / r =
      deriv χ r / r * (1 + deriv χ r ^ 2) := by
    field_simp
    ring
  rw [e1, e2] at hl
  exact lt_of_mul_lt_mul_right hl hd.le

/-- The slope of an `i`-convex shape is positive. -/
theorem deriv_pos (h : IsConvexShapeAt χ r) : 0 < deriv χ r :=
  (div_pos_iff_of_pos_right h.pos).1
    ((one_div_pos.2 h.pos_value).trans h.one_div_lt_deriv_div)

/-- The case `σ = r`, `u = 0` of (4.4): `1 / χ r < χ'' r + χ' r ³ / r`. -/
theorem one_div_lt_iteratedDeriv_add (h : IsConvexShapeAt χ r) :
    1 / χ r < iteratedDeriv 2 χ r + deriv χ r ^ 3 / r := by
  have hr := h.pos
  have hl := h.levi r 0 (by ring)
  have e1 : iteratedDeriv 2 χ r * r ^ 2 / r ^ 2 + deriv χ r * 0 ^ 2 / r ^ 3 + deriv χ r ^ 3 / r =
      iteratedDeriv 2 χ r + deriv χ r ^ 3 / r := by
    field_simp
    ring
  rw [e1] at hl
  simpa using hl

end IsConvexShapeAt

open Set in
/-- A function, continuous on `[δ, ∞)`, that is an `i`-convex shape at every `r > δ` is strictly
increasing on `[δ, ∞)`, since an `i`-convex shape has a positive slope. -/
theorem strictMonoOn_Ici_of_isConvexShapeAt {δ : ℝ} (hc : ContinuousOn χ (Ici δ))
    (hχ : ∀ r, δ < r → IsConvexShapeAt χ r) : StrictMonoOn χ (Ici δ) :=
  strictMonoOn_of_deriv_pos (convex_Ici δ) hc fun r hr ↦
    (hχ r (by rwa [interior_Ici] at hr)).deriv_pos

/-- `χ` is an `i`-convex shape at `r` if and only if `0 < r`, `0 < χ r`, `1 / χ r < χ' r / r`
and `1 / χ r < χ'' r + χ' r ³ / r`: the inequality (4.4) for all `σ, u` with `σ² + u² = r²`
amounts to its two cases `σ = 0` and `u = 0`. -/
theorem isConvexShapeAt_iff :
    IsConvexShapeAt χ r ↔ 0 < r ∧ 0 < χ r ∧ 1 / χ r < deriv χ r / r ∧
      1 / χ r < iteratedDeriv 2 χ r + deriv χ r ^ 3 / r := by
  refine ⟨fun h ↦ ⟨h.pos, h.pos_value, h.one_div_lt_deriv_div, h.one_div_lt_iteratedDeriv_add⟩,
    fun ⟨hr, hχ, h₃, h₄⟩ ↦ ⟨hr, hχ, fun σ u hσu ↦ ?_⟩⟩
  set d := deriv χ r
  set e := iteratedDeriv 2 χ r
  set θ := u ^ 2 / r ^ 2 with hθ
  have hθ₀ : 0 ≤ θ := by positivity
  have hσ : σ ^ 2 / r ^ 2 = 1 - θ := by
    rw [hθ]
    field_simp
    linarith
  have hθ₁ : θ ≤ 1 := by
    have : 0 ≤ σ ^ 2 / r ^ 2 := by positivity
    linarith
  -- The difference of the two sides is `(1 - θ) (e + d³/r - 1/χ) + θ (1 + d²) (d/r - 1/χ)`.
  have key : iteratedDeriv 2 χ r * σ ^ 2 / r ^ 2 + d * u ^ 2 / r ^ 3 + d ^ 3 / r -
      1 / χ r * (1 + d ^ 2 * u ^ 2 / r ^ 2) =
      (1 - θ) * (e + d ^ 3 / r - 1 / χ r) + θ * (1 + d ^ 2) * (d / r - 1 / χ r) := by
    have h1 : iteratedDeriv 2 χ r * σ ^ 2 / r ^ 2 = e * (1 - θ) := by
      rw [mul_div_assoc, hσ]
    have h2 : d * u ^ 2 / r ^ 3 = θ * d / r := by
      rw [hθ]
      field_simp
    have h3 : d ^ 2 * u ^ 2 / r ^ 2 = d ^ 2 * θ := by
      rw [hθ, mul_div_assoc]
    rw [h1, h2, h3]
    ring
  have hA : 0 < e + d ^ 3 / r - 1 / χ r := by linarith
  have hB : 0 < (1 + d ^ 2) * (d / r - 1 / χ r) := by
    have : 0 < d / r - 1 / χ r := by linarith
    positivity
  have : 0 < (1 - θ) * (e + d ^ 3 / r - 1 / χ r) + θ * (1 + d ^ 2) * (d / r - 1 / χ r) := by
    rcases hθ₁.lt_or_eq with hθ₁ | hθ₁
    · have : 0 < 1 - θ := by linarith
      linarith [mul_pos this hA, mul_nonneg hθ₀ hB.le]
    · rw [hθ₁]
      linarith
  linarith

/-- **A sufficient condition for a concave shape.** If `0 < r`, `0 < χ r`, `χ'' r ≤ 0` and
`(1 + χ' r ²) / χ r < χ'' r + χ' r ³ / r`, then `χ` is an `i`-convex shape at `r`. -/
theorem isConvexShapeAt_of_iteratedDeriv_two_nonpos (hr : 0 < r) (hχ : 0 < χ r)
    (he : iteratedDeriv 2 χ r ≤ 0)
    (h : (1 + deriv χ r ^ 2) / χ r < iteratedDeriv 2 χ r + deriv χ r ^ 3 / r) :
    IsConvexShapeAt χ r := by
  set d := deriv χ r
  have hd₁ : 0 < 1 + d ^ 2 := by positivity
  -- The hypotheses give `0 < χ' r ³ / r`, hence `0 < χ' r`.
  have hd : 0 < d := by
    have : 0 < d ^ 3 / r := by linarith [div_pos hd₁ hχ]
    exact (Odd.pow_pos_iff (by decide)).1 ((div_pos_iff_of_pos_right hr).1 this)
  refine isConvexShapeAt_iff.2 ⟨hr, hχ, ?_, ?_⟩
  · -- `χ'' ≤ 0` and `χ'³ < χ' (1 + χ'²)` give `(1 + χ'²) / χ < χ' (1 + χ'²) / r`.
    have h₁ : d ^ 3 / r < (1 + d ^ 2) * (d / r) := by
      rw [← mul_div_assoc]
      exact div_lt_div_of_pos_right (by nlinarith) hr
    have h₂ : (1 + d ^ 2) * (1 / χ r) < (1 + d ^ 2) * (d / r) := by
      rw [← mul_div_assoc, mul_one]
      linarith
    exact lt_of_mul_lt_mul_left h₂ hd₁.le
  · have : 1 / χ r ≤ (1 + d ^ 2) / χ r :=
      div_le_div_of_nonneg_right (by linarith [sq_nonneg d]) hχ.le
    linarith

open Metric in
/-- **`i`-convex shapes are stable under small one-sided `C²` perturbations, uniformly on a
compact set.** Let `K ⊆ ℝ × ℝ` be compact, with `χ ℓ` an `i`-convex shape at `r` for every
`(ℓ, r) ∈ K`, and with `(ℓ, r) ↦ iteratedDeriv k (χ ℓ) r` continuous on `K` for `k ≤ 2`. Then
there is `η > 0` such that every `φ : ℝ → ℝ` whose value and first derivative at `r` are within
`η` of those of `χ ℓ`, and whose second derivative at `r` exceeds `(χ ℓ)'' r - η`, for some
`(ℓ, r) ∈ K`, is an `i`-convex shape at `r`.

Only a lower bound on `φ''` is needed since the conditions of `isConvexShapeAt_iff` only get
easier as `χ''` grows. No differentiability of `φ` or of the `χ ℓ` is assumed: only the values of
the derivatives at `r` enter `isConvexShapeAt_iff`. -/
theorem exists_forall_isConvexShapeAt_of_sub_lt_iteratedDeriv_two {χ : ℝ → ℝ → ℝ}
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hc : ∀ x ∈ K, IsConvexShapeAt (χ x.1) x.2)
    (hcont : ∀ k ≤ 2, ContinuousOn (fun x : ℝ × ℝ ↦ iteratedDeriv k (χ x.1) x.2) K) :
    ∃ η > 0, ∀ φ : ℝ → ℝ, ∀ x ∈ K, |φ x.2 - χ x.1 x.2| < η →
      |deriv φ x.2 - deriv (χ x.1) x.2| < η →
        iteratedDeriv 2 (χ x.1) x.2 - η < iteratedDeriv 2 φ x.2 → IsConvexShapeAt φ x.2 := by
  -- The inequalities of `isConvexShapeAt_iff`, as an open set of `(r, χ r, χ' r, χ'' r)`.
  set U : Set (ℝ × ℝ × ℝ × ℝ) := {p | 0 < p.1 ∧ 0 < p.2.1 ∧ 1 / p.2.1 < p.2.2.1 / p.1 ∧
    1 / p.2.1 < p.2.2.2 + p.2.2.1 ^ 3 / p.1}
  have hU : IsOpen U := by
    refine isOpen_iff_mem_nhds.2 fun p ⟨h₁, h₂, h₃, h₄⟩ ↦ ?_
    have h₁' := h₁.ne'
    have h₂' := h₂.ne'
    have e₁ : ∀ᶠ q in 𝓝 p, 0 < q.1 := continuousAt_const.eventually_lt continuousAt_fst h₁
    have e₂ : ∀ᶠ q in 𝓝 p, 0 < q.2.1 :=
      continuousAt_const.eventually_lt (by fun_prop) h₂
    have e₃ : ∀ᶠ q in 𝓝 p, 1 / q.2.1 < q.2.2.1 / q.1 :=
      ContinuousAt.eventually_lt (by fun_prop (disch := assumption))
        (by fun_prop (disch := assumption)) h₃
    have e₄ : ∀ᶠ q in 𝓝 p, 1 / q.2.1 < q.2.2.2 + q.2.2.1 ^ 3 / q.1 :=
      ContinuousAt.eventually_lt (by fun_prop (disch := assumption))
        (by fun_prop (disch := assumption)) h₄
    filter_upwards [e₁, e₂, e₃, e₄] with q h₁ h₂ h₃ h₄ using ⟨h₁, h₂, h₃, h₄⟩
  -- The values of `(r, χ ℓ r, (χ ℓ)' r, (χ ℓ)'' r)` on `K` form a compact subset of `U`.
  set g : ℝ × ℝ → ℝ × ℝ × ℝ × ℝ :=
    fun x ↦ (x.2, χ x.1 x.2, deriv (χ x.1) x.2, iteratedDeriv 2 (χ x.1) x.2) with hg_def
  have hg : ContinuousOn g K := by
    have h₀ := hcont 0 (by norm_num)
    have h₁ := hcont 1 (by norm_num)
    simp only [iteratedDeriv_zero, iteratedDeriv_one] at h₀ h₁
    exact continuousOn_snd.prodMk (h₀.prodMk (h₁.prodMk (hcont 2 le_rfl)))
  obtain ⟨η, hη, hsub⟩ := (hK.image_of_continuousOn hg).exists_thickening_subset_open hU
    (by rintro _ ⟨x, hx, rfl⟩; exact isConvexShapeAt_iff.1 (hc x hx))
  refine ⟨η, hη, fun φ x hx h₀ h₁ h₂ ↦ ?_⟩
  -- Lowering `φ''` to at most `(χ ℓ)''` gives a point close to `g x`, hence in `U`.
  set e := min (iteratedDeriv 2 φ x.2) (iteratedDeriv 2 (χ x.1) x.2)
  have he : |e - iteratedDeriv 2 (χ x.1) x.2| < η := by
    have := min_le_right (iteratedDeriv 2 φ x.2) (iteratedDeriv 2 (χ x.1) x.2)
    rw [abs_lt]
    constructor
    · rcases min_cases (iteratedDeriv 2 φ x.2) (iteratedDeriv 2 (χ x.1) x.2) with h | h <;>
        linarith [h.1]
    · linarith
  have hq : (x.2, φ x.2, deriv φ x.2, e) ∈ U := by
    refine hsub (mem_thickening_iff.2 ⟨g x, Set.mem_image_of_mem g hx, ?_⟩)
    simp only [hg_def, Prod.dist_eq, Real.dist_eq, sub_self, abs_zero]
    exact max_lt hη (max_lt h₀ (max_lt h₁ he))
  -- `U` is a set-builder set, so membership in it is the conjunction of its conditions.
  obtain ⟨hr, hφ, h₃, h₄⟩ : 0 < x.2 ∧ 0 < φ x.2 ∧ 1 / φ x.2 < deriv φ x.2 / x.2 ∧
      1 / φ x.2 < e + deriv φ x.2 ^ 3 / x.2 := hq
  exact isConvexShapeAt_iff.2 ⟨hr, hφ, h₃, h₄.trans_le (by gcongr; exact min_le_left _ _)⟩

/-- **`i`-convex shapes are stable under small `C²` perturbations, uniformly on a compact set.**
Let `K ⊆ ℝ × ℝ` be compact, with `χ ℓ` an `i`-convex shape at `r` for every `(ℓ, r) ∈ K`, and
with `(ℓ, r) ↦ iteratedDeriv k (χ ℓ) r` continuous on `K` for `k ≤ 2`. Then there is `η > 0`
such that every `φ : ℝ → ℝ` whose value and first two derivatives at `r` are within `η` of
those of `χ ℓ`, for some `(ℓ, r) ∈ K`, is an `i`-convex shape at `r`.

No differentiability of `φ` or of the `χ ℓ` is assumed: only the values of the derivatives at
`r` enter `isConvexShapeAt_iff`. -/
theorem exists_forall_isConvexShapeAt_of_abs_sub_lt {χ : ℝ → ℝ → ℝ} {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hc : ∀ x ∈ K, IsConvexShapeAt (χ x.1) x.2)
    (hcont : ∀ k ≤ 2, ContinuousOn (fun x : ℝ × ℝ ↦ iteratedDeriv k (χ x.1) x.2) K) :
    ∃ η > 0, ∀ φ : ℝ → ℝ, ∀ x ∈ K,
      (∀ k ≤ 2, |iteratedDeriv k φ x.2 - iteratedDeriv k (χ x.1) x.2| < η) →
        IsConvexShapeAt φ x.2 := by
  obtain ⟨η, hη, h⟩ := exists_forall_isConvexShapeAt_of_sub_lt_iteratedDeriv_two hK hc hcont
  refine ⟨η, hη, fun φ x hx hφ ↦ h φ x hx ?_ ?_ ?_⟩
  · simpa only [iteratedDeriv_zero] using hφ 0 (by norm_num)
  · simpa only [iteratedDeriv_one] using hφ 1 (by norm_num)
  · linarith [(abs_lt.1 (hφ 2 le_rfl)).1]

/-- **Blending a convex shape with a nearby function by a cutoff.** Let `K ⊆ ℝ × ℝ` be compact,
with `χ ℓ` an `i`-convex shape at `r` for every `(ℓ, r) ∈ K` and
`(ℓ, r) ↦ iteratedDeriv k (χ ℓ) r` continuous on `K` for `k ≤ 2`, and let `ρ : ℝ → ℝ` be `C²`.
Then there is `τ > 0` such that for every `(ℓ, r) ∈ K` and every `φ : ℝ → ℝ` with `φ` and `χ ℓ`
both `C²` at `r`, whose value and first two derivatives at `r` are within `τ` of those of
`χ ℓ`, the blend `r ↦ ρ r * φ r + (1 - ρ r) * χ ℓ r` is an `i`-convex shape at `r`.

The cutoff `ρ` need not take values in `[0, 1]`: only its value and first two derivatives over `K`
enter `τ`. -/
theorem exists_forall_isConvexShapeAt_mul_add_one_sub_mul {χ : ℝ → ℝ → ℝ} {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hc : ∀ x ∈ K, IsConvexShapeAt (χ x.1) x.2)
    (hcont : ∀ k ≤ 2, ContinuousOn (fun x : ℝ × ℝ ↦ iteratedDeriv k (χ x.1) x.2) K)
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ 2 ρ) :
    ∃ τ > 0, ∀ φ : ℝ → ℝ, ∀ x ∈ K, ContDiffAt ℝ 2 φ x.2 → ContDiffAt ℝ 2 (χ x.1) x.2 →
      (∀ k ≤ 2, |iteratedDeriv k φ x.2 - iteratedDeriv k (χ x.1) x.2| < τ) →
        IsConvexShapeAt (fun r ↦ ρ r * φ r + (1 - ρ r) * χ x.1 r) x.2 := by
  obtain ⟨η, hη, hηK⟩ := exists_forall_isConvexShapeAt_of_abs_sub_lt hK hc hcont
  -- A bound `B` for the first two derivatives of `ρ` over the projection of `K`.
  obtain ⟨B, hB⟩ := hρ.exists_norm_iteratedDeriv_le_of_isCompact (hK.image continuous_snd)
  have hd : 0 < 4 * (B : ℝ) + 1 := by positivity
  refine ⟨η / (4 * B + 1), div_pos hη hd, fun φ x hx hφ hχ hclose ↦ hηK _ x hx fun k hk ↦ ?_⟩
  have hk' : (k : WithTop ℕ∞) ≤ 2 := by exact_mod_cast hk
  have hblend : (fun r ↦ ρ r * φ r + (1 - ρ r) * χ x.1 r) = χ x.1 + ρ * (φ - χ x.1) := by
    ext r
    simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
    ring
  have hmul : (fun r ↦ ContinuousLinearMap.mul ℝ ℝ (ρ r) ((φ - χ x.1) r)) = ρ * (φ - χ x.1) := by
    ext r
    simp
  have hρk : ContDiffAt ℝ k ρ x.2 := (hρ.of_le hk').contDiffAt
  have hdk : ContDiffAt ℝ k (φ - χ x.1) x.2 := (hφ.sub hχ).of_le hk'
  have hm : ContDiffAt ℝ k (ρ * (φ - χ x.1)) x.2 := hρk.mul hdk
  rw [hblend, iteratedDeriv_add (hχ.of_le hk') hm, add_sub_cancel_left,
    ← Real.norm_eq_abs, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have hle := (ContinuousLinearMap.mul ℝ ℝ).norm_iteratedFDeriv_le_of_bilinear_of_forall_le hρk
    hdk (M₁ := B) (M₂ := η / (4 * B + 1))
    (fun i hi ↦ by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      exact hB i (hi.trans hk) _ ⟨x, hx, rfl⟩)
    fun i hi ↦ by
      have hi' : (i : WithTop ℕ∞) ≤ 2 := by exact_mod_cast hi.trans hk
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_sub (hφ.of_le hi')
        (hχ.of_le hi'), Real.norm_eq_abs]
      exact (hclose i (hi.trans hk)).le
  rw [hmul] at hle
  have h2k : (2 : ℝ) ^ k ≤ 4 := by
    calc (2 : ℝ) ^ k ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num) hk
      _ = 4 := by norm_num
  have hlt : 4 * B * (η / (4 * B + 1)) < η := by
    rw [mul_div_assoc', div_lt_iff₀ hd]
    nlinarith
  calc _ ≤ ‖ContinuousLinearMap.mul ℝ ℝ‖ * 2 ^ k * B * (η / (4 * B + 1)) := hle
    _ ≤ 1 * 4 * B * (η / (4 * B + 1)) := by
        gcongr
        exact ContinuousLinearMap.opNorm_mul_le ℝ ℝ
    _ < η := by rwa [one_mul]

/-- **Blending a convex shape with a function that is close to it from above in `χ''`.** Let
`K ⊆ ℝ × ℝ` be compact, with `χ ℓ` an `i`-convex shape at `r` for every `(ℓ, r) ∈ K` and
`(ℓ, r) ↦ iteratedDeriv k (χ ℓ) r` continuous on `K` for `k ≤ 2`, and let `ρ : ℝ → ℝ` be `C²`
and nonnegative on the projection of `K` to `r`. Then there is `τ > 0` such that for every
`(ℓ, r) ∈ K` and every `φ : ℝ → ℝ` with `φ` and `χ ℓ` both `C²` at `r`, whose value and first
derivative at `r` are within `τ` of those of `χ ℓ` and whose second derivative at `r` exceeds
`(χ ℓ)'' r - τ`, the blend `r ↦ ρ r * φ r + (1 - ρ r) * χ ℓ r` is an `i`-convex shape at `r`.

The second derivative of the blend is `χ'' + ρ (φ'' - χ'') + 2 ρ' (φ' - χ') + ρ'' (φ - χ)`, so
that `ρ ≥ 0` turns the lower bound on `φ''` into one for the blend. -/
theorem exists_forall_isConvexShapeAt_mul_add_one_sub_mul_of_sub_lt_iteratedDeriv_two
    {χ : ℝ → ℝ → ℝ} {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hc : ∀ x ∈ K, IsConvexShapeAt (χ x.1) x.2)
    (hcont : ∀ k ≤ 2, ContinuousOn (fun x : ℝ × ℝ ↦ iteratedDeriv k (χ x.1) x.2) K)
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ 2 ρ) (hρ₀ : ∀ x ∈ K, 0 ≤ ρ x.2) :
    ∃ τ > 0, ∀ φ : ℝ → ℝ, ∀ x ∈ K, ContDiffAt ℝ 2 φ x.2 → ContDiffAt ℝ 2 (χ x.1) x.2 →
      |φ x.2 - χ x.1 x.2| < τ → |deriv φ x.2 - deriv (χ x.1) x.2| < τ →
        iteratedDeriv 2 (χ x.1) x.2 - τ < iteratedDeriv 2 φ x.2 →
          IsConvexShapeAt (fun r ↦ ρ r * φ r + (1 - ρ r) * χ x.1 r) x.2 := by
  obtain ⟨η, hη, hηK⟩ := exists_forall_isConvexShapeAt_of_sub_lt_iteratedDeriv_two hK hc hcont
  -- A bound `B` for the first two derivatives of `ρ` over the projection of `K`.
  obtain ⟨B, hB⟩ := hρ.exists_norm_iteratedDeriv_le_of_isCompact (hK.image continuous_snd)
  have hd : 0 < 4 * (B : ℝ) + 1 := by positivity
  set τ := η / (4 * B + 1)
  have hτ : 0 < τ := div_pos hη hd
  have hBτ : 4 * B * τ < η := by
    rw [mul_div_assoc', div_lt_iff₀ hd]
    nlinarith
  refine ⟨τ, hτ, fun φ x hx hφ hχ h₀ h₁ h₂ ↦ ?_⟩
  have hBk : ∀ k ≤ 2, |iteratedDeriv k ρ x.2| ≤ B := fun k hk ↦ by
    rw [← Real.norm_eq_abs]
    exact hB k hk _ ⟨x, hx, rfl⟩
  have hρ0 := hBk 0 (by norm_num)
  have hρ1 := hBk 1 (by norm_num)
  have hρ2 := hBk 2 le_rfl
  simp only [iteratedDeriv_zero, iteratedDeriv_one] at hρ0 hρ1
  have hblend : (fun r ↦ ρ r * φ r + (1 - ρ r) * χ x.1 r) = χ x.1 + ρ * (φ - χ x.1) := by
    ext r
    simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
    ring
  -- The derivatives of the blend minus those of `χ ℓ`, by the Leibniz rule.
  have hk : ∀ k ≤ 2, iteratedDeriv k (fun r ↦ ρ r * φ r + (1 - ρ r) * χ x.1 r) x.2 -
      iteratedDeriv k (χ x.1) x.2 = ∑ i ∈ Finset.range (k + 1), k.choose i *
        iteratedDeriv i ρ x.2 * (iteratedDeriv (k - i) φ x.2 -
          iteratedDeriv (k - i) (χ x.1) x.2) := fun k hk ↦ by
    have hk' : (k : WithTop ℕ∞) ≤ 2 := by exact_mod_cast hk
    have hdk : ContDiffAt ℝ k (φ - χ x.1) x.2 := (hφ.sub hχ).of_le hk'
    have hρk : ContDiffAt ℝ k ρ x.2 := (hρ.of_le hk').contDiffAt
    have hm : ContDiffAt ℝ k (ρ * (φ - χ x.1)) x.2 := hρk.mul hdk
    rw [hblend, iteratedDeriv_add (hχ.of_le hk') hm, add_sub_cancel_left,
      iteratedDeriv_mul hρk hdk]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hi' : ((k - i : ℕ) : WithTop ℕ∞) ≤ 2 := by exact_mod_cast (Nat.sub_le k i).trans hk
    rw [iteratedDeriv_sub (hφ.of_le hi') (hχ.of_le hi')]
  have e₀ := hk 0 (by norm_num)
  have e₁ := hk 1 (by norm_num)
  have e₂ := hk 2 le_rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_zero_right,
    Nat.choose_self, Nat.choose_one_right, iteratedDeriv_zero,
    iteratedDeriv_one, Nat.cast_one, Nat.cast_ofNat, zero_add, one_mul, Nat.sub_self,
    tsub_zero, Nat.add_one_sub_one] at e₀ e₁ e₂
  -- Each term is a derivative of `ρ`, at most `B`, times a difference, at most `τ`.
  have hab : ∀ a b : ℝ, |a| ≤ B → |b| < τ → |a * b| ≤ B * τ := fun a b ha hb ↦ by
    rw [abs_mul]
    gcongr
  refine hηK _ x hx ?_ ?_ ?_
  · rw [e₀]
    linarith [hab _ _ hρ0 h₀]
  · rw [e₁]
    linarith [abs_add_le (ρ x.2 * (deriv φ x.2 - deriv (χ x.1) x.2))
      (deriv ρ x.2 * (φ x.2 - χ x.1 x.2)), hab _ _ hρ0 h₁, hab _ _ hρ1 h₀]
  · -- Only here `ρ ≥ 0` is needed, as `φ - χ ℓ` is only bounded below.
    have hρx := hρ₀ x hx
    have hp₀ : -(B * τ) ≤ ρ x.2 * (iteratedDeriv 2 φ x.2 - iteratedDeriv 2 (χ x.1) x.2) := by
      have := le_of_abs_le hρ0
      nlinarith
    linarith [neg_abs_le (deriv ρ x.2 * (deriv φ x.2 - deriv (χ x.1) x.2)),
      neg_abs_le (iteratedDeriv 2 ρ x.2 * (φ x.2 - χ x.1 x.2)), hab _ _ hρ1 h₁, hab _ _ hρ2 h₀]

/-- Lowering a shape by a constant `c` lowers its margin `χ' / r - 1 / χ` in (4.3) at `r` by
exactly `c / (χ r (χ r - c))`, since only the term `1 / χ` changes. -/
theorem deriv_sub_const_div_sub_one_div_sub_const {c : ℝ} (hχ : χ r ≠ 0) (hc : χ r - c ≠ 0) :
    deriv (fun r ↦ χ r - c) r / r - 1 / (χ r - c) =
      deriv χ r / r - 1 / χ r - c / (χ r * (χ r - c)) := by
  rw [deriv_sub_const]
  field_simp
  ring

/-- Lowering a shape by a constant `c` lowers its margin `χ'' + χ'³ / r - 1 / χ` in the case
`σ = r` of (4.4) at `r` by exactly `c / (χ r (χ r - c))`, since only the term `1 / χ`
changes. -/
theorem iteratedDeriv_two_sub_const_add_pow_three_div_sub_one_div_sub_const {c : ℝ}
    (hχ : χ r ≠ 0) (hc : χ r - c ≠ 0) :
    iteratedDeriv 2 (fun r ↦ χ r - c) r + deriv (fun r ↦ χ r - c) r ^ 3 / r - 1 / (χ r - c) =
      iteratedDeriv 2 χ r + deriv χ r ^ 3 / r - 1 / χ r - c / (χ r * (χ r - c)) := by
  rw [iteratedDeriv_sub_const two_pos, deriv_sub_const]
  field_simp
  ring

namespace IsConvexShapeAt

/-- Being an `i`-convex shape at `r` only depends on the germ of the shape at `r`. -/
theorem congr_of_eventuallyEq {ψ : ℝ → ℝ} (h : IsConvexShapeAt χ r) (hψ : ψ =ᶠ[𝓝 r] χ) :
    IsConvexShapeAt ψ r := by
  rw [isConvexShapeAt_iff, hψ.eq_of_nhds, hψ.deriv_eq, hψ.iteratedDeriv_eq 2]
  exact isConvexShapeAt_iff.1 h

/-- A shape stays `i`-convex when it is shifted up: `χ + c` is an `i`-convex shape at `r` if `χ`
is and `0 ≤ c`. -/
theorem add_const {c : ℝ} (hc : 0 ≤ c) (h : IsConvexShapeAt χ r) :
    IsConvexShapeAt (fun r ↦ χ r + c) r := by
  have hχ := h.pos_value
  have hle : 1 / (χ r + c) ≤ 1 / χ r := one_div_le_one_div_of_le hχ (by linarith)
  refine isConvexShapeAt_iff.2 ⟨h.pos, by linarith, ?_, ?_⟩
  · rw [deriv_add_const]
    exact hle.trans_lt h.one_div_lt_deriv_div
  · rw [deriv_add_const, iteratedDeriv_add_const two_pos]
    exact hle.trans_lt h.one_div_lt_iteratedDeriv_add

/-- A shape stays `i`-convex when it is lowered a little: `χ - c` is an `i`-convex shape at `r`
if `χ` is, `c < χ r`, and `c / (χ r (χ r - c))`, by which the lowering decreases both margins of
`isConvexShapeAt_iff`, is less than each of them. -/
theorem sub_const {c : ℝ} (h : IsConvexShapeAt χ r) (hc : c < χ r)
    (h₃ : c / (χ r * (χ r - c)) < deriv χ r / r - 1 / χ r)
    (h₄ : c / (χ r * (χ r - c)) < iteratedDeriv 2 χ r + deriv χ r ^ 3 / r - 1 / χ r) :
    IsConvexShapeAt (fun r ↦ χ r - c) r := by
  have hχ := h.pos_value.ne'
  have hc' := (sub_pos.2 hc).ne'
  have e₃ := deriv_sub_const_div_sub_one_div_sub_const hχ hc'
  have e₄ := iteratedDeriv_two_sub_const_add_pow_three_div_sub_one_div_sub_const hχ hc'
  refine isConvexShapeAt_iff.2 ⟨h.pos, sub_pos.2 hc, ?_, ?_⟩ <;> linarith

/-- A shape stays `i`-convex under the rescaling `χ ↦ ℓ χ (· / ℓ)` of the plane of `(r, R)` by
`ℓ > 0`: if `χ` is an `i`-convex shape at `r`, then `r ↦ ℓ χ (r / ℓ)` is one at `ℓ r`. -/
theorem rescale {ℓ : ℝ} (hℓ : 0 < ℓ) (h : IsConvexShapeAt χ r) :
    IsConvexShapeAt (fun r ↦ ℓ * χ (r / ℓ)) (ℓ * r) := by
  have hr := h.pos
  have hχ := h.pos_value
  -- The derivatives of `r ↦ ℓ χ (r / ℓ)`, which need no differentiability of `χ`.
  have hn (n : ℕ) : iteratedDeriv n (fun r ↦ ℓ * χ (r / ℓ)) (ℓ * r) =
      ℓ * (ℓ⁻¹ ^ n * iteratedDeriv n χ r) := by
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_comp_div_const]
    simp only [mul_div_cancel_left₀ r hℓ.ne', smul_eq_mul]
  have h₁ : deriv (fun r ↦ ℓ * χ (r / ℓ)) (ℓ * r) = deriv χ r := by
    simpa [iteratedDeriv_one, hℓ.ne'] using hn 1
  have h₂ : iteratedDeriv 2 (fun r ↦ ℓ * χ (r / ℓ)) (ℓ * r) = iteratedDeriv 2 χ r / ℓ := by
    rw [hn 2]
    field_simp
  have hv : ℓ * χ (ℓ * r / ℓ) = ℓ * χ r := by
    rw [mul_div_cancel_left₀ r hℓ.ne']
  have e₁ : 1 / (ℓ * χ r) = 1 / χ r / ℓ := by rw [div_div, mul_comm]
  refine isConvexShapeAt_iff.2 ⟨by positivity, by rw [hv]; positivity, ?_, ?_⟩
  · rw [h₁, hv, e₁, show deriv χ r / (ℓ * r) = deriv χ r / r / ℓ by rw [div_div, mul_comm ℓ]]
    exact div_lt_div_of_pos_right h.one_div_lt_deriv_div hℓ
  · rw [h₁, h₂, hv, e₁, show iteratedDeriv 2 χ r / ℓ + deriv χ r ^ 3 / (ℓ * r) =
      (iteratedDeriv 2 χ r + deriv χ r ^ 3 / r) / ℓ by rw [add_div, div_div, mul_comm r]]
    exact div_lt_div_of_pos_right h.one_div_lt_iteratedDeriv_add hℓ

end IsConvexShapeAt

/-- The **defining function of a shape** `χ`: `(s, t) ↦ χ (√t) - √s`. Composed with
`shape`, its zero level near `shape p = (χ r ², r ²)` is the hypersurface `R = χ (r)`, with
`R = √s` and `r = √t`. -/
def shapeGraph (χ : ℝ → ℝ) (q : ℝ × ℝ) : ℝ :=
  χ (√q.2) - √q.1

theorem shapeGraph_def (χ : ℝ → ℝ) (q : ℝ × ℝ) : shapeGraph χ q = χ (√q.2) - √q.1 :=
  (rfl)

/-- `shapeGraph χ` is a separated sum of the functions `s ↦ -√s` and `t ↦ χ (√t)`. -/
theorem shapeGraph_eq_comp_fst_add_comp_snd (χ : ℝ → ℝ) :
    shapeGraph χ = (fun s ↦ -√s) ∘ Prod.fst + (χ ∘ fun t ↦ √t) ∘ Prod.snd := by
  funext q
  simp [shapeGraph_def, sub_eq_neg_add]

/-- `shapeGraph χ` is `Cⁿ` at `(s, t)` with `s, t > 0` if `χ` is `Cⁿ` at `√t`. -/
theorem contDiffAt_shapeGraph {n : WithTop ℕ∞} {s t : ℝ} (hχ : ContDiffAt ℝ n χ (√t))
    (hs : 0 < s) (ht : 0 < t) : ContDiffAt ℝ n (shapeGraph χ) (s, t) := by
  rw [shapeGraph_eq_comp_fst_add_comp_snd]
  exact ((Real.contDiffAt_sqrt hs.ne').neg.comp (s, t) contDiffAt_fst).add
    ((hχ.comp t (Real.contDiffAt_sqrt ht.ne')).comp (s, t) contDiffAt_snd)

/-- The differential of `shapeGraph χ` at `(s, t)` with `s, t > 0`:
`(a, b) ↦ -a / (2 √s) + b χ'(√t) / (2 √t)`. -/
theorem fderiv_shapeGraph_apply {s t : ℝ} (hχ : DifferentiableAt ℝ χ (√t)) (hs : 0 < s)
    (ht : 0 < t) (a b : ℝ) :
    fderiv ℝ (shapeGraph χ) (s, t) (a, b) = -a / (2 * √s) + b * deriv χ (√t) / (2 * √t) := by
  have hf : HasDerivAt (fun s ↦ -√s) (-(1 / (2 * √s))) s := (Real.hasDerivAt_sqrt hs.ne').neg
  have hg : HasDerivAt (χ ∘ fun t ↦ √t) (deriv χ (√t) * (1 / (2 * √t))) t :=
    hχ.hasDerivAt.comp t (Real.hasDerivAt_sqrt ht.ne')
  rw [shapeGraph_eq_comp_fst_add_comp_snd,
    fderiv_comp_fst_add_comp_snd hf.differentiableAt hg.differentiableAt]
  rw [hf.hasFDerivAt.fderiv, hg.hasFDerivAt.fderiv]
  simp only [ContinuousLinearMap.coprod_apply, ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul]
  ring

/-- The second derivative of `shapeGraph χ` at `(s, t)` with `s, t > 0` is diagonal:
`((a, b), (a', b')) ↦ a a' / (4 s √s) + b b' (χ''(√t) / (4 t) - χ'(√t) / (4 t √t))`. -/
theorem fderiv_fderiv_shapeGraph_apply {s t : ℝ} (hχ : ContDiffAt ℝ 2 χ (√t)) (hs : 0 < s)
    (ht : 0 < t) (a b a' b' : ℝ) :
    fderiv ℝ (fderiv ℝ (shapeGraph χ)) (s, t) (a, b) (a', b') =
      a * a' / (4 * s * √s) +
        b * b' * (iteratedDeriv 2 χ (√t) / (4 * t) - deriv χ (√t) / (4 * t * √t)) := by
  have hf : ContDiffAt ℝ 2 (fun s ↦ -√s) s := (Real.contDiffAt_sqrt hs.ne').neg
  have hg : ContDiffAt ℝ 2 (χ ∘ fun t ↦ √t) t := hχ.comp t (Real.contDiffAt_sqrt ht.ne')
  have h2f : iteratedDeriv 2 (fun s ↦ -√s) s = 1 / (4 * s * √s) := by
    rw [iteratedDeriv_fun_neg, Real.iteratedDeriv_two_sqrt hs]
    ring
  rw [shapeGraph_eq_comp_fst_add_comp_snd, fderiv_fderiv_comp_fst_add_comp_snd hf hg]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.coe_prodMap', Prod.map_fst, Prod.map_snd,
    ContinuousLinearMap.coprodEquivL_apply_apply,
    fderiv_fderiv_apply_eq_smul_iteratedDeriv, h2f, Real.iteratedDeriv_two_comp_sqrt hχ ht,
    smul_eq_mul]
  ring

variable {k m : ℕ}

/-- The differential of `shapeGraph χ ∘ shape` at `p` with `s = (shape p).1 > 0` and
`t = (shape p).2 > 0`, for `χ` differentiable at `√t`:
`v ↦ -ds_p v / (2 √s) + dt_p v χ'(√t) / (2 √t)`. -/
theorem fderiv_shapeGraph_comp_shape_apply
    {p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)}
    (hχ : DifferentiableAt ℝ χ (√(shape p).2)) (hs : 0 < (shape p).1) (ht : 0 < (shape p).2)
    (v : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    fderiv ℝ (shapeGraph χ ∘ shape) p v =
      -fderiv ℝ (fun q ↦ (shape q).1) p v / (2 * √(shape p).1) +
        fderiv ℝ (fun q ↦ (shape q).2) p v * deriv χ (√(shape p).2) / (2 * √(shape p).2) := by
  have hH : DifferentiableAt ℝ (shapeGraph χ) (shape p) := by
    rw [shapeGraph_eq_comp_fst_add_comp_snd]
    exact ((Real.hasDerivAt_sqrt hs.ne').neg.differentiableAt.comp _ differentiableAt_fst).add
      ((hχ.comp _ (Real.hasDerivAt_sqrt ht.ne').differentiableAt).comp _ differentiableAt_snd)
  have h := fderiv_shapeGraph_apply hχ hs ht (fderiv ℝ (fun q ↦ (shape q).1) p v)
    (fderiv ℝ (fun q ↦ (shape q).2) p v)
  rw [Prod.mk.eta] at h
  rw [fderiv_comp_shape_apply hH, h]

/-- `shapeGraph χ` vanishes at the point `(χ r ², r ²)` of the curve of the shape, for
`χ r ≥ 0` and `r ≥ 0`. -/
theorem shapeGraph_sq_sq (hR : 0 ≤ χ r) (hr : 0 ≤ r) : shapeGraph χ (χ r ^ 2, r ^ 2) = 0 := by
  rw [shapeGraph_def, Real.sqrt_sq hr, Real.sqrt_sq hR, sub_self]

/-- The differential of `shapeGraph χ ∘ shape` at a point `p` over the point `(χ r ², r ²)` of the
curve of the shape, for `χ r > 0`, `r > 0` and `χ` differentiable at `r`:
`v ↦ -ds_p v / (2 χ r) + dt_p v χ'(r) / (2 r)`. -/
theorem fderiv_shapeGraph_comp_shape_apply_of_shape_eq (hχ : DifferentiableAt ℝ χ r)
    (hR : 0 < χ r) (hr : 0 < r) {p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)}
    (hp : shape p = (χ r ^ 2, r ^ 2)) (v : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    fderiv ℝ (shapeGraph χ ∘ shape) p v =
      -fderiv ℝ (fun q ↦ (shape q).1) p v / (2 * χ r) +
        fderiv ℝ (fun q ↦ (shape q).2) p v * deriv χ r / (2 * r) := by
  have hsr : √(r ^ 2) = r := Real.sqrt_sq hr.le
  rw [fderiv_shapeGraph_comp_shape_apply (by rwa [hp, hsr]) (by rw [hp]; positivity)
    (by rw [hp]; positivity), hp, Real.sqrt_sq hR.le, hsr]

/-- At a point `p` over the point `(χ r ², r ²)` of the curve of the shape, for `χ r > 0`, `r > 0`
and `χ` differentiable at `r`, the differential of `shapeGraph χ ∘ shape` does not vanish: it
takes the value `-χ r` on the vector `((Re p₁ⱼ)ⱼ, 0)`. -/
theorem fderiv_shapeGraph_comp_shape_ne_zero (hχ : DifferentiableAt ℝ χ r) (hR : 0 < χ r)
    (hr : 0 < r) {p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)}
    (hp : shape p = (χ r ^ 2, r ^ 2)) : fderiv ℝ (shapeGraph χ ∘ shape) p ≠ 0 := by
  intro h0
  have h1 := fderiv_shapeGraph_comp_shape_apply_of_shape_eq hχ hR hr hp
    (modelDisc k m (modelDiscProj k m p))
  rw [h0, zero_apply, fderiv_shape_fst_apply, fderiv_shape_snd_apply] at h1
  have hsum : ∑ j, (p.1 j).re * (p.1 j).re = χ r ^ 2 := by
    have h2 : (shape p).1 = χ r ^ 2 := by rw [hp]
    rw [shape_fst] at h2
    rw [← h2]
    exact Finset.sum_congr rfl fun j _ ↦ (sq _).symm
  simp only [modelDisc_apply_fst_apply, modelDisc_apply_snd, modelDiscProj_apply,
    ofReal_re, ofReal_im, mul_zero, Finset.sum_const_zero, inner_zero_right, zero_re, add_zero,
    hsum] at h1
  field_simp at h1
  exact hR.ne' (by nlinarith [h1])

/-- **The Levi form of an `i`-convex shape.** Let `χ` be `C²` at `r` and an `i`-convex shape
there, and let `p ∈ ℂᵏ × ℂᵐ` lie on the hypersurface of the shape, `shape p = (χ r ², r ²)`. Then
the Levi form of `F = shapeGraph χ ∘ shape` at `p` is positive on every nonzero `v` with
`dF_p v = 0` and `dF_p (i v) = 0`, that is on the nonzero complex tangent vectors of the level set
of `F` through `p`. -/
theorem IsConvexShapeAt.re_leviForm_pos (hχ : ContDiffAt ℝ 2 χ r) (h : IsConvexShapeAt χ r)
    {p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)} (hp : shape p = (χ r ^ 2, r ^ 2))
    {v : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)} (hv : v ≠ 0)
    (hv₁ : fderiv ℝ (shapeGraph χ ∘ shape) p v = 0)
    (hv₂ : fderiv ℝ (shapeGraph χ ∘ shape) p (I • v) = 0) :
    0 < (leviForm (shapeGraph χ ∘ shape) p v v).re := by
  have hr := h.pos
  have hR := h.pos_value
  have hd := h.deriv_pos
  have h₃ := h.one_div_lt_deriv_div
  have h₄ := h.one_div_lt_iteratedDeriv_add
  have hsR : √(χ r ^ 2) = χ r := Real.sqrt_sq hR.le
  have hsr : √(r ^ 2) = r := Real.sqrt_sq hr.le
  have hχ' : ContDiffAt ℝ 2 χ (√(r ^ 2)) := by rwa [hsr]
  have hs : 0 < χ r ^ 2 := by positivity
  have ht : 0 < r ^ 2 := by positivity
  have hH : ContDiffAt ℝ 2 (shapeGraph χ) (shape p) := hp ▸ contDiffAt_shapeGraph hχ' hs ht
  set R := χ r
  set d := deriv χ r
  set e := iteratedDeriv 2 χ r
  have hH₁ (a b : ℝ) : fderiv ℝ (shapeGraph χ) (shape p) (a, b) = -a / (2 * R) + b * d / (2 * r) :=
    by rw [hp, fderiv_shapeGraph_apply (hχ'.differentiableAt (by norm_num)) hs ht, hsR, hsr]
  have hH₂ (a b a' b' : ℝ) : fderiv ℝ (fderiv ℝ (shapeGraph χ)) (shape p) (a, b) (a', b') =
      a * a' / (4 * R ^ 2 * R) + b * b' * (e / (4 * r ^ 2) - d / (4 * r ^ 2 * r)) := by
    rw [hp, fderiv_fderiv_shapeGraph_apply hχ' hs ht, hsR, hsr]
  -- On a complex tangency, `τ = l σ` with `l = r / (χ' R)`.
  set l := r / (d * R) with hl
  obtain ⟨-, hL, -, hCS⟩ := re_leviForm_comp_shape_apply_self_of_fderiv_eq_zero hH (c := l)
    (by rw [hH₁]; positivity) (by rw [hH₁, hH₁, hl]; field_simp; ring) hv₁ hv₂
  rw [hL, hH₁, hH₁, hH₂, hH₂, hH₂]
  rw [hp] at hCS
  dsimp only at hCS
  set S := ‖∑ j, ((p.1 j).re : ℂ) * v.1 j‖ ^ 2
  set a := ‖v.1‖ ^ 2
  set b := ‖v.2‖ ^ 2
  have hS : 0 ≤ S := by positivity
  have hb₀ : 0 ≤ b := by positivity
  have hab : 0 < a + b := Prod.norm_fst_sq_add_norm_snd_sq_pos hv
  have hX : 0 ≤ d ^ 2 * R ^ 2 * (a + b) - (1 + d ^ 2) * S := by
    have e₁ : (1 + d ^ 2) * S = d ^ 2 / r ^ 2 * ((r ^ 2 + l ^ 2 * R ^ 2) * S) := by
      rw [hl]
      field_simp
      ring
    have e₂ : d ^ 2 * R ^ 2 * (a + b) = d ^ 2 / r ^ 2 * (R ^ 2 * r ^ 2 * (a + b)) := by
      field_simp
    rw [e₁, e₂, sub_nonneg]
    exact mul_le_mul_of_nonneg_left hCS (by positivity)
  have hA : 0 < d / r - 1 / R := by linarith
  have hE : 0 < e + d ^ 3 / r - 1 / R := by linarith
  have hY : 0 < R ^ 2 * d ^ 2 * (d / r + 1 / R) := by positivity
  have hN : 0 < (d / r - 1 / R) * (d ^ 2 * R ^ 2 * (a + b) - (1 + d ^ 2) * S) +
      b * (R ^ 2 * d ^ 2 * (d / r + 1 / R)) + S * (e + d ^ 3 / r - 1 / R) := by
    have h1 := mul_nonneg hA.le hX
    have h2 := mul_nonneg hb₀ hY.le
    rcases hS.lt_or_eq with hS' | hS'
    · linarith [mul_pos hS' hE]
    · rw [← hS'] at h1 ⊢
      have hX' : 0 < d ^ 2 * R ^ 2 * (a + b) - (1 + d ^ 2) * 0 := by
        rw [mul_zero, sub_zero]
        positivity
      linarith [mul_pos hA hX']
  convert div_pos hN (by positivity : (0 : ℝ) < 4 * R ^ 2 * d ^ 2) using 1
  rw [hl]
  field_simp
  ring

/-! ### Shapes as graphs over `R`

Near the cylinder `r = δ` the shapes have vertical tangents, and their hypersurfaces are graphs
`r = ρ (R)` over `R = √s` rather than graphs `R = χ (r)` over `r = √t`. -/

/-- The **defining function of a shape over `R`** `ρ`: `(s, t) ↦ √t - ρ (√s)`. Composed with
`shape`, its zero level near `shape p = (R ², ρ R ²)` is the hypersurface `r = ρ (R)`, with
`R = √s` and `r = √t`. Where `ρ` is the inverse of an increasing `χ`, it has the sign of
`shapeGraph χ`. -/
def shapeGraphOverR (ρ : ℝ → ℝ) (q : ℝ × ℝ) : ℝ :=
  √q.2 - ρ (√q.1)

theorem shapeGraphOverR_def (ρ : ℝ → ℝ) (q : ℝ × ℝ) : shapeGraphOverR ρ q = √q.2 - ρ (√q.1) :=
  (rfl)

/-- `shapeGraphOverR ρ` is a separated sum of the functions `s ↦ -ρ (√s)` and `t ↦ √t`. -/
theorem shapeGraphOverR_eq_comp_fst_add_comp_snd (ρ : ℝ → ℝ) :
    shapeGraphOverR ρ = (-(ρ ∘ fun s ↦ √s)) ∘ Prod.fst + (fun t ↦ √t) ∘ Prod.snd := by
  funext q
  simp [shapeGraphOverR_def, sub_eq_neg_add]

/-- `shapeGraphOverR ρ` is `Cⁿ` at `(s, t)` with `s, t > 0` if `ρ` is `Cⁿ` at `√s`. -/
theorem contDiffAt_shapeGraphOverR {ρ : ℝ → ℝ} {n : WithTop ℕ∞} {s t : ℝ}
    (hρ : ContDiffAt ℝ n ρ (√s)) (hs : 0 < s) (ht : 0 < t) :
    ContDiffAt ℝ n (shapeGraphOverR ρ) (s, t) := by
  rw [shapeGraphOverR_eq_comp_fst_add_comp_snd]
  exact ((hρ.comp s (Real.contDiffAt_sqrt hs.ne')).neg.comp (s, t) contDiffAt_fst).add
    ((Real.contDiffAt_sqrt ht.ne').comp (s, t) contDiffAt_snd)

/-- The differential of `shapeGraphOverR ρ` at `(s, t)` with `s, t > 0`:
`(a, b) ↦ -a ρ'(√s) / (2 √s) + b / (2 √t)`. -/
theorem fderiv_shapeGraphOverR_apply {ρ : ℝ → ℝ} {s t : ℝ} (hρ : DifferentiableAt ℝ ρ (√s))
    (hs : 0 < s) (ht : 0 < t) (a b : ℝ) :
    fderiv ℝ (shapeGraphOverR ρ) (s, t) (a, b) =
      -a * deriv ρ (√s) / (2 * √s) + b / (2 * √t) := by
  have hf : HasDerivAt (-(ρ ∘ fun s ↦ √s)) (-(deriv ρ (√s) * (1 / (2 * √s)))) s :=
    (hρ.hasDerivAt.comp s (Real.hasDerivAt_sqrt hs.ne')).neg
  have hg : HasDerivAt (fun t ↦ √t) (1 / (2 * √t)) t := Real.hasDerivAt_sqrt ht.ne'
  rw [shapeGraphOverR_eq_comp_fst_add_comp_snd,
    fderiv_comp_fst_add_comp_snd hf.differentiableAt hg.differentiableAt,
    hf.hasFDerivAt.fderiv, hg.hasFDerivAt.fderiv]
  simp only [ContinuousLinearMap.coprod_apply, ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul]
  ring

/-- The second derivative of `shapeGraphOverR ρ` at `(s, t)` with `s, t > 0` is diagonal:
`((a, b), (a', b')) ↦ a a' (ρ'(√s) / (4 s √s) - ρ''(√s) / (4 s)) - b b' / (4 t √t)`. -/
theorem fderiv_fderiv_shapeGraphOverR_apply {ρ : ℝ → ℝ} {s t : ℝ} (hρ : ContDiffAt ℝ 2 ρ (√s))
    (hs : 0 < s) (ht : 0 < t) (a b a' b' : ℝ) :
    fderiv ℝ (fderiv ℝ (shapeGraphOverR ρ)) (s, t) (a, b) (a', b') =
      a * a' * (deriv ρ (√s) / (4 * s * √s) - iteratedDeriv 2 ρ (√s) / (4 * s)) -
        b * b' / (4 * t * √t) := by
  have hf : ContDiffAt ℝ 2 (-(ρ ∘ fun s ↦ √s)) s := (hρ.comp s (Real.contDiffAt_sqrt hs.ne')).neg
  have hg : ContDiffAt ℝ 2 (fun t ↦ √t) t := Real.contDiffAt_sqrt ht.ne'
  have h2f : iteratedDeriv 2 (-(ρ ∘ fun s ↦ √s)) s =
      deriv ρ (√s) / (4 * s * √s) - iteratedDeriv 2 ρ (√s) / (4 * s) := by
    rw [iteratedDeriv_neg, Real.iteratedDeriv_two_comp_sqrt hρ hs]
    ring
  rw [shapeGraphOverR_eq_comp_fst_add_comp_snd, fderiv_fderiv_comp_fst_add_comp_snd hf hg]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.coe_prodMap', Prod.map_fst, Prod.map_snd,
    ContinuousLinearMap.coprodEquivL_apply_apply,
    fderiv_fderiv_apply_eq_smul_iteratedDeriv, h2f, Real.iteratedDeriv_two_sqrt ht, smul_eq_mul]
  ring

/-- The differential of `shapeGraphOverR ρ ∘ shape` at `p` with `s = (shape p).1 > 0` and
`t = (shape p).2 > 0`, for `ρ` differentiable at `√s`:
`v ↦ -ds_p v ρ'(√s) / (2 √s) + dt_p v / (2 √t)`. -/
theorem fderiv_shapeGraphOverR_comp_shape_apply {ρ : ℝ → ℝ}
    {p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)}
    (hρ : DifferentiableAt ℝ ρ (√(shape p).1)) (hs : 0 < (shape p).1) (ht : 0 < (shape p).2)
    (v : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    fderiv ℝ (shapeGraphOverR ρ ∘ shape) p v =
      -fderiv ℝ (fun q ↦ (shape q).1) p v * deriv ρ (√(shape p).1) / (2 * √(shape p).1) +
        fderiv ℝ (fun q ↦ (shape q).2) p v / (2 * √(shape p).2) := by
  have hH : DifferentiableAt ℝ (shapeGraphOverR ρ) (shape p) := by
    rw [shapeGraphOverR_eq_comp_fst_add_comp_snd]
    exact ((hρ.comp _ (Real.hasDerivAt_sqrt hs.ne').differentiableAt).neg.comp _
      differentiableAt_fst).add
      ((Real.hasDerivAt_sqrt ht.ne').differentiableAt.comp _ differentiableAt_snd)
  have h := fderiv_shapeGraphOverR_apply hρ hs ht (fderiv ℝ (fun q ↦ (shape q).1) p v)
    (fderiv ℝ (fun q ↦ (shape q).2) p v)
  rw [Prod.mk.eta] at h
  rw [fderiv_comp_shape_apply hH, h]

variable {ρ : ℝ → ℝ} {R : ℝ}

/-- The **`i`-convexity criterion for a shape over `R`** at `R`: `ρ : ℝ → ℝ` is positive at
`R > 0`, and, with `r = ρ R`, `d = ρ' R` and `e = ρ'' R`,
`0 < a (1 / r - d / R) + 2 b / r + S (d / R³ - e / R² - d² / (r R²))` for all `a, b, S ≥ 0`
with `a + b > 0`, `S ≤ R² a` and `(1 + d²) S ≤ R² (a + b)`.

The right side is four times the real part of the Levi form of `shapeGraphOverR ρ ∘ shape`
(`re_leviForm_comp_shape_apply_self`) on a complex tangent vector `v` of its level set through a
point with `shape p = (R ², r ²)`, written in `a = |v₁|²`, `b = |v₂|²` and `S = |σ|²`, where
`σ = ∑ⱼ xⱼ v₁ⱼ`; the conditions on `S` are the Cauchy–Schwarz bounds `norm_sum_re_mul_sq_le`
and `norm_ofReal_mul_add_ofReal_mul_sq_le` on such a vector. `isConvexShapeOverRAt_iff` reduces it
to three inequalities on `d` and `e`. -/
structure IsConvexShapeOverRAt (ρ : ℝ → ℝ) (R : ℝ) : Prop where
  pos : 0 < R
  pos_value : 0 < ρ R
  levi : ∀ a b S : ℝ, 0 ≤ a → 0 ≤ b → 0 < a + b → 0 ≤ S → S ≤ R ^ 2 * a →
    (1 + deriv ρ R ^ 2) * S ≤ R ^ 2 * (a + b) →
    0 < a * (1 / ρ R - deriv ρ R / R) + 2 * b / ρ R +
      S * (deriv ρ R / R ^ 3 - iteratedDeriv 2 ρ R / R ^ 2 - deriv ρ R ^ 2 / (ρ R * R ^ 2))

namespace IsConvexShapeOverRAt

/-- The case `a = 1`, `b = S = 0` of the criterion over `R`: `ρ' R / R < 1 / ρ R`, the analogue
of `IsConvexShapeAt.one_div_lt_deriv_div` for the inverse `ρ` of a shape `χ`. -/
theorem deriv_div_lt_one_div (h : IsConvexShapeOverRAt ρ R) : deriv ρ R / R < 1 / ρ R := by
  have := h.levi 1 0 0 zero_le_one le_rfl (by norm_num) le_rfl (by positivity)
    (by simp [sq_nonneg])
  simp only [one_mul, mul_zero, zero_div, add_zero, zero_mul] at this
  linarith

/-- The slope of a shape over `R` is less than `R / ρ R`, the analogue of
`IsConvexShapeAt.deriv_pos` for the inverse `ρ` of a shape `χ`. Unlike that slope, it need not
be positive. -/
theorem deriv_lt_div (h : IsConvexShapeOverRAt ρ R) : deriv ρ R < R / ρ R := by
  have := h.deriv_div_lt_one_div
  rw [div_lt_iff₀ h.pos] at this
  calc deriv ρ R < 1 / ρ R * R := this
    _ = R / ρ R := by ring

/-- The case `a = 1`, `b = 0` and `S = R² / (1 + ρ' R ²)` of the criterion over `R`:
`ρ'' R < 1 / ρ R - ρ' R ³ / R`. -/
theorem iteratedDeriv_two_lt (h : IsConvexShapeOverRAt ρ R) :
    iteratedDeriv 2 ρ R < 1 / ρ R - deriv ρ R ^ 3 / R := by
  have hR := h.pos
  have hr := h.pos_value
  have hq : 0 < 1 + deriv ρ R ^ 2 := by positivity
  have := h.levi 1 0 (R ^ 2 / (1 + deriv ρ R ^ 2)) zero_le_one le_rfl (by norm_num)
    (by positivity) (by rw [mul_one]; exact div_le_self (sq_nonneg R) (by nlinarith))
    (by field_simp; linarith)
  rw [← sub_pos]
  have e : 1 * (1 / ρ R - deriv ρ R / R) + 2 * 0 / ρ R + R ^ 2 / (1 + deriv ρ R ^ 2) *
      (deriv ρ R / R ^ 3 - iteratedDeriv 2 ρ R / R ^ 2 - deriv ρ R ^ 2 / (ρ R * R ^ 2)) =
      (1 / ρ R - deriv ρ R ^ 3 / R - iteratedDeriv 2 ρ R) / (1 + deriv ρ R ^ 2) := by
    field_simp
    ring
  rw [e] at this
  exact (div_pos_iff_of_pos_right hq).1 this

/-- The case `a = 1`, `b = ρ' R ²` and `S = R²` of the criterion over `R`:
`ρ'' R < (1 + ρ' R ²) / ρ R`. It follows from `iteratedDeriv_two_lt` where `-R / ρ R ≤ ρ' R`
(`isConvexShapeOverRAt_of_neg_div_le_deriv`). -/
theorem iteratedDeriv_two_lt_one_add_sq_div (h : IsConvexShapeOverRAt ρ R) :
    iteratedDeriv 2 ρ R < (1 + deriv ρ R ^ 2) / ρ R := by
  have hR := h.pos
  have hr := h.pos_value
  have := h.levi 1 (deriv ρ R ^ 2) (R ^ 2) zero_le_one (sq_nonneg _) (by positivity)
    (sq_nonneg _) (by rw [mul_one]) (by rw [mul_comm])
  rw [← sub_pos]
  have e : 1 * (1 / ρ R - deriv ρ R / R) + 2 * deriv ρ R ^ 2 / ρ R + R ^ 2 *
      (deriv ρ R / R ^ 3 - iteratedDeriv 2 ρ R / R ^ 2 - deriv ρ R ^ 2 / (ρ R * R ^ 2)) =
      (1 + deriv ρ R ^ 2) / ρ R - iteratedDeriv 2 ρ R := by
    field_simp
    ring
  rwa [e] at this

end IsConvexShapeOverRAt

/-- The criterion over `R` holds at `R` if and only if `0 < R`, `0 < ρ R`,
`ρ' R / R < 1 / ρ R`, `ρ'' R < 1 / ρ R - ρ' R ³ / R` and `ρ'' R < (1 + ρ' R ²) / ρ R`: the
inequality for all `a, b, S` amounts to its cases at the three extreme rays where it is not
obvious. -/
theorem isConvexShapeOverRAt_iff :
    IsConvexShapeOverRAt ρ R ↔ 0 < R ∧ 0 < ρ R ∧ deriv ρ R / R < 1 / ρ R ∧
      iteratedDeriv 2 ρ R < 1 / ρ R - deriv ρ R ^ 3 / R ∧
      iteratedDeriv 2 ρ R < (1 + deriv ρ R ^ 2) / ρ R := by
  refine ⟨fun h ↦ ⟨h.pos, h.pos_value, h.deriv_div_lt_one_div, h.iteratedDeriv_two_lt,
    h.iteratedDeriv_two_lt_one_add_sq_div⟩, fun ⟨hR, hr, h₁, h₂, h₃⟩ ↦
    ⟨hR, hr, fun a b S ha hb hab hS hSa hSab ↦ ?_⟩⟩
  set r := ρ R
  set d := deriv ρ R
  set e := iteratedDeriv 2 ρ R
  set K := d / R ^ 3 - e / R ^ 2 - d ^ 2 / (r * R ^ 2) with hK
  have hq : 0 < 1 + d ^ 2 := by positivity
  have hA : 0 < 1 / r - d / R := by linarith
  have hr₂ : 0 < 2 / r := by positivity
  -- Positive at `S = 0`, since `a + b > 0`.
  have h₀ : 0 < a * (1 / r - d / R) + 2 * b / r := by
    rcases ha.lt_or_eq with ha' | ha'
    · have := mul_pos ha' hA
      have : 0 ≤ 2 * b / r := by positivity
      linarith
    · rw [← ha'] at hab ⊢
      have hb' : 0 < b := by linarith
      have : 0 < 2 * b / r := by positivity
      linarith
  rcases le_or_gt 0 K with hK₀ | hK₀
  · nlinarith [mul_nonneg hS hK₀]
  -- For `K < 0` the expression is smallest at the largest `S`, which is
  -- `R² (a + b) / (1 + d²)` for `b ≤ d² a` and `R² a` for `b ≥ d² a`.
  have hB : 0 < 1 / r - d ^ 3 / R - e := by linarith
  have hC : 0 < (1 + d ^ 2) / r - e := by linarith
  rcases le_total b (d ^ 2 * a) with hbd | hbd
  · have ha' : 0 < a := by
      rcases ha.lt_or_eq with ha' | ha'
      · exact ha'
      · rw [← ha'] at hbd hab
        linarith
    have e₁ : (1 + d ^ 2) * (a * (1 / r - d / R) + 2 * b / r) + R ^ 2 * (a + b) * K =
        a * (1 / r - d ^ 3 / R - e) + b * ((2 + d ^ 2) / r + d / R - e) := by
      rw [hK]
      field_simp
      ring
    have e₂ : (1 / r - d ^ 3 / R - e) + d ^ 2 * ((2 + d ^ 2) / r + d / R - e) =
        (1 + d ^ 2) * ((1 + d ^ 2) / r - e) := by
      field_simp
      ring
    have h₄ : 0 < a * (1 / r - d ^ 3 / R - e) + b * ((2 + d ^ 2) / r + d / R - e) := by
      rcases le_or_gt 0 ((2 + d ^ 2) / r + d / R - e) with hC₀ | hC₀
      · nlinarith [mul_pos ha' hB, mul_nonneg hb hC₀]
      · have h₆ := mul_le_mul_of_nonpos_right hbd hC₀.le
        nlinarith [mul_pos ha' (mul_pos hq hC)]
    have h₅ : R ^ 2 * (a + b) * K ≤ (1 + d ^ 2) * S * K :=
      mul_le_mul_of_nonpos_right hSab hK₀.le
    have : 0 < (1 + d ^ 2) * (a * (1 / r - d / R) + 2 * b / r + S * K) := by nlinarith
    exact pos_of_mul_pos_right this hq.le
  · have h₅ : R ^ 2 * a * K ≤ S * K := mul_le_mul_of_nonpos_right hSa hK₀.le
    rcases ha.lt_or_eq with ha' | ha'
    · have e₃ : a * (1 / r - d / R) + 2 * (d ^ 2 * a) / r + R ^ 2 * a * K =
          a * ((1 + d ^ 2) / r - e) := by
        rw [hK]
        field_simp
        ring
      have h₆ : 2 * (d ^ 2 * a) / r ≤ 2 * b / r := by gcongr
      nlinarith [mul_pos ha' hC]
    · rw [← ha'] at h₅ ⊢
      nlinarith

/-- The criterion over `R` for a slope `ρ' R ≥ -R / ρ R`, in particular for a nondecreasing `ρ`:
it holds if `0 < R`, `0 < ρ R`, `ρ' R / R < 1 / ρ R` and `ρ'' R < 1 / ρ R - ρ' R ³ / R`. -/
theorem isConvexShapeOverRAt_of_neg_div_le_deriv (hR : 0 < R) (hr : 0 < ρ R)
    (hd : -R / ρ R ≤ deriv ρ R) (h₁ : deriv ρ R / R < 1 / ρ R)
    (h₂ : iteratedDeriv 2 ρ R < 1 / ρ R - deriv ρ R ^ 3 / R) : IsConvexShapeOverRAt ρ R := by
  refine isConvexShapeOverRAt_iff.2 ⟨hR, hr, h₁, h₂, h₂.trans_le ?_⟩
  -- The difference of the two bounds is `ρ' R ² (1 / ρ R + ρ' R / R)`.
  have hd' : 0 ≤ 1 / ρ R + deriv ρ R / R := by
    have : -(1 / ρ R) ≤ deriv ρ R / R := by
      rw [le_div_iff₀ hR]
      calc -(1 / ρ R) * R = -R / ρ R := by ring
        _ ≤ deriv ρ R := hd
    linarith
  have e : (1 + deriv ρ R ^ 2) / ρ R - (1 / ρ R - deriv ρ R ^ 3 / R) =
      deriv ρ R ^ 2 * (1 / ρ R + deriv ρ R / R) := by
    field_simp
    ring
  nlinarith [mul_nonneg (sq_nonneg (deriv ρ R)) hd']

/-- **The Levi form of a shape over `R`.** Let `ρ` be `C²` at `R` and satisfy the criterion over
`R` there, and let `p ∈ ℂᵏ × ℂᵐ` lie on the hypersurface `r = ρ (R)`,
`shape p = (R ², ρ R ²)`. Then the Levi form of `F = shapeGraphOverR ρ ∘ shape` at `p` is positive
on every nonzero `v` with `dF_p v = 0` and `dF_p (i v) = 0`, that is on the nonzero complex
tangent vectors of the level set of `F` through `p`. -/
theorem IsConvexShapeOverRAt.re_leviForm_pos (hρ : ContDiffAt ℝ 2 ρ R)
    (h : IsConvexShapeOverRAt ρ R)
    {p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)} (hp : shape p = (R ^ 2, ρ R ^ 2))
    {v : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)} (hv : v ≠ 0)
    (hv₁ : fderiv ℝ (shapeGraphOverR ρ ∘ shape) p v = 0)
    (hv₂ : fderiv ℝ (shapeGraphOverR ρ ∘ shape) p (I • v) = 0) :
    0 < (leviForm (shapeGraphOverR ρ ∘ shape) p v v).re := by
  have hR := h.pos
  have hr := h.pos_value
  have hl := h.levi
  have hsR : √(R ^ 2) = R := Real.sqrt_sq hR.le
  have hsr : √(ρ R ^ 2) = ρ R := Real.sqrt_sq hr.le
  have hρ' : ContDiffAt ℝ 2 ρ (√(R ^ 2)) := by rwa [hsR]
  have hs : 0 < R ^ 2 := by positivity
  have ht : 0 < ρ R ^ 2 := by positivity
  have hH : ContDiffAt ℝ 2 (shapeGraphOverR ρ) (shape p) :=
    hp ▸ contDiffAt_shapeGraphOverR hρ' hs ht
  set r := ρ R
  set d := deriv ρ R
  set e := iteratedDeriv 2 ρ R
  have hH₁ (a b : ℝ) :
      fderiv ℝ (shapeGraphOverR ρ) (shape p) (a, b) = -a * d / (2 * R) + b / (2 * r) := by
    rw [hp, fderiv_shapeGraphOverR_apply (hρ'.differentiableAt (by norm_num)) hs ht, hsR, hsr]
  have hH₂ (a b a' b' : ℝ) : fderiv ℝ (fderiv ℝ (shapeGraphOverR ρ)) (shape p) (a, b) (a', b') =
      a * a' * (d / (4 * R ^ 2 * R) - e / (4 * R ^ 2)) - b * b' / (4 * r ^ 2 * r) := by
    rw [hp, fderiv_fderiv_shapeGraphOverR_apply hρ' hs ht, hsR, hsr]
  -- On a complex tangency, `τ = (r d / R) σ`.
  obtain ⟨-, hL, hSa, hCS⟩ := re_leviForm_comp_shape_apply_self_of_fderiv_eq_zero hH
    (c := r * d / R) (by rw [hH₁, neg_zero, zero_mul, zero_div, zero_add]; positivity)
    (by rw [hH₁, hH₁]; field_simp; ring) hv₁ hv₂
  rw [hL, hH₁, hH₁, hH₂, hH₂, hH₂]
  rw [hp] at hSa hCS
  dsimp only at hSa hCS
  set S := ‖∑ j, ((p.1 j).re : ℂ) * v.1 j‖ ^ 2
  set a := ‖v.1‖ ^ 2
  set b := ‖v.2‖ ^ 2
  have hab : 0 < a + b := Prod.norm_fst_sq_add_norm_snd_sq_pos hv
  have hSab : (1 + d ^ 2) * S ≤ R ^ 2 * (a + b) := by
    have e₁ : r ^ 2 + (r * d / R) ^ 2 * R ^ 2 = r ^ 2 * (1 + d ^ 2) := by
      field_simp
    rw [e₁, mul_assoc, mul_comm (R ^ 2) (r ^ 2), mul_assoc] at hCS
    exact le_of_mul_le_mul_left hCS (by positivity)
  have := hl a b S (by positivity) (by positivity) hab (by positivity) hSa hSab
  convert div_pos this (by norm_num : (0 : ℝ) < 4) using 1
  field_simp
  ring

end SymplecticGeometry

end
