/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.Shape

import Mathlib.Analysis.InnerProductSpace.ProdL2
import SymplecticGeometry.Algebra.Order.Ring.Basic
import SymplecticGeometry.Analysis.Calculus.IteratedDeriv.Comp
import SymplecticGeometry.Analysis.Normed.Group.Prod
import SymplecticGeometry.Analysis.SpecialFunctions.SmoothedMax
import SymplecticGeometry.Analysis.SpecialFunctions.Sqrt
import TauCeti.Analysis.Calculus.FDeriv.Prod
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
  `1 / χ r < χ'' r + χ' r ³ / r`.
* `SymplecticGeometry.isConvexShapeAt_of_iteratedDeriv_two_nonpos`: a sufficient condition for
  a shape with `χ'' ≤ 0`. `SymplecticGeometry.IsConvexShapeAt.add_const` and
  `SymplecticGeometry.IsConvexShapeAt.rescale`: `χ + c` for `c ≥ 0`, and `ℓ χ (· / ℓ)` at `ℓ r`
  for `ℓ > 0`, are again `i`-convex shapes. The derivatives of the rescaled shape come from
  `iteratedDeriv_comp_div_const`, with no differentiability assumption on `χ`.
* `SymplecticGeometry.exists_isConvexShapeAt_eq_max`: two `i`-convex shapes on `[r₁, r₂]` have
  a common smoothing of their maximum, `r ↦ smoothedMax δ (χ₁ r) (χ₂ r)` for small `δ`, that is
  again an `i`-convex shape and is the maximum away from a given neighbourhood of their crossings.
  Its slope is a convex combination of theirs, which gives (4.3). For the case `σ = r` of (4.4)
  the cube of that slope falls short of the combination of the cubes by a multiple of
  `(χ₁' - χ₂')²` (`SymplecticGeometry.mul_pow_three_add_mul_pow_three_sub_pow_three_le`);
  where the weight is near `0` or `1` this is small, and elsewhere the term
  `(smoothedAbs δ)'' (χ₁' - χ₂')² / 2` of the second derivative, of order `1 / δ`
  (`SymplecticGeometry.exists_pos_div_le_iteratedDeriv_two_smoothedAbs`), makes up for it. So
  this route, unlike the book's quadratic bridge, needs no transversality of the crossings.
* `SymplecticGeometry.exists_isConvexShapeAt_eqOn_Iic_Ici`: the same smoothing, for shapes that
  cross only inside `(u, v) ⊆ [r₁, r₂]`, continued by the first shape to the left of `u` and the
  second to the right of `v`, which gives an `i`-convex shape that passes from one to the other,
  and stays one outside `[r₁, r₂]` wherever the shape it equals there is.
  It glues by `SymplecticGeometry.IsConvexShapeAt.congr_of_eventuallyEq`: being an `i`-convex
  shape at `r` only depends on the germ at `r`.
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

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  §4.2–4.3: (4.3) and (4.4), Proposition 4.8 (a), (b), Proposition 4.10, Corollary 4.11 (a),
  Lemma 4.13 (a), (b), (d) and Lemma 4.14 (a).
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
  have h₂ : iteratedDeriv 2 (fun r ↦ χ r + c) r = iteratedDeriv 2 χ r := by
    simp only [iteratedDeriv_succ, iteratedDeriv_zero, deriv_add_const']
  refine isConvexShapeAt_iff.2 ⟨h.pos, by linarith, ?_, ?_⟩
  · rw [deriv_add_const]
    exact hle.trans_lt h.one_div_lt_deriv_div
  · rw [deriv_add_const, h₂]
    exact hle.trans_lt h.one_div_lt_iteratedDeriv_add

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

/-! ### The smoothed maximum of two shapes -/

/-- The first inequality of `isConvexShapeAt_iff` for the smoothed maximum of two `i`-convex
shapes at `r`. -/
private theorem one_div_smoothedMax_lt_deriv_div {χ₁ χ₂ : ℝ → ℝ} {δ : ℝ} (h₁ : ContDiff ℝ 2 χ₁)
    (h₂ : ContDiff ℝ 2 χ₂) (hδ : 0 < δ) (hc₁ : IsConvexShapeAt χ₁ r)
    (hc₂ : IsConvexShapeAt χ₂ r) :
    1 / smoothedMax δ (χ₁ r) (χ₂ r) < deriv (fun r ↦ smoothedMax δ (χ₁ r) (χ₂ r)) r / r := by
  have hs := abs_le.1 (abs_smoothedSign_le_one δ (χ₁ r - χ₂ r))
  have hinv := one_div_smoothedMax_le hδ hc₁.pos_value hc₂.pos_value
  rw [(hasDerivAt_smoothedMax ((h₁.differentiable two_ne_zero) r).hasDerivAt
    ((h₂.differentiable two_ne_zero) r).hasDerivAt).deriv]
  set s := smoothedSign δ (χ₁ r - χ₂ r)
  set w := (1 + s) / 2 with hw
  have hw₀ : 0 ≤ w := by rw [hw]; linarith
  have hw₁ : w ≤ 1 := by rw [hw]; linarith
  rw [show (1 - s) / 2 = 1 - w by rw [hw]; ring] at hinv
  have e : (deriv χ₁ r + deriv χ₂ r + s * (deriv χ₁ r - deriv χ₂ r)) / 2 / r =
      w * (deriv χ₁ r / r) + (1 - w) * (deriv χ₂ r / r) := by rw [hw]; ring
  rw [e]
  rcases hw₀.lt_or_eq with hw₀' | hw₀'
  · nlinarith [mul_lt_mul_of_pos_left hc₁.one_div_lt_deriv_div hw₀',
      mul_le_mul_of_nonneg_left hc₂.one_div_lt_deriv_div.le (sub_nonneg.2 hw₁)]
  · rw [← hw₀'] at hinv ⊢
    linarith [hc₂.one_div_lt_deriv_div]

/-- The second inequality of `isConvexShapeAt_iff` for the smoothed maximum of two `i`-convex
shapes at `r`, given a margin `a` in it for both, upper bounds `G` and `Q` for the error made by
the cube of the slope, and `δ`, `ε`, `c` so small that the curvature `c / δ` of `smoothedAbs δ`
makes up for that error where the weight `smoothedSign δ (χ₁ r - χ₂ r)` is in `[-1 + ε, 1 - ε]`,
and `ε G < a` where it is not. -/
private theorem one_div_smoothedMax_lt_iteratedDeriv_add {χ₁ χ₂ : ℝ → ℝ} {δ a G Q c ε : ℝ}
    (h₁ : ContDiff ℝ 2 χ₁) (h₂ : ContDiff ℝ 2 χ₂) (hδ : 0 < δ) (hc₁ : IsConvexShapeAt χ₁ r)
    (hc₂ : IsConvexShapeAt χ₂ r) (hε : 0 < ε)
    (ha₁ : a ≤ iteratedDeriv 2 χ₁ r + deriv χ₁ r ^ 3 / r - 1 / χ₁ r)
    (ha₂ : a ≤ iteratedDeriv 2 χ₂ r + deriv χ₂ r ^ 3 / r - 1 / χ₂ r)
    (hG : (deriv χ₁ r - deriv χ₂ r) ^ 2 * ((deriv χ₁ r + deriv χ₂ r) / r) ≤ G)
    (hQ : (deriv χ₁ r + deriv χ₂ r) / r ≤ Q) (hεG : ε * G < a)
    (hc : |smoothedSign δ (χ₁ r - χ₂ r)| ≤ 1 - ε →
      c / δ ≤ iteratedDeriv 2 (smoothedAbs δ) (χ₁ r - χ₂ r))
    (hδQ : δ * Q ≤ c) :
    1 / smoothedMax δ (χ₁ r) (χ₂ r) < iteratedDeriv 2 (fun r ↦ smoothedMax δ (χ₁ r) (χ₂ r)) r +
      deriv (fun r ↦ smoothedMax δ (χ₁ r) (χ₂ r)) r ^ 3 / r := by
  have hr := hc₁.pos
  have hx := hc₁.deriv_pos
  have hy := hc₂.deriv_pos
  have hs := abs_le.1 (abs_smoothedSign_le_one δ (χ₁ r - χ₂ r))
  have hinv := one_div_smoothedMax_le hδ hc₁.pos_value hc₂.pos_value
  rw [(hasDerivAt_smoothedMax ((h₁.differentiable two_ne_zero) r).hasDerivAt
    ((h₂.differentiable two_ne_zero) r).hasDerivAt).deriv, iteratedDeriv_two_smoothedMax h₁ h₂]
  set x := deriv χ₁ r
  set y := deriv χ₂ r
  set s := smoothedSign δ (χ₁ r - χ₂ r)
  set p := iteratedDeriv 2 (smoothedAbs δ) (χ₁ r - χ₂ r)
  set w := (1 + s) / 2 with hw
  have hw₀ : 0 ≤ w := by rw [hw]; linarith
  have hw₁ : w ≤ 1 := by rw [hw]; linarith
  have hp : 0 ≤ p := iteratedDeriv_two_smoothedAbs_nonneg hδ.le _
  rw [show (1 - s) / 2 = 1 - w by rw [hw]; ring] at hinv
  rw [show (x + y + s * (x - y)) / 2 = w * x + (1 - w) * y by rw [hw]; ring]
  -- The cube of the slope falls short of the combination of the cubes by
  -- `E ≤ (1 - s²) / 2 · (x - y)² (x + y) / r`.
  set E := w * (x ^ 3 / r) + (1 - w) * (y ^ 3 / r) - (w * x + (1 - w) * y) ^ 3 / r with hE
  have hEle : E ≤ (1 - s ^ 2) / 2 * ((x - y) ^ 2 * ((x + y) / r)) := by
    have h := div_le_div_of_nonneg_right
      (mul_pow_three_add_mul_pow_three_sub_pow_three_le hw₀ hw₁ hx.le hy.le) hr.le
    convert h using 1
    · rw [hE]; ring
    · rw [hw]; ring
  have he : (iteratedDeriv 2 χ₁ r + iteratedDeriv 2 χ₂ r + s * (iteratedDeriv 2 χ₁ r -
      iteratedDeriv 2 χ₂ r) + p * (x - y) ^ 2) / 2 =
      w * iteratedDeriv 2 χ₁ r + (1 - w) * iteratedDeriv 2 χ₂ r + p * (x - y) ^ 2 / 2 := by
    rw [hw]; ring
  rw [he]
  suffices E < a + p * (x - y) ^ 2 / 2 by
    nlinarith [mul_le_mul_of_nonneg_left ha₁ hw₀,
      mul_le_mul_of_nonneg_left ha₂ (sub_nonneg.2 hw₁)]
  have hg : 0 ≤ (x - y) ^ 2 * ((x + y) / r) := by positivity
  by_cases hsε : |s| ≤ 1 - ε
  · -- Near a crossing, the curvature `p ≥ c / δ ≥ Q` of `smoothedAbs δ` makes up for `E`.
    have ha : 0 < a := lt_of_le_of_lt (mul_nonneg hε.le (hg.trans hG)) hεG
    have hpQ : Q ≤ p := le_trans ((le_div_iff₀ hδ).2 (by linarith)) (hc hsε)
    have : E ≤ p * (x - y) ^ 2 / 2 := by
      calc E ≤ (1 - s ^ 2) / 2 * ((x - y) ^ 2 * ((x + y) / r)) := hEle
        _ ≤ 1 / 2 * ((x - y) ^ 2 * p) := by
          gcongr
          · linarith [sq_nonneg s]
          · exact hQ.trans hpQ
        _ = p * (x - y) ^ 2 / 2 := by ring
    linarith
  · -- Away from a crossing, the weight is near `0` or `1` and `E ≤ ε G < a`.
    have hs₃ : (1 - s ^ 2) / 2 < ε := by
      rw [not_le] at hsε
      rcases le_or_gt 0 (1 - ε) with h | h
      · have : (1 - ε) ^ 2 < s ^ 2 := by
          rw [← sq_abs s]
          exact pow_lt_pow_left₀ hsε h two_ne_zero
        linarith [sq_nonneg ε]
      · linarith [sq_nonneg s]
    have : E ≤ ε * G := by
      calc E ≤ (1 - s ^ 2) / 2 * ((x - y) ^ 2 * ((x + y) / r)) := hEle
        _ ≤ ε * ((x - y) ^ 2 * ((x + y) / r)) := by gcongr
        _ ≤ ε * G := by gcongr
    linarith [mul_nonneg hp (sq_nonneg (x - y))]

/-- The pointwise step of `exists_isConvexShapeAt_eq_max`: at `r`, the smoothed maximum of two
`i`-convex shapes is one, under the hypotheses of
`one_div_smoothedMax_lt_iteratedDeriv_add`. -/
private theorem isConvexShapeAt_smoothedMax_of_le {χ₁ χ₂ : ℝ → ℝ} {δ a G Q c ε : ℝ}
    (h₁ : ContDiff ℝ 2 χ₁) (h₂ : ContDiff ℝ 2 χ₂) (hδ : 0 < δ) (hc₁ : IsConvexShapeAt χ₁ r)
    (hc₂ : IsConvexShapeAt χ₂ r) (hε : 0 < ε)
    (ha₁ : a ≤ iteratedDeriv 2 χ₁ r + deriv χ₁ r ^ 3 / r - 1 / χ₁ r)
    (ha₂ : a ≤ iteratedDeriv 2 χ₂ r + deriv χ₂ r ^ 3 / r - 1 / χ₂ r)
    (hG : (deriv χ₁ r - deriv χ₂ r) ^ 2 * ((deriv χ₁ r + deriv χ₂ r) / r) ≤ G)
    (hQ : (deriv χ₁ r + deriv χ₂ r) / r ≤ Q) (hεG : ε * G < a)
    (hc : |smoothedSign δ (χ₁ r - χ₂ r)| ≤ 1 - ε →
      c / δ ≤ iteratedDeriv 2 (smoothedAbs δ) (χ₁ r - χ₂ r))
    (hδQ : δ * Q ≤ c) :
    IsConvexShapeAt (fun r ↦ smoothedMax δ (χ₁ r) (χ₂ r)) r :=
  isConvexShapeAt_iff.2 ⟨hc₁.pos, hc₁.pos_value.trans_le
    ((le_max_left _ _).trans (max_le_smoothedMax hδ _ _)),
    one_div_smoothedMax_lt_deriv_div h₁ h₂ hδ hc₁ hc₂,
    one_div_smoothedMax_lt_iteratedDeriv_add h₁ h₂ hδ hc₁ hc₂ hε ha₁ ha₂ hG hQ hεG hc hδQ⟩

/-- **The smoothed maximum of two `i`-convex shapes.** Let `χ₁` and `χ₂` be `C²` and `i`-convex
shapes at every point of `[r₁, r₂]`, and let `O` be a neighbourhood of the set where they cross.
Then some `χ`, as smooth as `χ₁` and `χ₂` are (so at least `C²`), is an `i`-convex shape at every
point of `[r₁, r₂]` and equals `max (χ₁ r) (χ₂ r)` at the points of `[r₁, r₂]` outside `O`.

The function is `r ↦ smoothedMax δ (χ₁ r) (χ₂ r)` for `δ` small. Unlike the book's, this
statement does not ask that the shapes cross transversally. -/
theorem exists_isConvexShapeAt_eq_max {χ₁ χ₂ : ℝ → ℝ} {r₁ r₂ : ℝ} {O : Set ℝ}
    (h₁ : ContDiff ℝ 2 χ₁) (h₂ : ContDiff ℝ 2 χ₂)
    (hc₁ : ∀ r ∈ Set.Icc r₁ r₂, IsConvexShapeAt χ₁ r)
    (hc₂ : ∀ r ∈ Set.Icc r₁ r₂, IsConvexShapeAt χ₂ r)
    (hO : O ∈ 𝓝ˢ {r | χ₁ r = χ₂ r}) :
    ∃ χ : ℝ → ℝ, (∀ n : ℕ∞, ContDiff ℝ n χ₁ → ContDiff ℝ n χ₂ → ContDiff ℝ n χ) ∧
      (∀ r ∈ Set.Icc r₁ r₂, IsConvexShapeAt χ r) ∧
      ∀ r ∈ Set.Icc r₁ r₂ \ O, χ r = max (χ₁ r) (χ₂ r) := by
  obtain ⟨U, hU, hDU, hUO⟩ := mem_nhdsSet_iff_exists.1 hO
  have hd₁ := h₁.continuous_deriv one_le_two
  have hd₂ := h₂.continuous_deriv one_le_two
  have hr₀ : ∀ r ∈ Set.Icc r₁ r₂, r ≠ 0 := fun r hr ↦ (hc₁ r hr).pos.ne'
  -- A common margin `a` in the second inequality of `isConvexShapeAt_iff` for both shapes.
  have margin {χ : ℝ → ℝ} (h : ContDiff ℝ 2 χ) (hc : ∀ r ∈ Set.Icc r₁ r₂, IsConvexShapeAt χ r) :
      ∃ a > 0, ∀ r ∈ Set.Icc r₁ r₂, a ≤ iteratedDeriv 2 χ r + deriv χ r ^ 3 / r - 1 / χ r := by
    have hcont : ContinuousOn (fun r ↦ iteratedDeriv 2 χ r + deriv χ r ^ 3 / r - 1 / χ r)
        (Set.Icc r₁ r₂) :=
      ((h.continuous_iteratedDeriv 2 le_rfl).continuousOn.add
        (((h.continuous_deriv one_le_two).continuousOn.pow 3).div continuousOn_id hr₀)).sub
        (continuousOn_const.div h.continuous.continuousOn fun r hr ↦ (hc r hr).pos_value.ne')
    obtain ⟨a, ha, h⟩ := isCompact_Icc.exists_forall_le' hcont fun r hr ↦
      sub_pos.2 (hc r hr).one_div_lt_iteratedDeriv_add
    exact ⟨a, ha, h⟩
  obtain ⟨a₁, ha₁, hA₁⟩ := margin h₁ hc₁
  obtain ⟨a₂, ha₂, hA₂⟩ := margin h₂ hc₂
  -- Bounds on the error terms.
  have hcq : ContinuousOn (fun r ↦ (deriv χ₁ r + deriv χ₂ r) / r) (Set.Icc r₁ r₂) :=
    (hd₁.add hd₂).continuousOn.div continuousOn_id hr₀
  obtain ⟨Q, hQ⟩ := isCompact_Icc.exists_bound_of_continuousOn hcq
  obtain ⟨G, hG⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (((hd₁.sub hd₂).pow 2).continuousOn.mul hcq)
  have hG₀ : 0 ≤ |G| := abs_nonneg G
  set a := min a₁ a₂
  have ha : 0 < a := lt_min ha₁ ha₂
  set ε := a / (2 * (|G| + 1))
  have hε : 0 < ε := by positivity
  have hεG : ε * |G| < a := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  obtain ⟨c, hc, hcδ⟩ := exists_pos_div_le_iteratedDeriv_two_smoothedAbs hε
  -- A lower bound `β` for `|χ₁ - χ₂|` on `[r₁, r₂]` outside `U`.
  obtain ⟨β, hβ, hβD⟩ := (isCompact_Icc.diff hU).exists_forall_le'
    ((h₁.continuous.sub h₂.continuous).abs.continuousOn) fun r hr ↦
      abs_pos.2 (sub_ne_zero.2 fun h ↦ hr.2 (hDU h))
  set δ := min (c / (|Q| + 1)) β
  have hδ : 0 < δ := lt_min (by positivity) hβ
  refine ⟨fun r ↦ smoothedMax δ (χ₁ r) (χ₂ r), fun n hn₁ hn₂ ↦
    (contDiff_smoothedMax δ).comp (hn₁.prodMk hn₂), fun r hr ↦ ?_, fun r hr ↦ ?_⟩
  · refine isConvexShapeAt_smoothedMax_of_le h₁ h₂ hδ (hc₁ r hr) (hc₂ r hr) hε
      ((min_le_left _ _).trans (hA₁ r hr)) ((min_le_right _ _).trans (hA₂ r hr))
      ((Real.le_norm_self _).trans ((hG r hr).trans (le_abs_self G)))
      ((Real.le_norm_self _).trans ((hQ r hr).trans (le_abs_self Q))) hεG
      (hcδ δ hδ _) ?_
    calc δ * |Q| ≤ c / (|Q| + 1) * |Q| := by gcongr; exact min_le_left _ _
      _ ≤ c := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith
  · exact smoothedMax_eq_max hδ ((min_le_right _ _).trans
      (hβD r ⟨hr.1, fun h ↦ hr.2 (hUO h)⟩))

open Set in
/-- **Passing from one `i`-convex shape to another.** Let `χ₁` and `χ₂` be `Cⁿ`, `n ≥ 2`, and
`i`-convex shapes at every point of `[r₁, r₂]`, and let `r₁ < u < v < r₂`. Suppose that `χ₁` is
at least `χ₂` on `[r₁, u]`, at most `χ₂` on `[v, r₂]`, and that they cross in `[r₁, r₂]` only
inside `(u, v)`. Then some `Cⁿ` function `χ`, an `i`-convex shape at every point of `[r₁, r₂]`,
equals `χ₁` on `(-∞, u]` and `χ₂` on `[v, ∞)`. Outside `[r₁, r₂]` it is still an `i`-convex
shape where `χ₁` is, left of `u`, and where `χ₂` is, right of `v`.

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
      (∀ r, v < r → IsConvexShapeAt χ₂ r → IsConvexShapeAt χ r) := by
  have hn' : ((2 : ℕ∞) : WithTop ℕ∞) ≤ n := WithTop.coe_le_coe.2 hn
  obtain ⟨χ, hχs, hχc, hχ⟩ := exists_isConvexShapeAt_eq_max (O := Iio r₁ ∪ Ioo u v ∪ Ioi r₂)
    (h₁.of_le hn') (h₂.of_le hn') hc₁ hc₂
    (((isOpen_Iio.union isOpen_Ioo).union isOpen_Ioi).mem_nhdsSet.2 fun r (hr : χ₁ r = χ₂ r) ↦ by
      rcases lt_or_ge r r₁ with h | h
      · exact Or.inl (Or.inl h)
      rcases le_or_gt r r₂ with h' | h'
      · exact Or.inl (Or.inr (hcross r ⟨h, h'⟩ hr))
      · exact Or.inr h')
  replace hχs := hχs n h₁ h₂
  have hnot : ∀ r ∈ Icc r₁ r₂, (r ≤ u ∨ v ≤ r) → r ∉ Iio r₁ ∪ Ioo u v ∪ Ioi r₂ := by
    intro r hr h
    simp only [mem_union, mem_Iio, mem_Ioo, mem_Ioi]
    rintro ((h' | ⟨h', h''⟩) | h') <;> rcases h with h | h <;> linarith [hr.1, hr.2]
  have hχ₁ : ∀ r ∈ Icc r₁ u, χ r = χ₁ r := fun r hr ↦ by
    have hr' : r ∈ Icc r₁ r₂ := ⟨hr.1, by linarith [hr.2]⟩
    rw [hχ r ⟨hr', hnot r hr' (Or.inl hr.2)⟩, max_eq_left (hle₁ r hr)]
  have hχ₂ : ∀ r ∈ Icc v r₂, χ r = χ₂ r := fun r hr ↦ by
    have hr' : r ∈ Icc r₁ r₂ := ⟨by linarith [hr.1], hr.2⟩
    rw [hχ r ⟨hr', hnot r hr' (Or.inr hr.1)⟩, max_eq_right (hle₂ r hr)]
  -- Outside `[r₁, r₂]`, replace `χ` by `χ₁` on the left and by `χ₂` on the right.
  set ψ : ℝ → ℝ := fun r ↦ if r ≤ (r₁ + u) / 2 then χ₁ r else if r ≤ (v + r₂) / 2 then χ r
    else χ₂ r with hψ
  have e₁ : EqOn ψ χ₁ (Iic u) := fun r (hr : r ≤ u) ↦ by
    simp only [hψ]
    split_ifs with h h'
    · rfl
    · exact hχ₁ r ⟨by linarith, hr⟩
    · exfalso; linarith
  have e₂ : EqOn ψ χ₂ (Ici v) := fun r (hr : v ≤ r) ↦ by
    simp only [hψ]
    split_ifs with h h'
    · exfalso; linarith
    · exact hχ₂ r ⟨hr, by linarith⟩
    · rfl
  have e : EqOn ψ χ (Ioo r₁ r₂) := fun r hr ↦ by
    simp only [hψ]
    split_ifs with h h'
    · exact (hχ₁ r ⟨hr.1.le, by linarith⟩).symm
    · rfl
    · exact (hχ₂ r ⟨by linarith, hr.2.le⟩).symm
  have key : ∀ r, (ψ =ᶠ[𝓝 r] χ₁ ∧ r < u) ∨ (ψ =ᶠ[𝓝 r] χ ∧ r ∈ Ioo r₁ r₂) ∨
      (ψ =ᶠ[𝓝 r] χ₂ ∧ v < r) := fun r ↦ by
    rcases lt_or_ge r u with h | h
    · exact Or.inl ⟨(e₁.mono Iio_subset_Iic_self).eventuallyEq_of_mem (isOpen_Iio.mem_nhds h), h⟩
    rcases le_or_gt r v with h' | h'
    · have hr : r ∈ Ioo r₁ r₂ := ⟨by linarith, by linarith⟩
      exact Or.inr (Or.inl ⟨e.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hr), hr⟩)
    · exact Or.inr (Or.inr
        ⟨(e₂.mono Ioi_subset_Ici_self).eventuallyEq_of_mem (isOpen_Ioi.mem_nhds h'), h'⟩)
  refine ⟨ψ, contDiff_iff_contDiffAt.2 fun r ↦ ?_, fun r hr ↦ ?_, e₁, e₂,
    fun r hr h ↦ h.congr_of_eventuallyEq
      ((e₁.mono Iio_subset_Iic_self).eventuallyEq_of_mem (isOpen_Iio.mem_nhds hr)),
    fun r hr h ↦ h.congr_of_eventuallyEq
      ((e₂.mono Ioi_subset_Ici_self).eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hr))⟩
  · rcases key r with ⟨he, -⟩ | ⟨he, -⟩ | ⟨he, -⟩
    · exact h₁.contDiffAt.congr_of_eventuallyEq he
    · exact hχs.contDiffAt.congr_of_eventuallyEq he
    · exact h₂.contDiffAt.congr_of_eventuallyEq he
  · rcases key r with ⟨he, -⟩ | ⟨he, h⟩ | ⟨he, -⟩
    · exact (hc₁ r hr).congr_of_eventuallyEq he
    · exact (hχc r (Ioo_subset_Icc_self h)).congr_of_eventuallyEq he
    · exact (hc₂ r hr).congr_of_eventuallyEq he

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
    (WithLp.toLp 2 (fun j ↦ ((p.1 j).re : ℂ)), 0)
  rw [h0, zero_apply, fderiv_shape_fst_apply, fderiv_shape_snd_apply] at h1
  have hsum : ∑ j, (p.1 j).re * (p.1 j).re = χ r ^ 2 := by
    have h2 : (shape p).1 = χ r ^ 2 := by rw [hp]
    rw [shape_fst] at h2
    rw [← h2]
    exact Finset.sum_congr rfl fun j _ ↦ (sq _).symm
  simp only [ofReal_re, ofReal_im, mul_zero, Finset.sum_const_zero,
    inner_zero_right, zero_re, add_zero, hsum] at h1
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
