/-
      ring
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.Shape

import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.InnerProductSpace.ProdL2
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
* `SymplecticGeometry.shapeGraph χ`: the function `(s, t) ↦ χ (√t) - √s`, whose zero level,
  composed with `shape`, is the hypersurface of the shape.
* `SymplecticGeometry.IsConvexShapeAt.re_leviForm_pos`: if `χ` is `C²` at `r` and
  `IsConvexShapeAt χ r`, then at every `p` with `shape p = (χ r ², r ²)` the Levi form of
  `shapeGraph χ ∘ shape` is positive on the nonzero complex tangencies of its level set.

The proof evaluates `SymplecticGeometry.re_leviForm_comp_shape_apply_self`. On a complex tangency
`v` the Wirtinger derivatives `σ = ∂s v` and `τ = ∂t v` are proportional, `τ = r / (R χ') σ`, and
a Cauchy–Schwarz bound for a combination of `σ` and `τ` bounds `|σ|²` by `|v|²`; this takes the
place of the book's splitting of the complex tangency into the two parts on which it computes
the Levi form separately, and of its passage from `k = n` to `k < n`, where the extra directions
only need `χ' > 0`.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  §4.2–4.3: (4.3) and (4.4), Proposition 4.8 (a), (b), Proposition 4.10 and Lemma 4.14 (a).
-/

public section

noncomputable section

namespace SymplecticGeometry

open TauCeti Complex ComplexConjugate
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
  have hq : ContDiffAt ℝ 2 (fun t ↦ √t) t := Real.contDiffAt_sqrt ht.ne'
  have hg : ContDiffAt ℝ 2 (χ ∘ fun t ↦ √t) t := hχ.comp t hq
  have h2f : iteratedDeriv 2 (fun s ↦ -√s) s = 1 / (4 * s * √s) := by
    rw [iteratedDeriv_fun_neg, Real.iteratedDeriv_two_sqrt hs]
    ring
  have h2g : iteratedDeriv 2 (χ ∘ fun t ↦ √t) t =
      iteratedDeriv 2 χ (√t) / (4 * t) - deriv χ (√t) / (4 * t * √t) := by
    rw [iteratedDeriv_comp_two hχ hq, Real.iteratedDeriv_two_sqrt ht,
      (Real.hasDerivAt_sqrt ht.ne').deriv]
    have hsq : √t ^ 2 = t := Real.sq_sqrt ht.le
    have : 0 < √t := Real.sqrt_pos.2 ht
    field_simp
    linear_combination (-4 * iteratedDeriv 2 χ (√t)) * hsq
  rw [shapeGraph_eq_comp_fst_add_comp_snd, fderiv_fderiv_comp_fst_add_comp_snd hf hg]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.coe_prodMap', Prod.map_fst, Prod.map_snd,
    ContinuousLinearMap.coprodEquivL_apply_apply,
    fderiv_fderiv_apply_eq_smul_iteratedDeriv, h2f, h2g,
    smul_eq_mul]
  ring

variable {k m : ℕ}

/-- The Cauchy–Schwarz bound `|c₁ σ + c₂ τ|² ≤ (c₁² s + c₂² t) |v|²` for real `c₁`, `c₂`, where
`σ = ∑ⱼ xⱼ v₁ⱼ` and `τ = ⟪w, v₂⟫ - i ∑ⱼ yⱼ v₁ⱼ` at `p = (x + i y, w)`: the combination is the
inner product of `v` with `(c₁ x + i c₂ y, c₂ w)`, whose real and imaginary parts are
orthogonal. -/
private theorem norm_smul_add_smul_sq_le (c₁ c₂ : ℝ)
    (p v : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    ‖(c₁ : ℂ) * ∑ j, ((p.1 j).re : ℂ) * v.1 j +
        (c₂ : ℂ) * (⟪p.2, v.2⟫_ℂ - I * ∑ j, ((p.1 j).im : ℂ) * v.1 j)‖ ^ 2 ≤
      (c₁ ^ 2 * (shape p).1 + c₂ ^ 2 * (shape p).2) * (‖v.1‖ ^ 2 + ‖v.2‖ ^ 2) := by
  let Y : EuclideanSpace ℂ (Fin k) :=
    WithLp.toLp 2 fun j ↦ (c₁ : ℂ) * ((p.1 j).re : ℂ) + I * ((c₂ : ℂ) * ((p.1 j).im : ℂ))
  let X : WithLp 2 (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :=
    WithLp.toLp 2 (Y, (c₂ : ℂ) • p.2)
  let u : WithLp 2 (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) := WithLp.toLp 2 v
  have hX : ⟪X, u⟫_ℂ = (c₁ : ℂ) * ∑ j, ((p.1 j).re : ℂ) * v.1 j +
      (c₂ : ℂ) * (⟪p.2, v.2⟫_ℂ - I * ∑ j, ((p.1 j).im : ℂ) * v.1 j) := by
    simp only [X, Y, u, WithLp.prod_inner_apply, PiLp.inner_apply, inner_smul_left,
      RCLike.inner_apply, map_add, map_mul, conj_ofReal, conj_I, Finset.mul_sum, mul_sub]
    have e : ∑ j, v.1 j * ((c₁ : ℂ) * ((p.1 j).re : ℂ) + -I * ((c₂ : ℂ) * ((p.1 j).im : ℂ))) =
        ∑ j, (c₁ : ℂ) * (((p.1 j).re : ℂ) * v.1 j) -
          ∑ j, (c₂ : ℂ) * (I * (((p.1 j).im : ℂ) * v.1 j)) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    rw [e]
    ring
  have hXn : ‖X‖ ^ 2 = c₁ ^ 2 * (shape p).1 + c₂ ^ 2 * (shape p).2 := by
    simp only [X, Y, WithLp.prod_norm_sq_eq_of_L2, EuclideanSpace.norm_sq_eq, norm_smul,
      shape_fst, shape_snd, Complex.sq_norm, normSq_apply, mul_pow, Finset.mul_sum, mul_add,
      WithLp.toLp_fst, WithLp.toLp_snd, Real.norm_eq_abs, sq_abs,
      Complex.norm_real]
    rw [← add_assoc, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im]
    ring
  have hun : ‖u‖ ^ 2 = ‖v.1‖ ^ 2 + ‖v.2‖ ^ 2 := by
    simp [u, WithLp.prod_norm_sq_eq_of_L2]
  rw [← hX, ← hXn, ← hun, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm X u) 2

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
  have htan (u : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
      fderiv ℝ (shapeGraph χ ∘ shape) p u =
        -fderiv ℝ (fun q ↦ (shape q).1) p u / (2 * χ r) +
          fderiv ℝ (fun q ↦ (shape q).2) p u * deriv χ r / (2 * r) := by
    rw [fderiv_comp p (hH.differentiableAt (by norm_num))
      ((contDiff_shape (n := 1)).differentiable one_ne_zero p), ContinuousLinearMap.comp_apply,
      fderiv_shape_apply, hp, fderiv_shapeGraph_apply (hχ'.differentiableAt (by norm_num)) hs ht,
      hsR, hsr]
  rw [htan, fderiv_shape_fst_apply, fderiv_shape_snd_apply] at hv₁ hv₂
  rw [re_leviForm_comp_shape_apply_self hH v, hp,
    fderiv_shapeGraph_apply (hχ'.differentiableAt (by norm_num)) hs ht,
    fderiv_shapeGraph_apply (hχ'.differentiableAt (by norm_num)) hs ht,
    fderiv_fderiv_shapeGraph_apply hχ' hs ht, fderiv_fderiv_shapeGraph_apply hχ' hs ht,
    fderiv_fderiv_shapeGraph_apply hχ' hs ht, hsR, hsr]
  set σ := ∑ j, ((p.1 j).re : ℂ) * v.1 j with hσ
  set τ := ⟪p.2, v.2⟫_ℂ - I * ∑ j, ((p.1 j).im : ℂ) * v.1 j with hτ
  have hσre : σ.re = ∑ j, (p.1 j).re * (v.1 j).re := by simp [hσ, re_sum]
  have hσim : σ.im = ∑ j, (p.1 j).re * (v.1 j).im := by simp [hσ, im_sum]
  have hτre : τ.re = ∑ j, (p.1 j).im * (v.1 j).im + (⟪p.2, v.2⟫_ℂ).re := by
    simp [hτ, re_sum, add_comm]
  have hτim : τ.im = (⟪p.2, v.2⟫_ℂ).im - ∑ j, (p.1 j).im * (v.1 j).re := by
    simp [hτ, im_sum]
  simp only [Prod.smul_fst, Prod.smul_snd, PiLp.smul_apply, smul_eq_mul, inner_smul_right,
    mul_re, mul_im, I_re, I_im, zero_mul, one_mul, zero_sub, mul_neg, Finset.sum_neg_distrib,
    zero_add] at hv₂
  set R := χ r
  set d := deriv χ r
  set e := iteratedDeriv 2 χ r
  -- On a complex tangency, `τ = λ σ` with `λ = r / (χ' R)`.
  set l := r / (d * R) with hl
  have hre : τ.re = l * σ.re := by
    have e₁ : τ.re * d / r = σ.re / R := by
      rw [hσre, hτre]
      linear_combination hv₁
    rw [hl]
    field_simp at e₁ ⊢
    linarith
  have him : τ.im = l * σ.im := by
    have e₁ : τ.im * d / r = σ.im / R := by
      rw [hσim, hτim]
      linear_combination -hv₂
    rw [hl]
    field_simp at e₁ ⊢
    linarith
  have hτσ : τ = (l : ℂ) * σ := Complex.ext (by simpa using hre) (by simpa using him)
  have hττ : ‖τ‖ ^ 2 = l ^ 2 * ‖σ‖ ^ 2 := by
    rw [hτσ, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  -- Cauchy–Schwarz for `σ + (R / (χ' r)) τ = (1 + 1 / χ'²) σ`.
  have hCS := norm_smul_add_smul_sq_le 1 (R / (d * r)) p v
  rw [← hσ, ← hτ, hp, hτσ] at hCS
  have hcl : R / (d * r) * l = 1 / d ^ 2 := by
    rw [hl]
    field_simp
  have hc : (((1 : ℝ) : ℂ) * σ + ((R / (d * r) : ℝ) : ℂ) * ((l : ℂ) * σ)) =
      ((1 + 1 / d ^ 2 : ℝ) : ℂ) * σ := by
    rw [← hcl]
    push_cast
    ring
  rw [hc, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs] at hCS
  set S := ‖σ‖ ^ 2
  set a := ‖v.1‖ ^ 2 with ha
  set b := ‖v.2‖ ^ 2 with hb
  have hS : 0 ≤ S := by positivity
  have ha₀ : 0 ≤ a := by positivity
  have hb₀ : 0 ≤ b := by positivity
  have hab : 0 < a + b := by
    by_contra hab
    refine hv (Prod.ext ?_ ?_)
    · simpa [ha] using (show a = 0 by linarith)
    · simpa [hb] using (show b = 0 by linarith)
  have hX : 0 ≤ d ^ 2 * R ^ 2 * (a + b) - (1 + d ^ 2) * S := by
    have h1 : 0 < 1 + 1 / d ^ 2 := by positivity
    have h2 : (1 + 1 / d ^ 2) * S ≤ R ^ 2 * (a + b) := by
      have : (1 + 1 / d ^ 2) * ((1 + 1 / d ^ 2) * S) ≤ (1 + 1 / d ^ 2) * (R ^ 2 * (a + b)) := by
        convert hCS using 1
        · ring
        · field_simp
      exact le_of_mul_le_mul_left this h1
    have : (1 + d ^ 2) * S = d ^ 2 * ((1 + 1 / d ^ 2) * S) := by
      field_simp
      ring
    rw [this]
    nlinarith [sq_nonneg d]
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
  rw [hττ]
  convert div_pos hN (by positivity : (0 : ℝ) < 4 * R ^ 2 * d ^ 2) using 1
  rw [hl]
  field_simp
  ring

end SymplecticGeometry

end
