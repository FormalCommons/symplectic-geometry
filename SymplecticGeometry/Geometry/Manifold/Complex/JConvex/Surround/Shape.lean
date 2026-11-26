/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.Manifold.Complex.LeviForm

import SymplecticGeometry.Algebra.Order.Ring.Basic
import SymplecticGeometry.Analysis.Complex.LeviForm.Prod
import Mathlib.Analysis.InnerProductSpace.ProdL2
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Complex.QuadraticLeviForm

/-!
# Shape functions

On `V = ℂᵏ × ℂᵐ`, with points `p = (x + i y, w)`, the *shape coordinates* are
`s = |x|²` and `t = |y|² + |w|²`. Functions of `(s, t)` are the model functions with which the
`J`-convex surrounding of a totally real disc is built: the disc is the real part `ℝᵏ`, where
`t = 0`. This file computes their Levi forms and gives a criterion for the strict
plurisubharmonicity of `f(s) + g(t)`.

## Main definitions

* `SymplecticGeometry.shape p`: the pair `(s p, t p)`.

## Main results

* `SymplecticGeometry.leviForm_shape_fst_apply`, `SymplecticGeometry.leviForm_shape_snd_apply`:
  the Levi forms of `s` and `t` are `⟪v₁, w₁⟫ / 2` and `⟪v₁, w₁⟫ / 2 + ⟪v₂, w₂⟫`.
* `SymplecticGeometry.re_leviForm_comp_shape_apply_self`: for `h` of class `C²`, the Levi form of
  `h ∘ shape` on `v` in terms of the partial derivatives of `h` and of
  `σ = ∑ⱼ xⱼ v₁ⱼ` and `τ = ⟪w, v₂⟫ - i ∑ⱼ yⱼ v₁ⱼ`, which are the Wirtinger derivatives
  `∂s v` and `∂t v`.
* `SymplecticGeometry.isManifoldStrictlyPlurisubharmonicAt_shape`: with `u⁻ = min u 0`, if
  `f' + g' + 2 f''⁻ s + 2 g''⁻ t > 0` and, when `m ≠ 0`, `g' + 2 g''⁻ t > 0`, then
  `f(s) + g(t)` is strictly plurisubharmonic. The flat form is
  `SymplecticGeometry.isStrictlyPlurisubharmonicAt_shape`.

The Levi form of `h ∘ shape` comes from `TauCeti.re_leviForm_comp_prodMk_apply_self` and the Levi
forms of `s` and `t`, which Tau Ceti's `TauCeti.leviForm_re_sq_comp_apply` and
`TauCeti.leviForm_norm_sq_comp_apply` give. The criterion follows from it by the Cauchy–Schwarz
bounds `|σ|² ≤ s |v₁|²` and `|τ|² ≤ t (|v₁|² + |v₂|²)`.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Chapter 4 (shapes of `i`-convex hypersurfaces)
-/

public section

open Complex ComplexConjugate TauCeti
open scoped InnerProductSpace

namespace SymplecticGeometry

variable {k m : ℕ}

/-- The **shape coordinates** on `ℂᵏ × ℂᵐ`: at `p = (x + i y, w)`, the pair `(s, t)` with
`s = |x|²` and `t = |y|² + |w|²`. -/
noncomputable def shape (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) : ℝ × ℝ :=
  (∑ j, (p.1 j).re ^ 2, ∑ j, (p.1 j).im ^ 2 + ‖p.2‖ ^ 2)

theorem shape_def (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    shape p = (∑ j, (p.1 j).re ^ 2, ∑ j, (p.1 j).im ^ 2 + ‖p.2‖ ^ 2) :=
  (rfl)

@[simp]
theorem shape_fst (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    (shape p).1 = ∑ j, (p.1 j).re ^ 2 := by
  rw [shape_def]

@[simp]
theorem shape_snd (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    (shape p).2 = ∑ j, (p.1 j).im ^ 2 + ‖p.2‖ ^ 2 := by
  rw [shape_def]

theorem shape_fst_nonneg (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    0 ≤ (shape p).1 := by
  rw [shape_fst]
  positivity

theorem shape_snd_nonneg (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    0 ≤ (shape p).2 := by
  rw [shape_snd]
  positivity

/-- The complex-linear functional `(z, w) ↦ c * z j` on `ℂᵏ × ℂᵐ`. -/
private noncomputable def coordCLM (c : ℂ) (j : Fin k) :
    EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) →L[ℂ] ℂ :=
  c • (EuclideanSpace.proj j ∘L ContinuousLinearMap.fst ℂ _ _)

private theorem coordCLM_apply (c : ℂ) (j : Fin k)
    (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    coordCLM c j p = c * p.1 j := by
  simp [coordCLM]

private theorem shape_fst_eq :
    (fun p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) ↦ (shape p).1) =
      ∑ j, fun p ↦ (coordCLM 1 j p).re ^ 2 := by
  funext p
  simp [coordCLM_apply]

private theorem shape_snd_eq :
    (fun p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) ↦ (shape p).2) =
      (∑ j, fun p ↦ (coordCLM (-I) j p).re ^ 2) +
        fun p ↦ ‖ContinuousLinearMap.snd ℂ _ _ p‖ ^ 2 := by
  funext p
  simp [coordCLM_apply]

private theorem contDiff_coordCLM_re_sq {n : WithTop ℕ∞} (c : ℂ) (j : Fin k) :
    ContDiff ℝ n fun p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) ↦
      (coordCLM c j p).re ^ 2 :=
  ((reCLM.contDiff.comp ((coordCLM c j).restrictScalars ℝ).contDiff).pow 2)

private theorem contDiff_norm_sq_snd {n : WithTop ℕ∞} :
    ContDiff ℝ n fun p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) ↦
      ‖ContinuousLinearMap.snd ℂ _ _ p‖ ^ 2 :=
  (contDiff_norm_sq ℝ).comp contDiff_snd

private theorem contDiff_sum_coordCLM_re_sq {n : WithTop ℕ∞} (c : ℂ) :
    ContDiff ℝ n (∑ j, fun p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) ↦
      (coordCLM c j p).re ^ 2) := by
  rw [Finset.sum_fn]
  exact ContDiff.sum fun j _ ↦ contDiff_coordCLM_re_sq c j

/-- The shape coordinates are smooth. -/
theorem contDiff_shape {n : WithTop ℕ∞} :
    ContDiff ℝ n (shape : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) → ℝ × ℝ) := by
  have h1 : ContDiff ℝ n fun p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) ↦
      (shape p).1 := by
    rw [shape_fst_eq]
    exact contDiff_sum_coordCLM_re_sq 1
  have h2 : ContDiff ℝ n fun p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) ↦
      (shape p).2 := by
    rw [shape_snd_eq]
    exact (contDiff_sum_coordCLM_re_sq (-I)).add contDiff_norm_sq_snd
  exact h1.prodMk h2

/-- The Levi form of `s = |x|²` on `ℂᵏ × ℂᵐ` is `⟪v₁, w₁⟫ / 2`. -/
theorem leviForm_shape_fst_apply (p v w : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    leviForm (fun q ↦ (shape q).1) p v w = ⟪v.1, w.1⟫_ℂ / 2 := by
  rw [shape_fst_eq, leviForm_sum _ fun j _ ↦ (contDiff_coordCLM_re_sq 1 j).contDiffAt]
  simp only [LinearMap.sum_apply, leviForm_re_sq_comp_apply]
  simp [coordCLM_apply, PiLp.inner_apply, Finset.sum_div]

/-- The Levi form of `t = |y|² + |w|²` on `ℂᵏ × ℂᵐ` is `⟪v₁, w₁⟫ / 2 + ⟪v₂, w₂⟫`. -/
theorem leviForm_shape_snd_apply (p v w : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    leviForm (fun q ↦ (shape q).2) p v w = ⟪v.1, w.1⟫_ℂ / 2 + ⟪v.2, w.2⟫_ℂ := by
  rw [shape_snd_eq, leviForm_add (contDiff_sum_coordCLM_re_sq (-I)).contDiffAt
    contDiff_norm_sq_snd.contDiffAt,
    leviForm_sum _ fun j _ ↦ (contDiff_coordCLM_re_sq (-I) j).contDiffAt]
  simp only [LinearMap.add_apply, LinearMap.sum_apply,
    leviForm_re_sq_comp_apply, leviForm_norm_sq_comp_apply]
  simp only [coordCLM_apply, PiLp.inner_apply, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [RCLike.inner_apply, map_mul, map_neg, conj_I]
  linear_combination (-(w.1 j * conj (v.1 j)) / 2) * I_sq

/-- The differential of `s = |x|²` at `p = (x + i y, w)` is `v ↦ 2 ∑ⱼ xⱼ Re v₁ⱼ`. -/
theorem fderiv_shape_fst_apply (p v : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    fderiv ℝ (fun q ↦ (shape q).1) p v = 2 * ∑ j, (p.1 j).re * (v.1 j).re := by
  have h (j : Fin k) : HasFDerivAt (fun q ↦ (coordCLM (m := m) 1 j q).re ^ 2)
      ((2 * (coordCLM 1 j p).re) • (reCLM.restrictScalars ℝ ∘L (coordCLM 1 j).restrictScalars ℝ))
      p := by
    simpa using ((reCLM.restrictScalars ℝ ∘L (coordCLM (m := m) 1 j).restrictScalars ℝ)
      |>.hasFDerivAt (x := p)).pow 2
  rw [shape_fst_eq, (HasFDerivAt.sum fun j _ ↦ h j).fderiv]
  simp [coordCLM_apply, Finset.mul_sum, mul_assoc]

/-- The differential of `t = |y|² + |w|²` at `p = (x + i y, w)` is
`v ↦ 2 (∑ⱼ yⱼ Im v₁ⱼ + Re ⟪w, v₂⟫)`. -/
theorem fderiv_shape_snd_apply (p v : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    fderiv ℝ (fun q ↦ (shape q).2) p v =
      2 * (∑ j, (p.1 j).im * (v.1 j).im + (⟪p.2, v.2⟫_ℂ).re) := by
  have h (j : Fin k) : HasFDerivAt (fun q ↦ (coordCLM (m := m) (-I) j q).re ^ 2)
      ((2 * (coordCLM (-I) j p).re) •
        (reCLM.restrictScalars ℝ ∘L (coordCLM (-I) j).restrictScalars ℝ)) p := by
    simpa using ((reCLM.restrictScalars ℝ ∘L (coordCLM (m := m) (-I) j).restrictScalars ℝ)
      |>.hasFDerivAt (x := p)).pow 2
  have h₂ : HasFDerivAt (fun q ↦ ‖ContinuousLinearMap.snd ℂ (EuclideanSpace ℂ (Fin k))
      (EuclideanSpace ℂ (Fin m)) q‖ ^ 2)
      ((2 : ℕ) • (innerSL ℝ p.2 ∘L ContinuousLinearMap.snd ℝ _ _)) p := by
    simpa using (hasFDerivAt_snd (𝕜 := ℝ) (p := p)).norm_sq
  rw [shape_snd_eq, ((HasFDerivAt.sum fun j _ ↦ h j).add h₂).fderiv]
  simp [coordCLM_apply, PiLp.inner_apply, Complex.re_sum, Finset.mul_sum, mul_add, mul_assoc]

/-- **The Levi form of a function of the shape coordinates.** Let `h : ℝ × ℝ → ℝ` be `C²` at
`(s, t) = shape p`, with `p = (x + i y, w)`, and write `hₛ`, `hₜ` for its first and `hₛₛ`, `hₛₜ`,
`hₜₜ` for its second partial derivatives there. For `v = (v₁, v₂)`, put `σ = ∑ⱼ xⱼ v₁ⱼ` and
`τ = ⟪w, v₂⟫ - i ∑ⱼ yⱼ v₁ⱼ`. Then the real part of the Levi form of `h ∘ shape` at `p` on `v` is
`hₛ |v₁|² / 2 + hₜ (|v₁|² / 2 + |v₂|²) + hₛₛ |σ|² + 2 hₛₜ Re (conj σ τ) + hₜₜ |τ|²`. -/
theorem re_leviForm_comp_shape_apply_self {h : ℝ × ℝ → ℝ}
    {p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)} (hh : ContDiffAt ℝ 2 h (shape p))
    (v : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    (leviForm (h ∘ shape) p v v).re =
      fderiv ℝ h (shape p) (1, 0) * (‖v.1‖ ^ 2 / 2) +
        fderiv ℝ h (shape p) (0, 1) * (‖v.1‖ ^ 2 / 2 + ‖v.2‖ ^ 2) +
        fderiv ℝ (fderiv ℝ h) (shape p) (1, 0) (1, 0) * ‖∑ j, ((p.1 j).re : ℂ) * v.1 j‖ ^ 2 +
        2 * fderiv ℝ (fderiv ℝ h) (shape p) (1, 0) (0, 1) *
          (conj (∑ j, ((p.1 j).re : ℂ) * v.1 j) *
            (⟪p.2, v.2⟫_ℂ - I * ∑ j, ((p.1 j).im : ℂ) * v.1 j)).re +
        fderiv ℝ (fderiv ℝ h) (shape p) (0, 1) (0, 1) *
          ‖⟪p.2, v.2⟫_ℂ - I * ∑ j, ((p.1 j).im : ℂ) * v.1 j‖ ^ 2 := by
  have hcomp : h ∘ shape = fun q : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) ↦
      h ((shape q).1, (shape q).2) := by
    funext q
    simp only [Function.comp_apply, Prod.mk.eta]
  -- The second derivative of `h` is symmetric, so on `(a, b)` it is `a² hₛₛ + 2 a b hₛₜ + b² hₜₜ`.
  have hsymm := hh.isSymmSndFDerivAt (by simp)
  have hB (a b : ℝ) : fderiv ℝ (fderiv ℝ h) (shape p) (a, b) (a, b) =
      a ^ 2 * fderiv ℝ (fderiv ℝ h) (shape p) (1, 0) (1, 0) +
        2 * a * b * fderiv ℝ (fderiv ℝ h) (shape p) (1, 0) (0, 1) +
        b ^ 2 * fderiv ℝ (fderiv ℝ h) (shape p) (0, 1) (0, 1) := by
    have hab : ((a, b) : ℝ × ℝ) = a • ((1 : ℝ), (0 : ℝ)) + b • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [hab]
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
    rw [hsymm (0, 1) (1, 0)]
    ring
  have hre {n : ℕ} (u : EuclideanSpace ℂ (Fin n)) : (⟪u, u⟫_ℂ).re = ‖u‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) u
  rw [hcomp, re_leviForm_comp_prodMk_apply_self (by rwa [Prod.mk.eta])
    (contDiff_shape.fst.contDiffAt) (contDiff_shape.snd.contDiffAt) v]
  simp only [Prod.mk.eta, leviForm_shape_fst_apply, leviForm_shape_snd_apply]
  rw [hB (fderiv ℝ (fun q ↦ (shape q).1) p v),
    hB (fderiv ℝ (fun q ↦ (shape q).1) p (I • v)),
    fderiv_shape_fst_apply, fderiv_shape_fst_apply, fderiv_shape_snd_apply,
    fderiv_shape_snd_apply]
  simp only [Prod.smul_fst, Prod.smul_snd, PiLp.smul_apply, smul_eq_mul, inner_smul_right,
    hre, Complex.sq_norm, normSq_apply, mul_re, mul_im, sub_re, sub_im,
    conj_re, conj_im, re_sum, im_sum, ofReal_re, ofReal_im, I_re, I_im, add_re, div_ofNat_re,
    zero_mul, one_mul, zero_sub, sub_zero, mul_neg, Finset.sum_neg_distrib]
  ring_nf

/-- The bound `|σ|² ≤ s |v₁|²` for `σ = ∑ⱼ xⱼ v₁ⱼ`, by Cauchy–Schwarz. -/
private theorem norm_sum_re_mul_sq_le (p v : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    ‖∑ j, ((p.1 j).re : ℂ) * v.1 j‖ ^ 2 ≤ (shape p).1 * ‖v.1‖ ^ 2 := by
  let X : EuclideanSpace ℂ (Fin k) := WithLp.toLp 2 fun j ↦ ((p.1 j).re : ℂ)
  have hX : ⟪X, v.1⟫_ℂ = ∑ j, ((p.1 j).re : ℂ) * v.1 j := by
    simp [X, PiLp.inner_apply, mul_comm]
  have hXn : ‖X‖ ^ 2 = (shape p).1 := by
    simp [X, EuclideanSpace.norm_sq_eq]
  rw [← hX, ← hXn, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm X v.1) 2

/-- The bound `|τ|² ≤ t (|v₁|² + |v₂|²)` for `τ = ⟪w, v₂⟫ - i ∑ⱼ yⱼ v₁ⱼ`, by Cauchy–Schwarz in
the `L²` product. -/
private theorem norm_inner_sub_I_mul_sum_sq_le
    (p v : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    ‖⟪p.2, v.2⟫_ℂ - I * ∑ j, ((p.1 j).im : ℂ) * v.1 j‖ ^ 2 ≤
      (shape p).2 * (‖v.1‖ ^ 2 + ‖v.2‖ ^ 2) := by
  let Y : EuclideanSpace ℂ (Fin k) := WithLp.toLp 2 fun j ↦ I * ((p.1 j).im : ℂ)
  let X : WithLp 2 (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) := WithLp.toLp 2 (Y, p.2)
  let u : WithLp 2 (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) := WithLp.toLp 2 v
  have hX : ⟪X, u⟫_ℂ = ⟪p.2, v.2⟫_ℂ - I * ∑ j, ((p.1 j).im : ℂ) * v.1 j := by
    simp [X, Y, u, WithLp.prod_inner_apply, PiLp.inner_apply, Finset.mul_sum, sub_eq_neg_add,
      mul_comm, mul_assoc]
  have hXn : ‖X‖ ^ 2 = (shape p).2 := by
    simp [X, Y, WithLp.prod_norm_sq_eq_of_L2, EuclideanSpace.norm_sq_eq]
  have hun : ‖u‖ ^ 2 = ‖v.1‖ ^ 2 + ‖v.2‖ ^ 2 := by
    simp [u, WithLp.prod_norm_sq_eq_of_L2]
  rw [← hX, ← hXn, ← hun, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm X u) 2

/-- **Strict plurisubharmonicity of `f(s) + g(t)`**, on `ℂᵏ × ℂᵐ`. Let `f` and `g` be `C²` at
`s = (shape p).1` and at `t = (shape p).2`, and write `u⁻ = min u 0`. If
`f'(s) + g'(t) + 2 f''(s)⁻ s + 2 g''(t)⁻ t > 0` and, when `m ≠ 0`, `g'(t) + 2 g''(t)⁻ t > 0`,
then `q ↦ f (s q) + g (t q)` is strictly plurisubharmonic at `p`. -/
theorem isStrictlyPlurisubharmonicAt_shape {f g : ℝ → ℝ}
    {p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)}
    (hf : ContDiffAt ℝ 2 f (shape p).1) (hg : ContDiffAt ℝ 2 g (shape p).2)
    (h₁ : 0 < deriv f (shape p).1 + deriv g (shape p).2 +
      2 * min (iteratedDeriv 2 f (shape p).1) 0 * (shape p).1 +
      2 * min (iteratedDeriv 2 g (shape p).2) 0 * (shape p).2)
    (h₂ : m ≠ 0 →
      0 < deriv g (shape p).2 + 2 * min (iteratedDeriv 2 g (shape p).2) 0 * (shape p).2) :
    IsStrictlyPlurisubharmonicAt (fun q ↦ f (shape q).1 + g (shape q).2) p := by
  set s := (shape p).1 with hs
  set t := (shape p).2 with ht
  have hp : shape p = (s, t) := by rw [hs, ht]
  have hcomp : (fun q : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) ↦
      f (shape q).1 + g (shape q).2) = (f ∘ Prod.fst + g ∘ Prod.snd) ∘ shape := by
    funext q
    simp only [Function.comp_apply, Pi.add_apply]
  have hH : ContDiffAt ℝ 2 (f ∘ Prod.fst + g ∘ Prod.snd) (shape p) := by
    rw [hp]
    exact (hf.comp (s, t) contDiffAt_fst).add (hg.comp (s, t) contDiffAt_snd)
  rw [isStrictlyPlurisubharmonicAt_iff, hcomp]
  intro v hv
  rw [re_leviForm_comp_shape_apply_self hH v, hp,
    fderiv_comp_fst_add_comp_snd (hf.differentiableAt (by norm_num))
      (hg.differentiableAt (by norm_num)),
    fderiv_fderiv_comp_fst_add_comp_snd hf hg]
  have hf₂ : deriv (fderiv ℝ f) s 1 = iteratedDeriv 2 f s := by
    simpa using fderiv_fderiv_apply_eq_smul_iteratedDeriv f s 1 1
  have hg₂ : deriv (fderiv ℝ g) t 1 = iteratedDeriv 2 g t := by
    simpa using fderiv_fderiv_apply_eq_smul_iteratedDeriv g t 1 1
  have hS := norm_sum_re_mul_sq_le p v
  have hT := norm_inner_sub_I_mul_sum_sq_le p v
  rw [← hs] at hS
  rw [← ht] at hT
  set S := ‖∑ j, ((p.1 j).re : ℂ) * v.1 j‖ ^ 2
  set T := ‖⟪p.2, v.2⟫_ℂ - I * ∑ j, ((p.1 j).im : ℂ) * v.1 j‖ ^ 2
  set a := ‖v.1‖ ^ 2 with ha
  set b := ‖v.2‖ ^ 2 with hb
  suffices H : 0 < deriv f s * (a / 2) + deriv g t * (a / 2 + b) + iteratedDeriv 2 f s * S +
      iteratedDeriv 2 g t * T by
    simpa [hf₂, hg₂] using H
  have hs₀ : 0 ≤ s := shape_fst_nonneg p
  have ht₀ : 0 ≤ t := shape_snd_nonneg p
  have ha₀ : 0 ≤ a := by positivity
  have hb₀ : 0 ≤ b := by positivity
  have hS₀ : 0 ≤ S := by positivity
  have hT₀ : 0 ≤ T := by positivity
  -- `f'' S ≥ f''⁻ s a` and `g'' T ≥ g''⁻ t (a + b)`.
  have hfS : min (iteratedDeriv 2 f s) 0 * s * a ≤ iteratedDeriv 2 f s * S :=
    mul_assoc (min _ 0) s a ▸ min_zero_mul_le_mul hS₀ hS
  have hgT : min (iteratedDeriv 2 g t) 0 * t * (a + b) ≤ iteratedDeriv 2 g t * T :=
    mul_assoc (min _ 0) t (a + b) ▸ min_zero_mul_le_mul hT₀ hT
  have hmg : min (iteratedDeriv 2 g t) 0 * t ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (min_le_right _ _) ht₀
  rcases hb₀.lt_or_eq with hb' | hb'
  · -- `v₂ ≠ 0`, so `m ≠ 0`.
    have hm : m ≠ 0 := by
      rintro rfl
      have h0 : v.2 = 0 := Subsingleton.elim _ _
      rw [hb, h0, norm_zero] at hb'
      norm_num at hb'
    nlinarith [mul_pos hb' (h₂ hm), mul_nonneg hb₀ (neg_nonneg.mpr hmg), mul_nonneg ha₀ h₁.le]
  · -- `v₂ = 0`, so `v₁ ≠ 0`.
    have ha' : 0 < a := by
      refine ha₀.lt_of_ne fun h ↦ hv ?_
      have h1 : v.1 = 0 := by simpa [ha] using h.symm
      have h2 : v.2 = 0 := by simpa [hb] using hb'.symm
      exact Prod.ext h1 h2
    rw [← hb'] at hgT ⊢
    nlinarith [mul_pos ha' h₁]

/-- **Strict plurisubharmonicity of `f(s) + g(t)`**, on `ℂᵏ × ℂᵐ` as a complex manifold modelled
on itself. Let `f` and `g` be `C²` at `s = (shape p).1` and at `t = (shape p).2`, and write
`u⁻ = min u 0`. If `f'(s) + g'(t) + 2 f''(s)⁻ s + 2 g''(t)⁻ t > 0` and, when `m ≠ 0`,
`g'(t) + 2 g''(t)⁻ t > 0`, then `q ↦ f (s q) + g (t q)` is strictly plurisubharmonic at `p`. -/
theorem isManifoldStrictlyPlurisubharmonicAt_shape {f g : ℝ → ℝ}
    {p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)}
    (hf : ContDiffAt ℝ 2 f (shape p).1) (hg : ContDiffAt ℝ 2 g (shape p).2)
    (h₁ : 0 < deriv f (shape p).1 + deriv g (shape p).2 +
      2 * min (iteratedDeriv 2 f (shape p).1) 0 * (shape p).1 +
      2 * min (iteratedDeriv 2 g (shape p).2) 0 * (shape p).2)
    (h₂ : m ≠ 0 →
      0 < deriv g (shape p).2 + 2 * min (iteratedDeriv 2 g (shape p).2) 0 * (shape p).2) :
    IsManifoldStrictlyPlurisubharmonicAt (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
      (fun q ↦ f (shape q).1 + g (shape q).2) p := by
  rw [isManifoldStrictlyPlurisubharmonicAt_iff]
  simpa only [manifoldLeviForm_eq_leviForm, ← isStrictlyPlurisubharmonicAt_iff] using
    isStrictlyPlurisubharmonicAt_shape hf hg h₁ h₂

end SymplecticGeometry

end
