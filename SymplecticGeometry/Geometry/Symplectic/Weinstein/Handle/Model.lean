/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.Shape
public import SymplecticGeometry.Geometry.Manifold.Morse.GradientLike
public import TauCeti.Geometry.Symplectic.Complex.ImInner.Basic
public import TauCeti.Geometry.Symplectic.Liouville.VectorField
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
public import TauCeti.Geometry.Symplectic.Prod.Basic
import SymplecticGeometry.Geometry.Symplectic.Liouville.VectorField
import TauCeti.Analysis.InnerProductSpace.Euclidean.Complex
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The standard Weinstein handle

On `V = ℂᵏ × ℂᵐ`, with points `p = (x + i y, w)`, the standard Weinstein handle of index `k` is
given by three objects:

* the constant symplectic form of `(imInnerSymplecticForm _).prod (imInnerSymplecticForm _)`,
  the form `Im ⟪·, ·⟫_ℂ` on each factor;
* the linear vector field `SymplecticGeometry.modelHandleField k m`,
  `(x + i y, w) ↦ (-x + 2 i y, w / 2)`;
* the model handle function `SymplecticGeometry.modelHandle k m a b = b t - a s` of the
  `J`-convex surrounding, with `s = |x|²`, `t = |y|² + |w|²`, `0 < a` and `0 < b`. Its Morse
  data are those of `JConvex/Surround/Shape.lean`.

For `k ≥ 1` the function is not bounded below, so the triple is not a Weinstein structure; it is
stated property by property.

## Main results

* `SymplecticGeometry.isLiouvilleVectorField_modelHandleField`: the handle field is a Liouville
  field of the constant product form. On each complex line of the first factor the field is
  `diag (-1, 2)`, of trace `1`, and on the second factor it is `1 / 2`, so that
  `ω (A u) v + ω u (A v) = ω u v`
  (`SymplecticGeometry.prod_imInnerSymplecticForm_modelHandleField_add`). The criterion
  `TauCeti.SymplecticForm.isLiouvilleVectorField_constSmooth` of
  `Liouville/VectorField.lean`, applied here, turns this identity into the Liouville property.
* `SymplecticGeometry.mvfderiv_modelHandle_modelHandleField`:
  `d(bt - as)_p (A p) = 2 a s + 4 b |y|² + b |w|²`.
* `SymplecticGeometry.isGradientLike_modelHandle_modelHandleField`: the handle field is
  gradient-like for the model handle function, by `TauCeti.isGradientLike_of_mul_le`, since the
  derivative above is a positive definite quadratic form in `p` while `A p` and `d(bt - as)_p`
  grow linearly in `p`. The differential of the model handle function and its bound,
  `SymplecticGeometry.fderiv_modelHandle_apply` and
  `SymplecticGeometry.norm_fderiv_modelHandle_le`, come from `JConvex/Surround/Shape.lean`.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Chapter 11 (Weinstein structures and the standard handle)
-/

public section

open Complex
open scoped Manifold ContDiff InnerProductSpace

namespace SymplecticGeometry

open TauCeti

variable (k m : ℕ)

/-- The **standard Weinstein handle field** on `ℂᵏ × ℂᵐ`: the real linear map
`(x + i y, w) ↦ (-x + 2 i y, w / 2)`. -/
noncomputable def modelHandleField :
    (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) →L[ℝ]
      EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) :=
  (((complexEuclideanEquivRealProd (Fin k)).symm :
        EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℂ (Fin k)) ∘L
      ((-ContinuousLinearMap.id ℝ _).prodMap ((2 : ℝ) • ContinuousLinearMap.id ℝ _)) ∘L
      (complexEuclideanEquivRealProd (Fin k) :
        EuclideanSpace ℂ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k))).prodMap
    ((2⁻¹ : ℝ) • ContinuousLinearMap.id ℝ _)

variable {k m}

/-- The coordinates of the first component of the handle field: `x + i y ↦ -x + 2 i y`. -/
theorem modelHandleField_apply_fst_apply
    (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) (j : Fin k) :
    (modelHandleField k m p).1 j = -(p.1 j).re + 2 * (p.1 j).im * I := by
  simp [modelHandleField]

/-- The second component of the handle field: `w ↦ w / 2`. -/
@[simp]
theorem modelHandleField_apply_snd (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    (modelHandleField k m p).2 = (2⁻¹ : ℝ) • p.2 := by
  simp [modelHandleField]

/-- The real part of a coordinate of the handle field: `x ↦ -x`. -/
@[simp]
theorem re_modelHandleField_apply_fst_apply
    (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) (j : Fin k) :
    ((modelHandleField k m p).1 j).re = -(p.1 j).re := by
  simp [modelHandleField_apply_fst_apply]

/-- The imaginary part of a coordinate of the handle field: `y ↦ 2 y`. -/
@[simp]
theorem im_modelHandleField_apply_fst_apply
    (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) (j : Fin k) :
    ((modelHandleField k m p).1 j).im = 2 * (p.1 j).im := by
  simp [modelHandleField_apply_fst_apply]

/-- The handle field `(x + i y, w) ↦ (-x + 2 i y, w / 2)`. -/
theorem modelHandleField_apply (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    modelHandleField k m p =
      (WithLp.toLp 2 fun j ↦ -(p.1 j).re + 2 * (p.1 j).im * I, (2⁻¹ : ℝ) • p.2) := by
  ext j
  · exact modelHandleField_apply_fst_apply p j
  · rw [modelHandleField_apply_snd]

/-- The handle field is smooth, as a section of the tangent bundle. -/
theorem contMDiff_modelHandleField {n : WithTop ℕ∞} :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
      𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)).tangent n
      (fun p ↦ (⟨p, modelHandleField k m p⟩ :
        TangentBundle 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
          (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)))) :=
  contMDiff_vectorSpace_iff_contDiff.mpr (modelHandleField k m).contDiff

/-! ### The Liouville property -/

/-- The handle field scales the product form `Im ⟪·, ·⟫_ℂ ⊕ Im ⟪·, ·⟫_ℂ` at rate one:
`ω (A u) v + ω u (A v) = ω u v`. -/
theorem prod_imInnerSymplecticForm_modelHandleField_add
    (u v : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    (imInnerSymplecticForm _).prod (imInnerSymplecticForm _) (modelHandleField k m u) v +
        (imInnerSymplecticForm _).prod (imInnerSymplecticForm _) u (modelHandleField k m v) =
      (imInnerSymplecticForm _).prod (imInnerSymplecticForm _) u v := by
  simp only [SymplecticForm.prod_apply, imInnerSymplecticForm_apply, PiLp.inner_apply,
    Complex.im_sum, modelHandleField_apply_snd]
  have h₁ : ∑ j, (⟪(modelHandleField k m u).1 j, v.1 j⟫_ℂ).im +
      ∑ j, (⟪u.1 j, (modelHandleField k m v).1 j⟫_ℂ).im = ∑ j, (⟪u.1 j, v.1 j⟫_ℂ).im := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [RCLike.inner_apply, mul_im, conj_re, conj_im, re_modelHandleField_apply_fst_apply,
      im_modelHandleField_apply_fst_apply]
    ring
  have h₂ : ∑ j, (⟪((2⁻¹ : ℝ) • u.2) j, v.2 j⟫_ℂ).im +
      ∑ j, (⟪u.2 j, ((2⁻¹ : ℝ) • v.2) j⟫_ℂ).im = ∑ j, (⟪u.2 j, v.2 j⟫_ℂ).im := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [PiLp.smul_apply, RCLike.inner_apply, Complex.real_smul, map_mul, conj_ofReal,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re]
    ring
  linear_combination h₁ + h₂

/-- **The standard handle field is Liouville.** The field `(x + i y, w) ↦ (-x + 2 i y, w / 2)`
is a Liouville vector field of the constant form `Im ⟪·, ·⟫_ℂ ⊕ Im ⟪·, ·⟫_ℂ` on `ℂᵏ × ℂᵐ`. -/
theorem isLiouvilleVectorField_modelHandleField :
    IsLiouvilleVectorField
      ((imInnerSymplecticForm (EuclideanSpace ℂ (Fin k))).prod
        (imInnerSymplecticForm (EuclideanSpace ℂ (Fin m)))).constSmooth.val
      (fun p ↦ modelHandleField k m p :
        (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) →
          TangentSpace 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) p) :=
  SymplecticForm.isLiouvilleVectorField_constSmooth _
    prod_imInnerSymplecticForm_modelHandleField_add

/-! ### The gradient-like property -/

/-- **The derivative of the model handle function along the handle field**:
`d(bt - as)_p (A p) = 2 a s + 4 b |y|² + b |w|²` at `p = (x + i y, w)`. -/
theorem mvfderiv_modelHandle_modelHandleField (a b : ℝ)
    (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    mvfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) (modelHandle k m a b) p
        (modelHandleField k m p) =
      2 * a * (shape p).1 + 4 * b * ∑ j, (p.1 j).im ^ 2 + b * ‖p.2‖ ^ 2 := by
  refine (mvfderiv_eq_fderiv_apply _ p _).trans ?_
  have hw : (⟪p.2, (2⁻¹ : ℝ) • p.2⟫_ℂ).re = 2⁻¹ * ‖p.2‖ ^ 2 := by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right, ← RCLike.re_to_complex,
      RCLike.re_ofReal_mul, inner_self_eq_norm_sq]
  rw [fderiv_modelHandle_apply, modelHandleField_apply_snd, hw, shape_fst]
  simp only [re_modelHandleField_apply_fst_apply, im_modelHandleField_apply_fst_apply]
  have h₁ : ∑ j, (p.1 j).im * (2 * (p.1 j).im) = 2 * ∑ j, (p.1 j).im ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ ↦ by ring
  have h₂ : ∑ j, (p.1 j).re * -(p.1 j).re = -∑ j, (p.1 j).re ^ 2 := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [h₁, h₂]
  ring

/-- **The standard handle field is gradient-like** for the model handle function `b t - a s`,
for `0 < a` and `0 < b`, with a constant `δ`. -/
theorem isGradientLike_modelHandle_modelHandleField {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IsGradientLike (modelHandle k m a b)
      (fun p ↦ modelHandleField k m p :
        (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) →
          TangentSpace 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) p) := by
  set A := modelHandleField k m
  set C := 2 * |a| + 4 * |b|
  have hC : 0 < C := by positivity
  refine isGradientLike_of_mul_le (c := min (2 * a) b / (‖A‖ ^ 2 + C ^ 2))
    (by positivity) fun p ↦ ?_
  have hD : fderiv ℝ (modelHandle k m a b) p (A p) =
      2 * a * (shape p).1 + 4 * b * ∑ j, (p.1 j).im ^ 2 + b * ‖p.2‖ ^ 2 :=
    (mvfderiv_eq_fderiv_apply _ p _).symm.trans (mvfderiv_modelHandle_modelHandleField a b p)
  have hA : ‖A p‖ ^ 2 ≤ ‖A‖ ^ 2 * ‖p‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm p) 2
  have hdf : ‖fderiv ℝ (modelHandle k m a b) p‖ ^ 2 ≤ C ^ 2 * ‖p‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_modelHandle_le a b p) 2
  -- The derivative along the field dominates `min (2 a) b * ‖p‖ ^ 2`.
  have hp : ‖p‖ ^ 2 ≤ ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2 := by
    rw [Prod.norm_def]
    rcases max_cases ‖p.1‖ ‖p.2‖ with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
    all_goals nlinarith [sq_nonneg ‖p.1‖, sq_nonneg ‖p.2‖]
  have hκ : min (2 * a) b * ‖p‖ ^ 2 ≤ fderiv ℝ (modelHandle k m a b) p (A p) := by
    rw [hD, shape_fst]
    have h1 : ‖p.1‖ ^ 2 = ∑ j, (p.1 j).re ^ 2 + ∑ j, (p.1 j).im ^ 2 := by
      have h := norm_complexEuclideanEquivRealProd_symm_sq
        (complexEuclideanEquivRealProd (Fin k) p.1)
      rw [ContinuousLinearEquiv.symm_apply_apply, EuclideanSpace.real_norm_sq_eq,
        EuclideanSpace.real_norm_sq_eq] at h
      simpa using h
    have hs : 0 ≤ ∑ j, (p.1 j).re ^ 2 := by positivity
    have hy : 0 ≤ ∑ j, (p.1 j).im ^ 2 := by positivity
    have hm₁ : min (2 * a) b ≤ 2 * a := min_le_left _ _
    have hm₂ : min (2 * a) b ≤ b := min_le_right _ _
    have hm₀ : 0 ≤ min (2 * a) b := le_min (by linarith) hb.le
    calc min (2 * a) b * ‖p‖ ^ 2
        ≤ min (2 * a) b * (∑ j, (p.1 j).re ^ 2 + ∑ j, (p.1 j).im ^ 2 + ‖p.2‖ ^ 2) := by
          rw [← h1]; exact mul_le_mul_of_nonneg_left hp hm₀
      _ ≤ _ := by nlinarith [sq_nonneg ‖p.2‖]
  calc min (2 * a) b / (‖A‖ ^ 2 + C ^ 2) *
        (‖A p‖ ^ 2 + ‖fderiv ℝ (modelHandle k m a b) p‖ ^ 2)
      ≤ min (2 * a) b / (‖A‖ ^ 2 + C ^ 2) * ((‖A‖ ^ 2 + C ^ 2) * ‖p‖ ^ 2) := by
        gcongr
        linarith
    _ = min (2 * a) b * ‖p‖ ^ 2 := by field_simp
    _ ≤ _ := hκ

end SymplecticGeometry

end
