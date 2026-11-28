/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.Shape
public import SymplecticGeometry.Geometry.Manifold.Flow.Linear
public import SymplecticGeometry.Geometry.Manifold.Morse.GradientLike
public import SymplecticGeometry.Geometry.Symplectic.Weinstein.Basic
public import TauCeti.Geometry.Symplectic.Complex.ImInner.Basic
public import TauCeti.Geometry.Symplectic.Liouville.VectorField
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
public import TauCeti.Geometry.Symplectic.Prod.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import SymplecticGeometry.Analysis.ODE.Linear
import SymplecticGeometry.Geometry.Symplectic.Liouville.VectorField
import TauCeti.Analysis.InnerProductSpace.Euclidean.Complex
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Topology.Maps.Proper.Metric

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
stated property by property. For `k = 0` the coordinate `s` vanishes, the function is `b ‖p‖²`,
and the triple is a Weinstein structure.

## Main results

* `SymplecticGeometry.isCompleteVectorField_modelHandleField`: the handle field is complete, as
  is every bounded linear field (`ContinuousLinearMap.isCompleteVectorField`,
  `Geometry/Manifold/Flow/Linear.lean`).
* `SymplecticGeometry.modelHandleField_flow_apply`: the linear flow `exp (t A)` of the handle field
  is `(x + i y, w) ↦ (e^{-t} x + i e^{2t} y, e^{t/2} w)`. The right side is an integral curve
  through `(x + i y, w)`, so it is the flow by uniqueness of integral curves
  (`ContinuousLinearMap.flow_eq_of_isMIntegralCurve`).
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
* `SymplecticGeometry.isWeinsteinStructure_modelHandle_zero`: for `k = 0` and `0 < b` the triple
  is a Weinstein structure. It is checked condition by condition: the Liouville, completeness and
  gradient-like results above, the Morse property `SymplecticGeometry.isMorse_modelHandle`, and
  properness and boundedness below of `b ‖p‖²`, the form the function takes for `k = 0`
  (`SymplecticGeometry.modelHandle_zero_apply`, from `JConvex/Surround/Shape.lean`).
* `SymplecticGeometry.stableSubspace_modelHandleField`: the stable set of `0` for the handle
  field, Tau Ceti's `ContinuousLinearMap.stableSubspace`, is the core `range (modelDisc k m)`.
  In real coordinates the field is `(-1) • id ⊕ 2 • id ⊕ ½ • id`, so this follows from
  `ContinuousLinearMap.stableSubspace_prodMap`, `ContinuousLinearMap.stableSubspace_smul_id_of_neg`
  and `ContinuousLinearMap.stableSubspace_smul_id_of_nonneg` (`Analysis/ODE/Linear.lean`), carried
  through the coordinates by `ContinuousLinearEquiv.stableSubspace_conjContinuousAlgEquiv`.
  The block-diagonal step is
  `SymplecticGeometry.stableSubspace_conjContinuousAlgEquiv_prodMap_eq_map_modelDisc`: a field that
  is `A ⊕ B ⊕ ½ • id` in real coordinates, with `B` having no nonzero stable vector, has stable
  subspace `ι₀ (A.stableSubspace)`. `Homotopy/IsotropicLift.lean` uses it for the Liouville lift.
* `SymplecticGeometry.prod_imInnerSymplecticForm_eq_zero_of_mem_range_modelDisc`: the core is
  isotropic for the product form, by `ContinuousLinearMap.apply_eq_zero_of_mem_stableSubspace`
  (`Analysis/ODE/Linear.lean`) applied to the identity above.
* `SymplecticGeometry.range_modelDisc_inter_preimage_modelHandle_neg`: the attaching sphere of
  the model. Since `b t - a s` is `-a |x|²` on the core
  (`SymplecticGeometry.modelHandle_modelDisc`), the core meets the level `-c` in
  `ι₀ (sphere 0 √(c / a))`.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  §12.3: on `T^*L × ℂ^ℓ` a vector field `Y` on `L` extends to the Liouville field
  `p ∂_p + z ∂_z / 2 + X_H`, `H = ⟨p, Y(q)⟩`, given in coordinates in the proof of Lemma 12.8 (i).
  These `q`, `p` and `z` are the book's coordinates on `T^*L × ℂ^ℓ`, not the point `p` above.
  For `L = ℝᵏ` and `Y = -q` the field is `-q ∂_q + 2 p ∂_p + z ∂_z / 2`. Under the dictionary
  `q = x`, `p = y`, `z = w` and `ℓ = m`, it is `modelHandleField k m`, and the function
  `ψ(q) + |p|² + |z|²` of that section, for `ψ = -|q|²`, is `modelHandle k m 1 1`. The book
  takes `dp ∧ dq` on `T^*ℝᵏ`, the opposite of the form here, which does not change the Liouville
  condition. Definition 11.10 for Weinstein structures; Proposition 11.9 (a) for the isotropy of
  the stable subspace of the linearization of a Liouville field at a zero.
-/

public section

open Complex Filter Metric Set Topology
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
  (modelHandleField k m).contMDiff_tangent n

/-! ### Completeness and the flow -/

/-- The handle field is complete: its integral curves are defined for all time. -/
theorem isCompleteVectorField_modelHandleField :
    IsCompleteVectorField (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)))
      (fun p ↦ modelHandleField k m p) :=
  (modelHandleField k m).isCompleteVectorField

/-- The curve `t ↦ (e^{-t} x + i e^{2t} y, e^{t/2} w)` through `p = (x + i y, w)`, written with
the real and imaginary parts of `TauCeti.complexEuclideanEquivRealProd`, is an integral curve of
the handle field. -/
private theorem isMIntegralCurve_modelHandleField
    (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    IsMIntegralCurve (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)))
      (fun t : ℝ ↦ ((complexEuclideanEquivRealProd (Fin k)).symm
          (Real.exp (-t) • (complexEuclideanEquivRealProd (Fin k) p.1).1,
            Real.exp (2 * t) • (complexEuclideanEquivRealProd (Fin k) p.1).2),
        Real.exp (t / 2) • p.2))
      (fun q ↦ modelHandleField k m q) := by
  intro t
  set e := complexEuclideanEquivRealProd (Fin k)
  have h₁ : HasDerivAt (fun s : ℝ ↦ Real.exp (-s)) (-Real.exp (-t)) t := by
    simpa using (hasDerivAt_neg t).exp
  have h₂ : HasDerivAt (fun s : ℝ ↦ Real.exp (2 * s)) (2 * Real.exp (2 * t)) t := by
    simpa [mul_comm] using ((hasDerivAt_id t).const_mul 2).exp
  have h₃ : HasDerivAt (fun s : ℝ ↦ Real.exp (s / 2)) (2⁻¹ * Real.exp (t / 2)) t := by
    simpa [div_eq_mul_inv, mul_comm] using ((hasDerivAt_id t).mul_const 2⁻¹).exp
  have h := HasDerivAt.prodMk (e.symm.hasFDerivAt.comp_hasDerivAt t
    (HasDerivAt.prodMk (h₁.smul_const (e p.1).1) (h₂.smul_const (e p.1).2)))
    (h₃.smul_const p.2)
  refine (h.congr_deriv ?_).hasFDerivAt.hasMFDerivAt
  ext j
  · apply Complex.ext <;> simp [e, modelHandleField_apply_fst_apply, -Complex.ofReal_exp]
    ring
  · simp [smul_smul, mul_comm]

/-- **The flow of the handle field**: at time `t` it is
`(x + i y, w) ↦ (e^{-t} x + i e^{2t} y, e^{t/2} w)`. -/
theorem modelHandleField_flow_apply (t : ℝ)
    (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    (modelHandleField k m).flow t p =
      (WithLp.toLp 2 fun j ↦
          ((Real.exp (-t) * (p.1 j).re : ℝ) : ℂ) + ((Real.exp (2 * t) * (p.1 j).im : ℝ) : ℂ) * I,
        Real.exp (t / 2) • p.2) := by
  have h := (modelHandleField k m).flow_eq_of_isMIntegralCurve
    (isMIntegralCurve_modelHandleField p) t
  simp only [neg_zero, mul_zero, zero_div, Real.exp_zero, one_smul, Prod.mk.eta,
    ContinuousLinearEquiv.symm_apply_apply] at h
  rw [h]
  ext j <;> simp

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
      have h := shape_fst_add_shape_snd p
      rw [shape_fst, shape_snd] at h
      linarith
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

/-! ### Index zero -/

/-- **The standard handle of index zero is a Weinstein structure.** On `ℂ⁰ × ℂᵐ`, for `0 < b` and
every `a`, the constant form `Im ⟪·, ·⟫_ℂ ⊕ Im ⟪·, ·⟫_ℂ`, the handle field `p ↦ p / 2` and the
model handle function `p ↦ b ‖p‖²` form a Weinstein structure. -/
theorem isWeinsteinStructure_modelHandle_zero (a : ℝ) {b : ℝ} (hb : 0 < b) :
    IsWeinsteinStructure
      ((imInnerSymplecticForm (EuclideanSpace ℂ (Fin 0))).prod
        (imInnerSymplecticForm (EuclideanSpace ℂ (Fin m)))).constSmooth
      (fun p ↦ modelHandleField 0 m p :
        (p : EuclideanSpace ℂ (Fin 0) × EuclideanSpace ℂ (Fin m)) →
          TangentSpace 𝓘(ℝ, EuclideanSpace ℂ (Fin 0) × EuclideanSpace ℂ (Fin m)) p)
      (modelHandle 0 m a b) := by
  have hf : modelHandle 0 m a b = (b * ·) ∘ fun p ↦ ‖p‖ ^ 2 :=
    funext (modelHandle_zero_apply a b)
  -- The function does not depend on `a`, so the Morse and gradient-like results apply with `1`.
  have h₁ : modelHandle 0 m a b = modelHandle 0 m 1 b := funext fun p ↦ by
    rw [modelHandle_zero_apply, modelHandle_zero_apply]
  refine ⟨SymplecticForm.isSymplectic_constSmooth _, contMDiff_modelHandleField,
    isLiouvilleVectorField_modelHandleField, isCompleteVectorField_modelHandleField, ?_, ?_,
    h₁ ▸ (isMorse_modelHandle one_pos hb).isGeneralizedMorse,
    h₁ ▸ isGradientLike_modelHandle_modelHandleField one_pos hb⟩
  · rw [hf]
    exact (Homeomorph.mulLeft₀ b hb.ne').isProperMap.comp
      (by simpa using isProperMap_norm_sq_sub (0 : EuclideanSpace ℂ (Fin 0) ×
        EuclideanSpace ℂ (Fin m)))
  · rw [hf, Set.range_comp]
    exact ⟨0, by rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩; positivity⟩

/-! ### The core: stable subspace, isotropy and attaching sphere -/

/-- On the core `ι₀ (ℝᵏ)` the flow of the handle field is the contraction `x ↦ e^{-t} x`. -/
theorem modelHandleField_flow_modelDisc (t : ℝ) (x : EuclideanSpace ℝ (Fin k)) :
    (modelHandleField k m).flow t (modelDisc k m x) = modelDisc k m (Real.exp (-t) • x) := by
  rw [modelHandleField_flow_apply]
  ext j <;> simp

/-- **Stable subspaces of block-diagonal fields on the handle.** For `A B : ℝᵏ →L[ℝ] ℝᵏ` with
`B.stableSubspace = ⊥`, the field on `ℂᵏ × ℂᵐ` that is `A ⊕ B ⊕ ½ I` in the real coordinates
`(x + i y, w) ↦ ((x, y), w)` has stable subspace the image of `A.stableSubspace` under `ι₀`. -/
theorem stableSubspace_conjContinuousAlgEquiv_prodMap_eq_map_modelDisc
    (A B : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (hB : B.stableSubspace = ⊥) :
    (((complexEuclideanEquivRealProd (Fin k)).prodCongr
        (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℂ (Fin m)))).symm.conjContinuousAlgEquiv
        ((A.prodMap B).prodMap ((2⁻¹ : ℝ) • ContinuousLinearMap.id ℝ _))).stableSubspace =
      A.stableSubspace.map (modelDisc k m).toLinearMap := by
  rw [ContinuousLinearEquiv.stableSubspace_conjContinuousAlgEquiv,
    ContinuousLinearMap.stableSubspace_prodMap, ContinuousLinearMap.stableSubspace_prodMap, hB,
    ContinuousLinearMap.stableSubspace_smul_id_of_nonneg (by norm_num), ← Submodule.map_inl,
    ← Submodule.map_inl, ← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  refine LinearMap.ext fun y ↦
    Prod.ext ((complexEuclideanEquivRealProd (Fin k)).injective ?_) ?_ <;> simp

/-- **The stable set of the handle field is the core**: the points whose orbit under the flow of
`(x + i y, w) ↦ (-x + 2 i y, w / 2)` tends to `0` are those of `ι₀ (ℝᵏ) = {(x, 0)}`. In real
coordinates the field is `(-1) • id ⊕ 2 • id ⊕ ½ • id`, whose stable subspace is `ℝᵏ × 0 × 0`. -/
theorem stableSubspace_modelHandleField :
    ((modelHandleField k m).stableSubspace :
        Set (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))) =
      range (modelDisc k m) := by
  have h : modelHandleField k m = ((complexEuclideanEquivRealProd (Fin k)).prodCongr
      (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℂ (Fin m)))).symm.conjContinuousAlgEquiv
      ((((-1 : ℝ) • ContinuousLinearMap.id ℝ _).prodMap
          ((2 : ℝ) • ContinuousLinearMap.id ℝ _)).prodMap
        ((2⁻¹ : ℝ) • ContinuousLinearMap.id ℝ _)) := by
    ext p j <;> simp [modelHandleField_apply_fst_apply]
  rw [h, stableSubspace_conjContinuousAlgEquiv_prodMap_eq_map_modelDisc _ _
      (ContinuousLinearMap.stableSubspace_smul_id_of_nonneg (by norm_num)),
    ContinuousLinearMap.stableSubspace_smul_id_of_neg (by norm_num), Submodule.map_top,
    LinearMap.coe_range, ContinuousLinearMap.coe_coe]

/-- **The core of the handle is isotropic**: the constant form `Im ⟪·, ·⟫_ℂ ⊕ Im ⟪·, ·⟫_ℂ`
vanishes on pairs of vectors of `ι₀ (ℝᵏ)`. The core is the stable subspace of the handle field,
which the field's Liouville identity makes isotropic
(`ContinuousLinearMap.apply_eq_zero_of_mem_stableSubspace`). -/
theorem prod_imInnerSymplecticForm_eq_zero_of_mem_range_modelDisc
    {u v : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)} (hu : u ∈ range (modelDisc k m))
    (hv : v ∈ range (modelDisc k m)) :
    (imInnerSymplecticForm _).prod (imInnerSymplecticForm _) u v = 0 := by
  rw [← stableSubspace_modelHandleField, SetLike.mem_coe] at hu hv
  simpa only [LinearMap.toContinuousBilinearMap_apply] using
    ContinuousLinearMap.apply_eq_zero_of_mem_stableSubspace
      (B := ((imInnerSymplecticForm (EuclideanSpace ℂ (Fin k))).prod
        (imInnerSymplecticForm (EuclideanSpace ℂ (Fin m)))).toBilinForm.toContinuousBilinearMap)
      (fun u v ↦ by
        simpa only [LinearMap.toContinuousBilinearMap_apply] using
          prod_imInnerSymplecticForm_modelHandleField_add u v) hu hv

/-- **The attaching sphere of the model**: for `0 < a` and `0 ≤ c`, the core `ι₀ (ℝᵏ)` meets the
level `-c` of the model handle function `b t - a s` in the image of the sphere of radius
`√(c / a)`, since that function is `-a |x|²` on the core. -/
theorem range_modelDisc_inter_preimage_modelHandle_neg {a b c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) :
    range (modelDisc k m) ∩ modelHandle k m a b ⁻¹' {-c} =
      modelDisc k m '' sphere 0 √(c / a) := by
  ext p
  simp only [mem_inter_iff, mem_range, mem_preimage, mem_singleton_iff, mem_image,
    mem_sphere_zero_iff_norm]
  constructor
  · rintro ⟨⟨x, rfl⟩, hx⟩
    refine ⟨x, ?_, rfl⟩
    rw [modelHandle_modelDisc, neg_inj] at hx
    rw [← hx, mul_div_cancel_left₀ _ ha.ne', Real.sqrt_sq (norm_nonneg x)]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, rfl⟩, ?_⟩
    rw [modelHandle_modelDisc, hx, Real.sq_sqrt (div_nonneg hc ha.le),
      mul_div_cancel₀ _ ha.ne']

end SymplecticGeometry

end
