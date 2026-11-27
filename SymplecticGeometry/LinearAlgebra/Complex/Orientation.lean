/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Complex.Orientation

/-!
# The standard orientation of `ℂ` and of `ℝ²`

The identification `Complex.orthonormalBasisOneI.repr : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)`,
`z ↦ (re z, im z)`, carries the standard orientation `Complex.orientation` of `ℂ` to the
orientation of the standard basis of `ℝ²`.

An `ℝ`-linear endomorphism `L` of `ℂ` multiplies the area form `(a, b) ↦ Im (conj a * b)`, the
determinant in the basis `(1, i)`, by its determinant. So an `ℝ`-linear automorphism `L` has
positive determinant, that is, preserves the orientation of `ℂ`, exactly when the area form tames
the complex structure `L⁻¹ ∘ i ∘ L`.

## Main results

* `Complex.orientation_map_orthonormalBasisOneI_repr`.
* `Complex.im_conj_map_mul_map`: `Im (conj (L a) * L b) = det L * Im (conj a * b)`.
* `Complex.det_pos_iff_forall_im_conj_mul_symm_I_mul_pos`: `0 < det L` exactly when
  `Im (conj v * L⁻¹ (i L v)) > 0` for every `v ≠ 0`.
-/

public section

open Module ComplexConjugate

/-- The real basis `(1, i)` of `ℂ` goes to the standard basis of `ℝ²` under
`Complex.orthonormalBasisOneI.repr`, so this identification carries the standard orientation of
`ℂ` to that of `ℝ²`. -/
theorem Complex.orientation_map_orthonormalBasisOneI_repr :
    Complex.orientation.map (Fin 2) Complex.orthonormalBasisOneI.repr.toLinearEquiv =
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation := by
  rw [Complex.orientation, ← Basis.orientation_map]
  congr 1
  ext i : 1
  rw [← Complex.toBasis_orthonormalBasisOneI, Basis.map_apply, OrthonormalBasis.coe_toBasis]
  fin_cases i <;> ext j <;> fin_cases j <;> simp [Complex.orthonormalBasisOneI_repr_apply]

/-- An `ℝ`-linear endomorphism `L` of `ℂ` multiplies the area form `(a, b) ↦ Im (conj a * b)` by
its determinant. -/
theorem Complex.im_conj_map_mul_map (L : ℂ →ₗ[ℝ] ℂ) (a b : ℂ) :
    (conj (L a) * L b).im = LinearMap.det L * (conj a * b).im := by
  -- The area form is the determinant in the basis `(1, i)`.
  have h (a b : ℂ) : (conj a * b).im = Complex.basisOneI.det ![a, b] := by
    rw [Basis.det_apply, Matrix.det_fin_two]
    simp [Basis.toMatrix_apply]
    ring
  rw [h, h, ← Basis.det_comp]
  congr 1
  ext i
  fin_cases i <;> rfl

/-- An `ℝ`-linear automorphism `L` of `ℂ` has positive determinant exactly when the area form
`(a, b) ↦ Im (conj a * b)` tames the conjugate `L⁻¹ ∘ i ∘ L` of multiplication by `i`. -/
theorem Complex.det_pos_iff_forall_im_conj_mul_symm_I_mul_pos (L : ℂ ≃ₗ[ℝ] ℂ) :
    0 < LinearMap.det (L : ℂ →ₗ[ℝ] ℂ) ↔
      ∀ v ≠ 0, 0 < (conj v * L.symm (Complex.I * L v)).im := by
  have key (u : ℂ) : (conj (L.symm u) * L.symm (Complex.I * u)).im =
      (LinearMap.det (L : ℂ →ₗ[ℝ] ℂ))⁻¹ * Complex.normSq u := by
    have h := Complex.im_conj_map_mul_map (L.symm : ℂ →ₗ[ℝ] ℂ) u (Complex.I * u)
    rw [LinearEquiv.coe_coe] at h
    rw [h, ← LinearEquiv.coe_det, ← LinearEquiv.coe_det, LinearEquiv.det_symm, map_inv,
      Units.val_inv_eq_inv_val]
    simp [Complex.normSq_apply]
  refine ⟨fun h v hv ↦ ?_, fun h ↦ ?_⟩
  · have h1 := key (L v)
    rw [L.symm_apply_apply] at h1
    rw [h1]
    exact mul_pos (inv_pos.2 h) (Complex.normSq_pos.2 (by simpa using hv))
  · have h1 := h (L.symm 1) (by simp)
    rw [L.apply_symm_apply, key, Complex.normSq_one, mul_one] at h1
    exact inv_pos.1 h1

end
