/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Complex.Euclidean.Space
import SymplecticGeometry.Analysis.InnerProductSpace.PiL2

/-!
# Norms of the real coordinates of complex vectors

Tau Ceti's `TauCeti.complexToRealEuclidean ι` splits `u : ι → ℂ` into its real and imaginary
coordinate blocks in `EuclideanSpace ℝ (ι ⊕ ι)`. This file computes the norm of the image, from
Tau Ceti's `TauCeti.inner_complexToRealEuclidean` and `Matrix.re_star_dotProduct_self`:

* `TauCeti.norm_sq_complexToRealEuclidean`: `‖complexToRealEuclidean ι u‖ ^ 2 = ∑ᵢ ‖uᵢ‖²`;
* `TauCeti.norm_complexToRealEuclidean_smul`: scaling `u` by `a : ℂ` scales that norm by `‖a‖`;
* `TauCeti.complexToRealEuclideanIsometry ι`: so `complexToRealEuclidean ι`, read on
  `EuclideanSpace ℂ ι`, is a real linear isometry onto `EuclideanSpace ℝ (ι ⊕ ι)`;
* `TauCeti.norm_complexToRealEuclidean`: so the norm of `complexToRealEuclidean ι u` is the
  Hermitian norm of `u`, read in `EuclideanSpace ℂ ι`;
* `TauCeti.complexToRealEuclideanCoord ι j`: the `j`-th complex coordinate of
  `(complexToRealEuclidean ι).symm x`, as a real continuous linear map, of operator norm at most
  `1` (`TauCeti.norm_complexToRealEuclideanCoord_le`), since each coordinate has norm at most
  `‖x‖` (`TauCeti.norm_complexToRealEuclidean_symm_apply_le`).
-/

public section

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- The squared norm of `complexToRealEuclidean ι u` is `∑ᵢ ‖uᵢ‖²`. -/
theorem norm_sq_complexToRealEuclidean (u : ι → ℂ) :
    ‖complexToRealEuclidean ι u‖ ^ 2 = ∑ i, ‖u i‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_complexToRealEuclidean, Matrix.re_star_dotProduct_self]

/-- `complexToRealEuclidean ι` is compatible with the norms: scaling by `a : ℂ` scales the norm
of the image by `‖a‖`. -/
theorem norm_complexToRealEuclidean_smul (a : ℂ) (v : ι → ℂ) :
    ‖complexToRealEuclidean ι (a • v)‖ = ‖a‖ * ‖complexToRealEuclidean ι v‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity)]
  simp [mul_pow, norm_sq_complexToRealEuclidean, Finset.mul_sum]

variable (ι) in
/-- The real linear isometry `EuclideanSpace ℂ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ (ι ⊕ ι)` sending `v` to
the real and imaginary parts of its coordinates: `complexToRealEuclidean ι` read on
`EuclideanSpace ℂ ι`. -/
noncomputable def complexToRealEuclideanIsometry :
    EuclideanSpace ℂ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ (ι ⊕ ι) where
  toLinearEquiv := ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℂ)).trans
    (complexToRealEuclidean ι)).toLinearEquiv
  norm_map' v := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), EuclideanSpace.norm_sq_eq v]
    exact norm_sq_complexToRealEuclidean (WithLp.ofLp v)

/-- `complexToRealEuclideanIsometry ι` is `complexToRealEuclidean ι` on the coordinates. -/
@[simp]
theorem complexToRealEuclideanIsometry_apply (v : EuclideanSpace ℂ ι) :
    complexToRealEuclideanIsometry ι v = complexToRealEuclidean ι (WithLp.ofLp v) :=
  (rfl)

/-- The inverse of `complexToRealEuclideanIsometry ι` recombines the two real coordinate blocks
into a complex vector, by the inverse of `complexToRealEuclidean ι`. -/
@[simp]
theorem complexToRealEuclideanIsometry_symm_apply (x : EuclideanSpace ℝ (ι ⊕ ι)) :
    (complexToRealEuclideanIsometry ι).symm x =
      WithLp.toLp 2 ((complexToRealEuclidean ι).symm x) :=
  (rfl)

/-- `complexToRealEuclidean ι` preserves the norm: the Euclidean norm of the real coordinates of
`u : ι → ℂ` is the Hermitian norm of `u`, read in `EuclideanSpace ℂ ι`. -/
theorem norm_complexToRealEuclidean (u : ι → ℂ) :
    ‖complexToRealEuclidean ι u‖ = ‖(EuclideanSpace.equiv ι ℂ).symm u‖ := by
  rw [← (complexToRealEuclideanIsometry ι).norm_map ((EuclideanSpace.equiv ι ℂ).symm u),
    complexToRealEuclideanIsometry_apply]
  simp

/-- The `j`-th complex coordinate of `(complexToRealEuclidean ι).symm x` has norm at most `‖x‖`. -/
theorem norm_complexToRealEuclidean_symm_apply_le (x : EuclideanSpace ℝ (ι ⊕ ι)) (j : ι) :
    ‖(complexToRealEuclidean ι).symm x j‖ ≤ ‖x‖ := by
  have h := PiLp.norm_apply_le ((complexToRealEuclideanIsometry ι).symm x) j
  rwa [LinearIsometryEquiv.norm_map, complexToRealEuclideanIsometry_symm_apply,
    PiLp.toLp_apply] at h

variable (ι) in
/-- The `j`-th complex coordinate `x ↦ (complexToRealEuclidean ι).symm x j` on
`EuclideanSpace ℝ (ι ⊕ ι)`, as a real continuous linear map. -/
noncomputable def complexToRealEuclideanCoord (j : ι) : EuclideanSpace ℝ (ι ⊕ ι) →L[ℝ] ℂ :=
  ContinuousLinearMap.proj j ∘L (complexToRealEuclidean ι).symm.toContinuousLinearMap

@[simp]
theorem complexToRealEuclideanCoord_apply (j : ι) (x : EuclideanSpace ℝ (ι ⊕ ι)) :
    complexToRealEuclideanCoord ι j x = (complexToRealEuclidean ι).symm x j :=
  (rfl)

/-- The `j`-th complex coordinate on `EuclideanSpace ℝ (ι ⊕ ι)` has operator norm at most `1`. -/
theorem norm_complexToRealEuclideanCoord_le (j : ι) : ‖complexToRealEuclideanCoord ι j‖ ≤ 1 :=
  (complexToRealEuclideanCoord ι j).opNorm_le_bound zero_le_one fun x ↦ by
    simpa using norm_complexToRealEuclidean_symm_apply_le x j

end TauCeti

end
