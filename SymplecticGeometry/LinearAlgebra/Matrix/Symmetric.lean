/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import TauCeti.LinearAlgebra.Matrix.OfReal

/-!
# Symmetric matrices

Three facts about symmetric matrices that Mathlib does not have.

If `Aᵀ B = Bᵀ A`, then `A B⁻¹` is symmetric. When `B` is invertible, `A B⁻¹` equals
`B⁻ᵀ (Aᵀ B) B⁻¹`, whose transpose is `B⁻ᵀ (Bᵀ A) B⁻¹`; otherwise Mathlib's `B⁻¹` is `0`.

For a symmetric complex matrix `Z`, the conjugate transpose `Zᴴ` is the entrywise conjugate of `Z`,
so the difference `Z - Zᴴ` is `2i` times the imaginary part of `Z`. This is Tau Ceti's
`Matrix.map_im_map_ofReal_of_transpose_eq` solved for `Z - Zᴴ`, the form in which the library
rewrites with it.

## Main results

* `Matrix.isSymm_mul_nonsing_inv_of_transpose_mul_eq`: `A B⁻¹` is symmetric when `Aᵀ B = Bᵀ A`.
* `Matrix.IsSymm.sub_conjTranspose`: `Z - Zᴴ = 2i Im Z` for a symmetric complex matrix `Z`.
* `Matrix.isSelfAdjoint_one_iff_isSymm`: the matrices that are self-adjoint for the bilinear form
  of the identity matrix, which make up Mathlib's `selfAdjointMatricesSubmodule 1`, are the
  symmetric matrices.
-/

public section

open Complex

namespace Matrix

variable {n : Type*}

/-- If `Aᵀ B = Bᵀ A`, then `A B⁻¹` is symmetric. No invertibility is needed, since Mathlib's
`B⁻¹` is `0` when `det B` is not a unit. -/
theorem isSymm_mul_nonsing_inv_of_transpose_mul_eq [Fintype n] [DecidableEq n] {α : Type*}
    [CommRing α] {A B : Matrix n n α} (hAB : Aᵀ * B = Bᵀ * A) : (A * B⁻¹).IsSymm := by
  by_cases hB : IsUnit B.det
  swap
  · simp [nonsing_inv_apply_not_isUnit _ hB, IsSymm]
  rw [IsSymm, transpose_mul, transpose_nonsing_inv]
  calc Bᵀ⁻¹ * Aᵀ = Bᵀ⁻¹ * (Aᵀ * B) * B⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hB, Matrix.mul_one]
    _ = A * B⁻¹ := by
        rw [hAB, ← Matrix.mul_assoc, nonsing_inv_mul _ (by rwa [det_transpose]), Matrix.one_mul]

/-- For a symmetric complex matrix `Z`, `Z - Zᴴ = 2i Im Z`, the imaginary part `Im Z` being taken
entrywise. -/
theorem IsSymm.sub_conjTranspose {Z : Matrix n n ℂ} (hZ : Z.IsSymm) :
    Z - Zᴴ = (2 * I) • (Z.map Complex.im).map ofReal := by
  rw [map_im_map_ofReal_of_transpose_eq hZ.eq, smul_inv_smul₀ (by simp)]

/-- A matrix is self-adjoint for the bilinear form of the identity matrix, `Aᵀ * 1 = 1 * A`,
exactly when it is symmetric. With `mem_selfAdjointMatricesSubmodule`, `simp` reduces membership
in `selfAdjointMatricesSubmodule 1` to symmetry. -/
@[simp]
theorem isSelfAdjoint_one_iff_isSymm [Fintype n] {R : Type*} [CommRing R] [DecidableEq n]
    {A : Matrix n n R} : (1 : Matrix n n R).IsSelfAdjoint A ↔ A.IsSymm := by
  rw [Matrix.IsSelfAdjoint, Matrix.IsAdjointPair, Matrix.mul_one, Matrix.one_mul, IsSymm]

end Matrix

end
