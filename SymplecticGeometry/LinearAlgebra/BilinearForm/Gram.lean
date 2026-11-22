/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The vector dual to a linear form, through the inverse Gram matrix

Let `B` be a bilinear form on a module `M` over a commutative ring, and `b` a finite basis of `M`
whose Gram matrix `G = BilinForm.toMatrix b B` has an invertible determinant. For a linear form
`ξ` on `M`, the vector `u = ∑ᵢⱼ G⁻¹ᵢⱼ ξ(bᵢ) bⱼ` satisfies `B u = ξ`
(`LinearMap.BilinForm.apply_sum_inv_toMatrix_smul`). No symmetry of `B` is needed.
-/

public section

namespace LinearMap.BilinForm

open Module

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]

/-- **The vector dual to a linear form.** If the Gram matrix `G` of a bilinear form `B` in a basis
`b` has an invertible determinant, then for every linear form `ξ` the vector
`∑ᵢⱼ G⁻¹ᵢⱼ ξ(bᵢ) bⱼ` is sent to `ξ` by `B`. -/
theorem apply_sum_inv_toMatrix_smul (B : LinearMap.BilinForm R M) (b : Basis ι R M)
    (hB : IsUnit (toMatrix b B).det) (ξ : M →ₗ[R] R) :
    B (∑ i, ∑ j, (toMatrix b B)⁻¹ i j • ξ (b i) • b j) = ξ := by
  set G := toMatrix b B
  have hG : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul _ hB
  refine b.ext fun c ↦ ?_
  have h (i : ι) : ∑ j, G⁻¹ i j * B (b j) (b c) = (1 : Matrix ι ι R) i c := by
    simp only [← hG, Matrix.mul_apply, G, toMatrix_apply]
  simp only [_root_.map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul]
  simp_rw [mul_left_comm (G⁻¹ _ _), ← Finset.mul_sum, h, Matrix.one_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

end LinearMap.BilinForm

end
