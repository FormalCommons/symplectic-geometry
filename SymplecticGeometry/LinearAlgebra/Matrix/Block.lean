/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Data.Matrix.Block
import TauCeti.Data.Matrix.Block

/-!
# Block matrices

This file identifies block matrices linearly with their four blocks, and gives the identities
between the blocks of a square root of `-1`: for a block matrix `M = !![M₁₁, M₁₂; M₂₁, M₂₂]` over
a non-associative ring with `M * M = -1`, the first block column of `M * M` gives two identities
between the blocks of `M`.

## Main definitions

* `Matrix.fromBlocksLinearEquiv`: `((A, B), (C, D)) ↦ fromBlocks A B C D` as a linear
  equivalence, whose inverse takes the four blocks.

## Main results

* `Matrix.toBlocks₁₁_mul_toBlocks₁₁_add_of_mul_self_eq_neg_one`: `M₁₁² + M₁₂ M₂₁ = -1`.
* `Matrix.toBlocks₂₁_mul_toBlocks₁₁_add_of_mul_self_eq_neg_one`: `M₂₁ M₁₁ + M₂₂ M₂₁ = 0`.
-/

public section

namespace Matrix

section LinearMap

variable {l m n o R α : Type*} [Semiring R] [AddCommMonoid α] [Module R α]

variable (R) in
/-- The block matrix `fromBlocks A B C D` as a linear equivalence in the four blocks
`((A, B), (C, D))`. Its inverse sends a matrix `M` to its four blocks
`((M.toBlocks₁₁, M.toBlocks₁₂), (M.toBlocks₂₁, M.toBlocks₂₂))`. -/
def fromBlocksLinearEquiv :
    ((Matrix n l α × Matrix n m α) × (Matrix o l α × Matrix o m α)) ≃ₗ[R]
      Matrix (n ⊕ o) (l ⊕ m) α where
  toFun p := fromBlocks p.1.1 p.1.2 p.2.1 p.2.2
  invFun M := ((M.toBlocks₁₁, M.toBlocks₁₂), (M.toBlocks₂₁, M.toBlocks₂₂))
  map_add' _ _ := (fromBlocks_add ..).symm
  map_smul' _ _ := (fromBlocks_smul ..).symm
  left_inv _ := by
    simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁,
      toBlocks_fromBlocks₂₂]
  right_inv := fromBlocks_toBlocks

@[simp]
theorem fromBlocksLinearEquiv_apply
    (p : (Matrix n l α × Matrix n m α) × (Matrix o l α × Matrix o m α)) :
    fromBlocksLinearEquiv R p = fromBlocks p.1.1 p.1.2 p.2.1 p.2.2 :=
  (rfl)

@[simp]
theorem fromBlocksLinearEquiv_symm_apply (M : Matrix (n ⊕ o) (l ⊕ m) α) :
    (fromBlocksLinearEquiv R).symm M =
      ((M.toBlocks₁₁, M.toBlocks₁₂), (M.toBlocks₂₁, M.toBlocks₂₂)) :=
  (rfl)

end LinearMap

variable {m n R : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  [NonAssocRing R]

/-- If `M * M = -1` for a block matrix `M`, then `M₁₁² + M₁₂ M₂₁ = -1`. -/
theorem toBlocks₁₁_mul_toBlocks₁₁_add_of_mul_self_eq_neg_one {M : Matrix (m ⊕ n) (m ⊕ n) R}
    (hM : M * M = -1) :
    M.toBlocks₁₁ * M.toBlocks₁₁ + M.toBlocks₁₂ * M.toBlocks₂₁ = -1 := by
  rw [← toBlocks₁₁_mul, hM, ← fromBlocks_one, fromBlocks_neg, toBlocks_fromBlocks₁₁]

/-- If `M * M = -1` for a block matrix `M`, then `M₂₁ M₁₁ + M₂₂ M₂₁ = 0`. -/
theorem toBlocks₂₁_mul_toBlocks₁₁_add_of_mul_self_eq_neg_one {M : Matrix (m ⊕ n) (m ⊕ n) R}
    (hM : M * M = -1) :
    M.toBlocks₂₁ * M.toBlocks₁₁ + M.toBlocks₂₂ * M.toBlocks₂₁ = 0 := by
  rw [← toBlocks₂₁_mul, hM, ← fromBlocks_one, fromBlocks_neg, toBlocks_fromBlocks₂₁, neg_zero]

end Matrix

end
