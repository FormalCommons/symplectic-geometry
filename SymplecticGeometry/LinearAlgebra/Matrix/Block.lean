/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Data.Matrix.Block
import TauCeti.Data.Matrix.Block

/-!
# Block matrices

This file builds block matrices linearly from their blocks, and gives the identities between the
blocks of a square root of `-1`: for a block matrix `M = !![M₁₁, M₁₂; M₂₁, M₂₂]` over a
non-associative ring with `M * M = -1`, the first block column of `M * M` gives two identities
between the blocks of `M`.

## Main definitions

* `Matrix.fromBlocksLinearMap`: `((A, B), (C, D)) ↦ fromBlocks A B C D` as a linear map.

## Main results

* `Matrix.toBlocks₁₁_mul_toBlocks₁₁_add_of_mul_self_eq_neg_one`: `M₁₁² + M₁₂ M₂₁ = -1`.
* `Matrix.toBlocks₂₁_mul_toBlocks₁₁_add_of_mul_self_eq_neg_one`: `M₂₁ M₁₁ + M₂₂ M₂₁ = 0`.
-/

public section

namespace Matrix

section LinearMap

variable {l m n o R α : Type*} [Semiring R] [AddCommMonoid α] [Module R α]

variable (R) in
/-- The block matrix `fromBlocks A B C D` as a linear function of the four blocks
`((A, B), (C, D))`. -/
def fromBlocksLinearMap :
    (Matrix n l α × Matrix n m α) × (Matrix o l α × Matrix o m α) →ₗ[R]
      Matrix (n ⊕ o) (l ⊕ m) α where
  toFun p := fromBlocks p.1.1 p.1.2 p.2.1 p.2.2
  map_add' _ _ := (fromBlocks_add ..).symm
  map_smul' _ _ := (fromBlocks_smul ..).symm

@[simp]
theorem fromBlocksLinearMap_apply
    (p : (Matrix n l α × Matrix n m α) × (Matrix o l α × Matrix o m α)) :
    fromBlocksLinearMap R p = fromBlocks p.1.1 p.1.2 p.2.1 p.2.2 :=
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
