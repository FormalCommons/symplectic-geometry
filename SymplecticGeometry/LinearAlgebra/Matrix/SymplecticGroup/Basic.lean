/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.SymplecticGroup
public import TauCeti.LinearAlgebra.SymplecticGroup

/-!
# The matrix `J` and the symplectic group

The entries of Mathlib's `Matrix.J l R`, the block matrix `fromBlocks 0 (-1) 1 0`, are given
block by block as `simp` lemmas, so that `simp` evaluates `J` at indices `Sum.inl i`, `Sum.inr j`.

The inverse `A⁻¹` of a symplectic matrix, as a matrix, is symplectic, since it is the inverse of
`A` in the group `symplecticGroup l R` (Mathlib's `SymplecticGroup.coe_inv'`).

Over a commutative star ring `R`, the conjugate transpose `Aᴴ` of a matrix `A` is the transpose of
its entrywise conjugate. Both operations preserve the symplectic group `Sp(2n, R)` (Mathlib's
`SymplecticGroup.transpose_mem` and `SymplecticGroup.map_mem`), so `Aᴴ` is symplectic exactly
when `A` is.

## Main results

* `Matrix.J_inl_inl`, `Matrix.J_inl_inr`, `Matrix.J_inr_inl`, `Matrix.J_inr_inr`: the four
  blocks of `Matrix.J`.
* `Matrix.neg_J_mul_eq_fromBlocks`: the blocks of `-J * M` in terms of those of `M`.
* `SymplecticGroup.inv_mem`: the inverse of a symplectic matrix is symplectic.
* `SymplecticGroup.star_mem`: the conjugate transpose of a symplectic matrix is symplectic.
* `SymplecticGroup.star_mem_iff`: a matrix is symplectic exactly when its conjugate transpose is.
* `Matrix.IsSymm.mem_symplecticGroup_iff`: a symmetric matrix `P` is symplectic exactly when
  `(J P)² = -1`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Section 2.2.
-/

public section

namespace Matrix

variable {l R : Type*} [DecidableEq l] [CommRing R] (i j : l)

/-- The upper left block of `Matrix.J` is zero. -/
@[simp]
theorem J_inl_inl : J l R (.inl i) (.inl j) = 0 := rfl

/-- The upper right block of `Matrix.J` is `-1`. -/
@[simp]
theorem J_inl_inr : J l R (.inl i) (.inr j) = -(1 : Matrix l l R) i j := rfl

/-- The lower left block of `Matrix.J` is `1`. -/
@[simp]
theorem J_inr_inl : J l R (.inr i) (.inl j) = (1 : Matrix l l R) i j := rfl

/-- The lower right block of `Matrix.J` is zero. -/
@[simp]
theorem J_inr_inr : J l R (.inr i) (.inr j) = 0 := rfl

section Mul

variable [Fintype l]

/-- Left multiplication by `-J`, the block matrix `fromBlocks 0 1 (-1) 0`, moves the lower blocks
of a matrix up and the negated upper blocks down:
`-J * fromBlocks A B C D = fromBlocks C D (-A) (-B)`. -/
theorem neg_J_mul_eq_fromBlocks (M : Matrix (l ⊕ l) (l ⊕ l) R) :
    -J l R * M = fromBlocks M.toBlocks₂₁ M.toBlocks₂₂ (-M.toBlocks₁₁) (-M.toBlocks₁₂) := by
  conv_lhs => rw [← fromBlocks_toBlocks M]
  simp [Matrix.J, fromBlocks_neg, fromBlocks_multiply]

end Mul

section IsSymm

variable [Fintype l]

/-- A symmetric matrix `P` is symplectic, `Pᵀ J P = J`, exactly when `J P` squares to `-1`. -/
theorem IsSymm.mem_symplecticGroup_iff {P : Matrix (l ⊕ l) (l ⊕ l) R} (hP : P.IsSymm) :
    P ∈ symplecticGroup l R ↔ J l R * P * (J l R * P) = -1 := by
  rw [SymplecticGroup.mem_iff_neg_J_mul_transpose_mul_J_mul_eq_one, hP.eq, neg_eq_iff_eq_neg,
    Matrix.mul_assoc (J l R * P)]

end IsSymm

end Matrix

open Matrix

namespace SymplecticGroup

section Inv

variable {l : Type*} [Fintype l] [DecidableEq l] {R : Type*} [CommRing R]
  {A : Matrix (l ⊕ l) (l ⊕ l) R}

/-- The inverse `A⁻¹` (`Matrix.inv`) of a symplectic matrix `A` is symplectic. -/
theorem inv_mem (hA : A ∈ symplecticGroup l R) : A⁻¹ ∈ symplecticGroup l R := by
  simpa only [coe_inv'] using ((⟨A, hA⟩ : symplecticGroup l R)⁻¹).property

end Inv

variable {l : Type*} [Fintype l] [DecidableEq l] {R : Type*} [CommRing R] [StarRing R]
  {A : Matrix (l ⊕ l) (l ⊕ l) R}

/-- The conjugate transpose `Aᴴ` of a symplectic matrix over a commutative star ring is
symplectic, being the transpose of the entrywise conjugate of `A`. -/
theorem star_mem (hA : A ∈ symplecticGroup l R) : star A ∈ symplecticGroup l R := by
  rw [star_eq_conjTranspose, conjTranspose]
  exact transpose_mem (map_mem hA (starRingEnd R))

/-- A matrix is symplectic exactly when its conjugate transpose is. -/
@[simp]
theorem star_mem_iff : star A ∈ symplecticGroup l R ↔ A ∈ symplecticGroup l R :=
  ⟨fun h ↦ star_star A ▸ star_mem h, star_mem⟩

end SymplecticGroup

end
