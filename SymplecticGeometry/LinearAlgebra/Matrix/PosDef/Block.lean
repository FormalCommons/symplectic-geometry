/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Positive definiteness of block diagonal matrices

The block diagonal matrix `fromBlocks A 0 0 D` is positive (semi)definite exactly when both
diagonal blocks `A` and `D` are. The index types are arbitrary, as in Mathlib's `Matrix.PosDef`,
which tests the quadratic form on finitely supported vectors: such a vector on `m ⊕ n` is
`Finsupp.sumElim x y`, and the quadratic form of `fromBlocks A 0 0 D` at it is the sum of those
of `A` at `x` and of `D` at `y`.

## Main results

* `Matrix.posSemidef_fromBlocks_zero_zero_iff`:
  `(fromBlocks A 0 0 D).PosSemidef ↔ A.PosSemidef ∧ D.PosSemidef`.
* `Matrix.posDef_fromBlocks_zero_zero_iff`: `(fromBlocks A 0 0 D).PosDef ↔ A.PosDef ∧ D.PosDef`.
-/

public section

namespace Matrix

variable {m n R : Type*} [Ring R] [StarRing R]
  {A : Matrix m m R} {D : Matrix n n R}

/-- The quadratic form of a block diagonal matrix at `Finsupp.sumElim x y` is the sum of the
quadratic forms of its diagonal blocks at `x` and at `y`. -/
private lemma sum_sum_fromBlocks_zero_zero (x : m →₀ R) (y : n →₀ R) :
    ((x.sumElim y).sum fun i a ↦ (x.sumElim y).sum fun j b ↦
        star a * fromBlocks A 0 0 D i j * b) =
      (x.sum fun i a ↦ x.sum fun j b ↦ star a * A i j * b) +
        (y.sum fun i a ↦ y.sum fun j b ↦ star a * D i j * b) := by
  simp [Finsupp.sum_sumElim, Function.comp_def]

variable [PartialOrder R]

/-- The block diagonal matrix with diagonal blocks `A` and `D` is positive semidefinite exactly
when `A` and `D` both are. -/
@[simp]
theorem posSemidef_fromBlocks_zero_zero_iff [AddLeftMono R] :
    (fromBlocks A 0 0 D).PosSemidef ↔ A.PosSemidef ∧ D.PosSemidef := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨hA, hD⟩ ↦ ⟨hA.isHermitian.fromBlocks (by simp) hD.isHermitian,
    fun z ↦ ?_⟩⟩
  · convert h.submatrix Sum.inl
    ext; simp
  · convert h.submatrix Sum.inr
    ext; simp
  rw [← Finsupp.comapDomain_sumElim_comapDomain z, sum_sum_fromBlocks_zero_zero]
  exact add_nonneg (hA.2 _) (hD.2 _)

/-- The block diagonal matrix with diagonal blocks `A` and `D` is positive definite exactly when
`A` and `D` both are. -/
@[simp]
theorem posDef_fromBlocks_zero_zero_iff [AddLeftMono R] :
    (fromBlocks A 0 0 D).PosDef ↔ A.PosDef ∧ D.PosDef := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨hA, hD⟩ ↦ ⟨hA.isHermitian.fromBlocks (by simp) hD.isHermitian,
    fun z hz ↦ ?_⟩⟩
  · convert h.submatrix Sum.inl_injective
    ext; simp
  · convert h.submatrix Sum.inr_injective
    ext; simp
  rw [← Finsupp.comapDomain_sumElim_comapDomain z] at hz ⊢
  rw [sum_sum_fromBlocks_zero_zero]
  by_cases hx : Finsupp.comapDomain Sum.inl z Sum.inl_injective.injOn = 0
  · have hy : Finsupp.comapDomain Sum.inr z Sum.inr_injective.injOn ≠ 0 := by
      rintro hy
      simp [hx, hy] at hz
    exact add_pos_of_nonneg_of_pos (hA.posSemidef.2 _) (hD.2 hy)
  · exact add_pos_of_pos_of_nonneg (hA.2 hx) (hD.posSemidef.2 _)

end Matrix

end
