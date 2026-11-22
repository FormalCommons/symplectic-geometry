/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Tactic.LinearCombination

/-!
# Trace of squares of self-adjoint endomorphisms

Let `B` be a symmetric positive-definite bilinear form on a finite-dimensional vector space over
an ordered field. An endomorphism that is self-adjoint for `B` has nonnegative trace of its
square, and positive trace of its square unless it is zero. In a `B`-orthogonal basis the
`(i, j)` and `(j, i)` matrix entries of such an endomorphism have the same sign, so the trace of
its square is a sum of nonnegative terms.

This is the self-adjoint counterpart of Tau Ceti's
`LinearMap.BilinForm.trace_mul_self_nonpos_of_posDef` for skew-adjoint endomorphisms. The proof
adapts that of Tau Ceti's private lemmas `LinearMap.BilinForm.exists_positive_basis_skew` and
`LinearMap.BilinForm.exists_matrix_trace_mul_self_of_isSelfAdjoint`
(`TauCeti/LinearAlgebra/BilinearForm/SkewAdjoint.lean`), with the sign of the adjoint changed.

## Main results

* `LinearMap.BilinForm.trace_mul_self_nonneg_of_posDef`: the trace of the square of a
  self-adjoint endomorphism is nonnegative.
* `LinearMap.BilinForm.trace_mul_self_pos_of_posDef`: it is positive unless the endomorphism is
  zero.

## References

* J. Hilgert and K.-H. Neeb, *Structure and Geometry of Lie Groups*, Springer (2012),
  Remark 12.2.14, for the trace-square argument in the skew-adjoint case.
-/

public section

open Module

namespace LinearMap.BilinForm

variable {F V : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]

private theorem exists_positive_basis_of_isSelfAdjoint (B : LinearMap.BilinForm F V)
    (hsymm : B.IsSymm) (hpos : B.toQuadraticMap.PosDef) {A : Module.End F V}
    (hA : B.IsSelfAdjoint A) :
    ∃ b : Basis (Fin (finrank F V)) F V,
      (∀ i, 0 < B (b i) (b i)) ∧
        ∀ i j, LinearMap.toMatrix b b A j i * B (b j) (b j) =
          B (b i) (b i) * LinearMap.toMatrix b b A i j := by
  classical
  let _ : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  obtain ⟨b, hb⟩ := exists_orthogonal_basis (isSymm_iff.mp hsymm)
  let d := fun i ↦ B (b i) (b i)
  let M := LinearMap.toMatrix b b A
  have hd (i) : 0 < d i := by
    simpa only [d, LinearMap.BilinMap.toQuadraticMap_apply] using hpos (b i) (b.ne_zero i)
  have hdiag : LinearMap.toMatrix₂ b b B = Matrix.diagonal d := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [LinearMap.toMatrix₂_apply, Matrix.diagonal_apply_eq, d]
    · simp only [LinearMap.toMatrix₂_apply, Matrix.diagonal_apply_ne _ hij]
      exact (LinearMap.BilinForm.iIsOrtho_def.mp hb) i j hij
  have hB : Matrix.toLinearMap₂ b b (Matrix.diagonal d) = B := by
    rw [← hdiag]
    exact Matrix.toLinearMap₂_toMatrix₂ b b B
  have hself : Matrix.IsAdjointPair (Matrix.diagonal d) (Matrix.diagonal d) M M := by
    apply (isAdjointPair_toLinearMap₂
      (b₁ := b) (b₂ := b) (J := Matrix.diagonal d) (J' := Matrix.diagonal d)
      (A := M) (A' := M)).mp
    -- `B.IsSelfAdjoint A` is `IsAdjointPair B B A A` by definition.
    have hA' : IsAdjointPair B B A A := hA
    simpa only [hB, M, Matrix.toLin_toMatrix] using hA'
  rw [Matrix.IsAdjointPair] at hself
  refine ⟨b, hd, fun i j ↦ ?_⟩
  simpa only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.diagonal_mul] using
    congrFun (congrFun hself i) j

private theorem exists_matrix_of_isSelfAdjoint (B : LinearMap.BilinForm F V)
    (hsymm : B.IsSymm) (hpos : B.toQuadraticMap.PosDef) {A : Module.End F V}
    (hA : B.IsSelfAdjoint A) :
    ∃ M : Matrix (Fin (finrank F V)) (Fin (finrank F V)) F,
      LinearMap.trace F V (A * A) = ∑ i, ∑ j, M i j * M j i ∧
      (∀ i j, 0 ≤ M i j * M j i ∧ (M i j ≠ 0 → 0 < M i j * M j i)) ∧ (M = 0 → A = 0) := by
  classical
  obtain ⟨b, hd, hentry⟩ := exists_positive_basis_of_isSelfAdjoint B hsymm hpos hA
  let M := LinearMap.toMatrix b b A
  refine ⟨M, ?_, fun i j ↦ ?_, ?_⟩
  · rw [LinearMap.trace_eq_matrix_trace F b (A * A), LinearMap.toMatrix_mul]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, M]
  · -- `d j * (M i j * M j i) = d i * (M i j) ^ 2`
    have hw : B (b j) (b j) * (M i j * M j i) = B (b i) (b i) * M i j ^ 2 := by
      linear_combination M i j * hentry i j
    refine ⟨nonneg_of_mul_nonneg_right ?_ (hd j), fun h ↦ pos_of_mul_pos_right ?_ (hd j).le⟩
    · rw [hw]
      exact mul_nonneg (hd i).le (sq_nonneg _)
    · rw [hw]
      exact mul_pos (hd i) (sq_pos_of_ne_zero h)
  · exact (LinearMap.toMatrix b b).map_eq_zero_iff.1

/-- An endomorphism that is self-adjoint for a symmetric positive-definite bilinear form has
nonnegative trace of its square. -/
theorem trace_mul_self_nonneg_of_posDef (B : LinearMap.BilinForm F V)
    (hsymm : B.IsSymm) (hpos : B.toQuadraticMap.PosDef) {A : Module.End F V}
    (hA : B.IsSelfAdjoint A) : 0 ≤ LinearMap.trace F V (A * A) := by
  obtain ⟨M, htrace, hterm, _⟩ := exists_matrix_of_isSelfAdjoint B hsymm hpos hA
  rw [htrace]
  exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ (hterm i j).1

/-- A nonzero endomorphism that is self-adjoint for a symmetric positive-definite bilinear form
has positive trace of its square. -/
theorem trace_mul_self_pos_of_posDef (B : LinearMap.BilinForm F V)
    (hsymm : B.IsSymm) (hpos : B.toQuadraticMap.PosDef) {A : Module.End F V}
    (hA : B.IsSelfAdjoint A) (h0 : A ≠ 0) : 0 < LinearMap.trace F V (A * A) := by
  obtain ⟨M, htrace, hterm, hzero⟩ := exists_matrix_of_isSelfAdjoint B hsymm hpos hA
  obtain ⟨i, j, hij⟩ : ∃ i j, M i j ≠ 0 := by
    by_contra! h
    exact h0 (hzero (Matrix.ext h))
  rw [htrace]
  exact Finset.sum_pos' (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ (hterm i j).1)
    ⟨i, Finset.mem_univ _, Finset.sum_pos' (fun j _ ↦ (hterm i j).1)
      ⟨j, Finset.mem_univ _, (hterm i j).2 hij⟩⟩

end LinearMap.BilinForm

end
