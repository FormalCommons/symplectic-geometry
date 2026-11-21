/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.Matrix
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import TauCeti.LinearAlgebra.Matrix.Diagonal

/-!
# The rank of an endomorphism that is diagonal in a basis

* `LinearMap.finrank_range_eq_card_of_apply_basis_eq_smul`: if an endomorphism `T` of a vector
  space scales each vector `b i` of a finite basis by `d i`, its range has dimension the number
  of `i` with `d i ≠ 0`. This is Mathlib's `Matrix.rank_diagonal` for the matrix of `T` in `b`.
* `Matrix.range_toLpLin_mul_of_isUnit`: multiplying a matrix on the right by an invertible
  matrix does not change its column space, over any commutative ring and for any `L^p` norm.
-/

public section

open Module

open scoped ENNReal

namespace LinearMap

/-- An endomorphism that is diagonal in a finite basis `b`, with diagonal `d`, has rank the
number of nonzero entries of `d`. -/
theorem finrank_range_eq_card_of_apply_basis_eq_smul {K V ι : Type*} [Field K] [DecidableEq K]
    [AddCommGroup V] [Module K V] [Fintype ι] (b : Basis ι K V) {T : Module.End K V}
    {d : ι → K} (h : ∀ i, T (b i) = d i • b i) :
    finrank K (LinearMap.range T) = Fintype.card {i // d i ≠ 0} := by
  classical
  rw [← Matrix.rank_diagonal, ← (b.toMatrix_eq_diagonal_iff b T d).2 h,
    Matrix.rank_eq_finrank_range_toLin _ b b, Matrix.toLin_toMatrix]

end LinearMap

namespace Matrix

/-- Multiplying a matrix `A` on the right by an invertible matrix `B` does not change its column
space: `A * B` and `A` have the same range as linear maps between `L^p` spaces. -/
theorem range_toLpLin_mul_of_isUnit {R m n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (p : ℝ≥0∞) (A : Matrix m n R) {B : Matrix n n R} (hB : IsUnit B) :
    LinearMap.range (toLpLin p p (A * B)) = LinearMap.range (toLpLin p p A) := by
  rw [toLpLin_mul_same]
  exact LinearMap.range_comp_of_range_eq_top _
    (range_toLin_eq_top (PiLp.basisFun p R n) B ((isUnit_iff_isUnit_det B).1 hB))

end Matrix

end
