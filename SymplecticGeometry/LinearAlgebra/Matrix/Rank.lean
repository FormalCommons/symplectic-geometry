/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import TauCeti.LinearAlgebra.Matrix.Diagonal

/-!
# The rank of an endomorphism that is diagonal in a basis

* `LinearMap.finrank_range_eq_card_of_apply_basis_eq_smul`: if an endomorphism `T` of a vector
  space scales each vector `b i` of a finite basis by `d i`, its range has dimension the number
  of `i` with `d i ≠ 0`. This is Mathlib's `Matrix.rank_diagonal` for the matrix of `T` in `b`.
-/

public section

open Module

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

end
