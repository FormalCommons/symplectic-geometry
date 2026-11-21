/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.Rank
public import TauCeti.LinearAlgebra.Matrix.Diagonal

/-!
# The rank of an endomorphism that is diagonal in a basis

* `LinearMap.finrank_range_eq_card_of_apply_basis_eq_smul`: if an endomorphism `T` of a vector
  space scales each vector `b i` of a finite basis by `d i`, its range has dimension the number
  of `i` with `d i ≠ 0`. This is Mathlib's `Matrix.rank_diagonal` for the matrix of `T` in `b`.
* `Matrix.range_toEuclideanLin_mul_of_isUnit`: multiplying a matrix on the right by an invertible
  matrix does not change its column space.
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

namespace Matrix

/-- Multiplying a matrix `A` on the right by an invertible matrix `B` does not change its column
space: `A * B` and `A` have the same range as maps of Euclidean spaces. -/
theorem range_toEuclideanLin_mul_of_isUnit {𝕜 m n : Type*} [RCLike 𝕜]
    [Fintype n] [DecidableEq n] (A : Matrix m n 𝕜) {B : Matrix n n 𝕜} (hB : IsUnit B) :
    LinearMap.range (toEuclideanLin (A * B)) = LinearMap.range (toEuclideanLin A) := by
  have hdet := (isUnit_iff_isUnit_det B).1 hB
  have hsurj : LinearMap.range (toEuclideanLin B) = ⊤ :=
    LinearMap.range_eq_top.2 fun v ↦ ⟨toEuclideanLin B⁻¹ v, by
      rw [← LinearMap.comp_apply, ← toLpLin_mul_same, mul_nonsing_inv _ hdet, toLpLin_one,
        LinearMap.id_apply]⟩
  rw [toLpLin_mul_same, LinearMap.range_comp_of_range_eq_top _ hsurj]

end Matrix

end
