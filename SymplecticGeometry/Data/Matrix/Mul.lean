/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Data.Matrix.Mul

/-!
# Injectivity and surjectivity of a matrix acting on vectors

* `Matrix.mulVec_injective_of_mul_eq_one`: a (possibly rectangular) matrix `A` with a left
  inverse, `B * A = 1`, acts injectively on vectors. Mathlib's
  `Matrix.mulVec_injective_of_isUnit`, in `Mathlib/Data/Matrix/Mul.lean`, is the case of a
  square invertible matrix.
* `Matrix.mulVec_surjective_iff_of_mul_eq_mul`: scaling the rows and the
  columns of a (possibly rectangular) matrix by units, `B i j * a j = b i * A i j`, does
  not change whether it acts surjectively on vectors.
-/

public section

open Function

namespace Matrix

variable {l m R : Type*} [Fintype l] [Fintype m]

/-- A matrix with a left inverse acts injectively on vectors: `A.mulVec` is injective. -/
theorem mulVec_injective_of_mul_eq_one [Semiring R] [DecidableEq m] {A : Matrix l m R}
    {B : Matrix m l R} (h : B * A = 1) : Injective A.mulVec := fun z w hzw ↦ by
  simpa [mulVec_mulVec, h] using congrArg (B *ᵥ ·) hzw

omit [Fintype l] in
/-- If `B i j * a j = b i * A i j` for all entries, with `a` and `b` units, that is, if `B` is
`A` with row `i` multiplied by `b i` and column `j` by the inverse of `a j`, then `B` acts
surjectively on vectors if and only if `A` does. -/
theorem mulVec_surjective_iff_of_mul_eq_mul [Semiring R] {A B : Matrix l m R} {a : m → R}
    {b : l → R} (ha : IsUnit a) (hb : IsUnit b) (h : ∀ i j, B i j * a j = b i * A i j) :
    Surjective B.mulVec ↔ Surjective A.mulVec := by
  have e : B.mulVec ∘ (a * ·) = (b * ·) ∘ A.mulVec := funext fun x ↦ funext fun i ↦ by
    simp [mulVec, dotProduct, Finset.mul_sum, ← mul_assoc, h]
  rw [← Surjective.of_comp_iff _ (Units.mulLeft_bijective ha.unit).surjective, IsUnit.unit_spec,
    e, Surjective.of_comp_iff' (hb.unit_spec ▸ Units.mulLeft_bijective hb.unit)]

end Matrix

end
