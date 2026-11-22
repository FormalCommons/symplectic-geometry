/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import TauCeti.LinearAlgebra.Matrix.DotProduct

/-!
# Dot products: isometries and inserted entries

* `Matrix.star_mulVec_dotProduct_mulVec`: a matrix with orthonormal columns, `Aᴴ * A = 1`,
  preserves the Hermitian product `star z ⬝ᵥ v`. It is the case `M = 1` of Tau Ceti's
  `Matrix.star_dotProduct_conjTranspose_mul_mul_mulVec`, in
  `TauCeti/LinearAlgebra/Matrix/DotProduct.lean`.
* `Fin.star_insertNth`: the star of a tuple with an entry inserted at `j` is the star of the
  tuple with the star of the entry inserted at `j`.
* `Matrix.insertNth_dotProduct_insertNth`: the dot product of two vectors with an entry inserted
  at the same position `j` splits off the product of these entries. It is the analogue for
  `Fin.insertNth` of Mathlib's `Matrix.cons_dotProduct_cons`, and its proof splits the sum with
  `Fin.sum_univ_succAbove`.
-/

public section

namespace Fin

/-- The star of a tuple with an entry inserted at `j` is the star of the tuple with the star of
the entry inserted at `j`. -/
theorem star_insertNth {R : Type*} [Star R] {m : ℕ} (j : Fin (m + 1)) (c : R) (x : Fin m → R) :
    star (Fin.insertNth (α := fun _ ↦ R) j c x) =
      Fin.insertNth (α := fun _ ↦ R) j (star c) (star x) := by
  funext i
  rcases Fin.eq_self_or_eq_succAbove j i with rfl | ⟨k, rfl⟩ <;> simp

end Fin

namespace Matrix

variable {l m R : Type*} [Fintype l] [Fintype m]

/-- A matrix with orthonormal columns, `Aᴴ * A = 1`, preserves the Hermitian product
`star z ⬝ᵥ v`. This is the case `M = 1` of `Matrix.star_dotProduct_conjTranspose_mul_mul_mulVec`.
-/
theorem star_mulVec_dotProduct_mulVec [Semiring R] [StarRing R] [DecidableEq m]
    {A : Matrix l m R} (hA : Aᴴ * A = 1) (z v : m → R) :
    star (A *ᵥ z) ⬝ᵥ (A *ᵥ v) = star z ⬝ᵥ v := by
  classical
  simpa [hA] using (star_dotProduct_conjTranspose_mul_mul_mulVec A 1 z v).symm

/-- The dot product of two vectors with an entry inserted at the same position `j` is the
product of these entries plus the dot product of the remaining vectors. -/
theorem insertNth_dotProduct_insertNth [AddCommMonoid R] [Mul R] {n : ℕ}
    (j : Fin (n + 1)) (a b : R) (x y : Fin n → R) :
    Fin.insertNth (α := fun _ ↦ R) j a x ⬝ᵥ Fin.insertNth (α := fun _ ↦ R) j b y =
      a * b + x ⬝ᵥ y := by
  simp [dotProduct, Fin.sum_univ_succAbove _ j]

end Matrix

end
