/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.RCLike.Basic
public import TauCeti.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Dot products: isometries, inserted entries and Cauchy–Schwarz

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
* `Matrix.norm_star_dotProduct_sq_le`: Cauchy–Schwarz for the Hermitian product,
  `‖star z ⬝ᵥ v‖² ≤ (∑ᵢ ‖zᵢ‖²) (∑ᵢ ‖vᵢ‖²)`, read off from Mathlib's `norm_inner_le_norm` on
  `EuclideanSpace 𝕜 ι`.
-/

public section

namespace Fin

/-- The star of a tuple with an entry inserted at `j` is the star of the tuple with the star of
the entry inserted at `j`. -/
@[simp]
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
@[simp]
theorem insertNth_dotProduct_insertNth [AddCommMonoid R] [Mul R] {n : ℕ}
    (j : Fin (n + 1)) (a b : R) (x y : Fin n → R) :
    Fin.insertNth (α := fun _ ↦ R) j a x ⬝ᵥ Fin.insertNth (α := fun _ ↦ R) j b y =
      a * b + x ⬝ᵥ y := by
  simp [dotProduct, Fin.sum_univ_succAbove _ j]

/-- **Cauchy–Schwarz for the Hermitian product** `star z ⬝ᵥ v` on `ι → 𝕜`:
`‖star z ⬝ᵥ v‖² ≤ (∑ᵢ ‖zᵢ‖²) (∑ᵢ ‖vᵢ‖²)`. -/
theorem norm_star_dotProduct_sq_le {ι 𝕜 : Type*} [Fintype ι] [RCLike 𝕜] (z v : ι → 𝕜) :
    ‖star z ⬝ᵥ v‖ ^ 2 ≤ (∑ i, ‖z i‖ ^ 2) * ∑ i, ‖v i‖ ^ 2 := by
  have h := norm_inner_le_norm (𝕜 := 𝕜) (WithLp.toLp 2 z) (WithLp.toLp 2 v)
  rw [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, WithLp.ofLp_toLp,
    dotProduct_comm] at h
  rw [← EuclideanSpace.norm_sq_eq, ← EuclideanSpace.norm_sq_eq, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

end Matrix

end
