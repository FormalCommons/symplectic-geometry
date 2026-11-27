/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Matrix.Polar

/-!
# The right polar decomposition of an invertible matrix

Over `𝕜 = ℝ` or `ℂ`, every invertible matrix `A : GL n 𝕜` factors uniquely as `A = U Q` with `U`
unitary (orthogonal when `𝕜 = ℝ`) and `Q` positive definite: `Q = √(Aᴴ A)` is the square root of
the continuous functional calculus and `U = Units.polarUnitary A`, the same unitary factor as in
the left decomposition `A = √(A Aᴴ) U` of Tau Ceti's `existsUnique_posDef_mul_unitary`. This file
gives the matrix form of Tau Ceti's right polar decomposition of invertible elements
(`Units.polarUnitary_mul_sqrt_star_mul` and
`Units.mul_eq_iff_polarUnitary_eq_and_sqrt_star_mul_eq`), where the positive factor is positive
definite, and writes the unitary factor as `U = A (Aᴴ A) ^ (-1 / 2)`.

## Main results

* `Matrix.GeneralLinearGroup.posDef_sqrt_star_mul`: the positive factor `√(Aᴴ A)` is positive
  definite.
* `Matrix.GeneralLinearGroup.existsUnique_unitary_mul_posDef`: existence and uniqueness of the
  right polar decomposition `A = U Q` with `U` unitary and `Q` positive definite.
* `Matrix.GeneralLinearGroup.coe_polarUnitary_eq_mul_rpow`: the unitary factor is
  `A (Aᴴ A) ^ (-1 / 2)`.
* `Matrix.GeneralLinearGroup.coe_polarUnitary_reindex`: the unitary factor commutes with
  reindexing rows and columns, as Tau Ceti's `Units.coe_polarUnitary_map` gives for the star
  algebra equivalence `Matrix.reindexStarAlgEquiv`.

## References

* Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition, Graduate Texts
  in Mathematics 222, Springer, 2015, Section 2.5.
-/

public section

open scoped MatrixOrder ComplexOrder

namespace Matrix.GeneralLinearGroup

variable {n 𝕜 : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] (A : GL n 𝕜)

/-- The positive factor `√(Aᴴ A)` of the right polar decomposition of an invertible matrix is
positive definite. -/
theorem posDef_sqrt_star_mul : (CFC.sqrt (star (A : Matrix n n 𝕜) * (A : Matrix n n 𝕜))).PosDef :=
  isStrictlyPositive_iff_posDef.1 (Units.isStrictlyPositive_sqrt_star_mul A)

/-- **The right polar decomposition of an invertible matrix.** Every `A : GL n 𝕜` is uniquely a
product `U Q` of a unitary matrix `U` and a positive definite matrix `Q`; the factors are
`U = Units.polarUnitary A` and `Q = √(Aᴴ A)`. Over `ℝ`, `U` is orthogonal. -/
theorem existsUnique_unitary_mul_posDef :
    ∃! UQ : unitaryGroup n 𝕜 × Matrix n n 𝕜, UQ.2.PosDef ∧ UQ.1 * UQ.2 = A := by
  refine ⟨(Units.polarUnitary A, CFC.sqrt (star (A : Matrix n n 𝕜) * A)),
    ⟨posDef_sqrt_star_mul A, Units.polarUnitary_mul_sqrt_star_mul A⟩, ?_⟩
  rintro ⟨U, Q⟩ ⟨hQ, h⟩
  obtain ⟨hU, hQ'⟩ :=
    (Units.mul_eq_iff_polarUnitary_eq_and_sqrt_star_mul_eq A hQ.posSemidef.nonneg).1 h
  exact Prod.ext hU.symm hQ'.symm

/-- The unitary polar factor of `A` is `A (Aᴴ A) ^ (-1 / 2)`; over `ℝ` this is the orthogonal
factor `A (AᵀA) ^ (-1 / 2)`. -/
theorem coe_polarUnitary_eq_mul_rpow :
    (A.polarUnitary : Matrix n n 𝕜) = A * (star (A : Matrix n n 𝕜) * A) ^ (-(1 / 2 : ℝ)) := by
  have hu : IsUnit (star (A : Matrix n n 𝕜) * A) := (star A * A).isUnit
  have hQ := Units.isStrictlyPositive_sqrt_star_mul A
  -- `(Aᴴ A) ^ (-1 / 2) = √(Aᴴ A) ^ (-1)`, and `A = U √(Aᴴ A)`.
  rw [show (-(1 / 2 : ℝ)) = -1 / 2 by ring, ← CFC.rpow_sqrt _ _ hu]
  have h1 : CFC.sqrt (star (A : Matrix n n 𝕜) * A) * CFC.sqrt (star (A : Matrix n n 𝕜) * A) ^
      (-1 : ℝ) = 1 := by
    simpa [CFC.rpow_one _ hQ.nonneg] using CFC.rpow_mul_rpow_neg 1 hQ
  calc (A.polarUnitary : Matrix n n 𝕜)
      = A.polarUnitary * CFC.sqrt (star (A : Matrix n n 𝕜) * A) *
          CFC.sqrt (star (A : Matrix n n 𝕜) * A) ^ (-1 : ℝ) := by rw [mul_assoc, h1, mul_one]
    _ = _ := by rw [Units.polarUnitary_mul_sqrt_star_mul]

/-- The unitary polar factor commutes with reindexing: the unitary factor of `A` reindexed along
`e : n ≃ m` is the unitary factor of `A`, reindexed along `e`. -/
theorem coe_polarUnitary_reindex {m : Type*} [Fintype m] [DecidableEq m] (e : n ≃ m) :
    ((reindex 𝕜 e A).polarUnitary : Matrix m m 𝕜) =
      Matrix.reindex e e (A.polarUnitary : Matrix n n 𝕜) := by
  have h : reindex 𝕜 e A =
      Units.map ((reindexStarAlgEquiv 𝕜 𝕜 e : Matrix n n 𝕜 ≃⋆ₐ[𝕜] Matrix m m 𝕜) :
        Matrix n n 𝕜 →* Matrix m m 𝕜) A := Units.ext (by simp)
  rw [h, Units.coe_polarUnitary_map]
  simp

end Matrix.GeneralLinearGroup

end
