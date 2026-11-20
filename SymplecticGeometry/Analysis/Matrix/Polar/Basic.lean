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
definite.

## Main results

* `Matrix.GeneralLinearGroup.posDef_sqrt_star_mul`: the positive factor `√(Aᴴ A)` is positive
  definite.
* `Matrix.GeneralLinearGroup.existsUnique_unitary_mul_posDef`: existence and uniqueness of the
  right polar decomposition `A = U Q` with `U` unitary and `Q` positive definite.

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

end Matrix.GeneralLinearGroup

end
