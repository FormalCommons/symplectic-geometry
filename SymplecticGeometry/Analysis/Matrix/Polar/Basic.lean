/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Matrix.Polar
public import TauCeti.Analysis.Matrix.Polar.Deformation

/-!
# The right polar decomposition of an invertible matrix

Over `𝕜 = ℝ` or `ℂ`, every invertible matrix `A : GL n 𝕜` factors uniquely as `A = U Q` with `U`
unitary (orthogonal when `𝕜 = ℝ`) and `Q` positive definite: `Q = √(Aᴴ A)` is the square root of
the continuous functional calculus and `U = Units.polarUnitary A`, the same unitary factor as in
the left decomposition `A = √(A Aᴴ) U` of Tau Ceti's `existsUnique_posDef_mul_unitary`. This file
gives the matrix form of Tau Ceti's right polar decomposition of invertible elements
(`Units.polarUnitary_mul_sqrt_star_mul` and
`Units.mul_eq_iff_polarUnitary_eq_and_sqrt_star_mul_eq`), where the positive factor is positive
definite. It also writes the unitary factor and Tau Ceti's polar deformation
`Matrix.GeneralLinearGroup.polarDeformation A t = √(A Aᴴ) ^ (1 - t) U` in the right form
`A (Aᴴ A) ^ (-t / 2)`, which involves `A` alone.

## Main results

* `Matrix.GeneralLinearGroup.posDef_sqrt_star_mul`: the positive factor `√(Aᴴ A)` is positive
  definite.
* `Matrix.GeneralLinearGroup.existsUnique_unitary_mul_posDef`: existence and uniqueness of the
  right polar decomposition `A = U Q` with `U` unitary and `Q` positive definite.
* `Matrix.GeneralLinearGroup.coe_polarDeformation_eq_mul_rpow`: the polar deformation at time
  `t` is `A (Aᴴ A) ^ (-t / 2)`.
* `Matrix.GeneralLinearGroup.coe_polarUnitary_eq_mul_rpow`: the unitary factor is
  `A (Aᴴ A) ^ (-1 / 2)`.

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

/-- **The polar deformation in right form.** At time `t`, the polar deformation
`√(A Aᴴ) ^ (1 - t) U` of `A = √(A Aᴴ) U` is `A (Aᴴ A) ^ (-t / 2)`. -/
theorem coe_polarDeformation_eq_mul_rpow (t : ℝ) :
    (polarDeformation A t : Matrix n n 𝕜) = A * (star (A : Matrix n n 𝕜) * A) ^ (-(t / 2)) := by
  have hu : IsUnit (star (A : Matrix n n 𝕜) * A) := (star A * A).isUnit
  have hP := Units.isStrictlyPositive_sqrt_mul_star A
  set P := CFC.sqrt ((A : Matrix n n 𝕜) * star (A : Matrix n n 𝕜))
  set U := A.polarUnitary
  -- `(Aᴴ A) ^ (-t / 2) = √(Aᴴ A) ^ (-t) = Uᴴ P ^ (-t) U`, so the right side is `P ^ (1 - t) U`.
  have hconj := CFC.rpow_unitary_mul_mul_star (star U) P (-t)
  simp only [Unitary.coe_star, star_star] at hconj
  rw [← neg_div, ← CFC.rpow_sqrt _ _ hu, Units.sqrt_star_mul_eq, hconj, coe_polarDeformation]
  conv_rhs => rw [← Units.sqrt_mul_star_mul_polarUnitary A]
  rw [mul_assoc, ← mul_assoc (U : Matrix n n 𝕜), ← mul_assoc (U : Matrix n n 𝕜),
    Unitary.mul_star_self_of_mem U.property, one_mul, ← mul_assoc, sub_eq_add_neg,
    CFC.rpow_add hP.isUnit, CFC.rpow_one P hP.nonneg]

/-- The unitary polar factor of `A` is `A (Aᴴ A) ^ (-1 / 2)`; over `ℝ` this is the orthogonal
factor `A (AᵀA) ^ (-1 / 2)`. -/
theorem coe_polarUnitary_eq_mul_rpow :
    (A.polarUnitary : Matrix n n 𝕜) = A * (star (A : Matrix n n 𝕜) * A) ^ (-(1 / 2 : ℝ)) := by
  simpa using coe_polarDeformation_eq_mul_rpow A 1

end Matrix.GeneralLinearGroup

end
