/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Matrix.Polar.Deformation
import SymplecticGeometry.Analysis.Matrix.Polar.Basic
import SymplecticGeometry.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Polar

/-!
# The polar deformation of an invertible matrix in right form

Tau Ceti's polar deformation of `A : GL n 𝕜`, over `𝕜 = ℝ` or `ℂ`, is
`Matrix.GeneralLinearGroup.polarDeformation A t = √(A Aᴴ) ^ (1 - t) U`, where `A = √(A Aᴴ) U` is
the left polar decomposition. This file writes it in the right form `A (Aᴴ A) ^ (-t / 2)`, which
involves `A` alone: conjugating by the unitary factor turns `√(A Aᴴ)` into `√(Aᴴ A)`. It also
shows that the deformation of a matrix of square `-1`, such as the matrix of a complex structure,
keeps square `-1` at every time, and that the deformation of a positive semidefinite matrix is a
real power of it.

## Main results

* `Matrix.GeneralLinearGroup.coe_polarDeformation_eq_mul_rpow`: the polar deformation at time
  `t` is `A (Aᴴ A) ^ (-t / 2)`.
* `Matrix.GeneralLinearGroup.polarDeformation_mul_self_of_mul_self_eq_neg_one`: the polar
  deformation of a matrix of square `-1` has square `-1` at every time.
* `Matrix.GeneralLinearGroup.coe_polarDeformation_of_nonneg`: for `A ≥ 0`, the polar
  deformation at time `t` is `A ^ (1 - t)`.

## References

* Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition, Graduate Texts
  in Mathematics 222, Springer, 2015, Section 2.5.
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Section 2.2, Proposition 2.2.4, and Section 2.5.
-/

public section

open scoped MatrixOrder ComplexOrder

namespace Matrix.GeneralLinearGroup

variable {n 𝕜 : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] (A : GL n 𝕜)

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
  have hUU : (U : Matrix n n 𝕜) * star (U : Matrix n n 𝕜) = 1 :=
    Unitary.mul_star_self_of_mem U.property
  rw [sub_eq_add_neg, CFC.rpow_add hP.isUnit, CFC.rpow_one P hP.nonneg]
  calc P * P ^ (-t) * (U : Matrix n n 𝕜)
      = P * ((U : Matrix n n 𝕜) * star (U : Matrix n n 𝕜)) * P ^ (-t) * U := by
        rw [hUU, mul_one]
    _ = _ := by noncomm_ring

/-- **The polar deformation preserves square `-1`.** If `A * A = -1`, then at every time `t` the
polar deformation `√(A Aᴴ) ^ (1 - t) U` of `A = √(A Aᴴ) U` also squares to `-1`: conjugation by
`U` inverts the powers of `√(A Aᴴ)`, so the square is `U * U = A * A`. -/
theorem polarDeformation_mul_self_of_mul_self_eq_neg_one {A : GL n 𝕜}
    (hA : (A : Matrix n n 𝕜) * A = -1) (t : ℝ) :
    (polarDeformation A t : Matrix n n 𝕜) * polarDeformation A t = -1 := by
  set P := CFC.sqrt ((A : Matrix n n 𝕜) * star (A : Matrix n n 𝕜))
  set U := (A.polarUnitary : Matrix n n 𝕜)
  have hP : IsStrictlyPositive P := Units.isStrictlyPositive_sqrt_mul_star A
  have hU : star U * U = 1 := Unitary.star_mul_self_of_mem A.polarUnitary.property
  -- `(P ^ s U) ^ 2 = P ^ s (U P ^ s U⋆) U ^ 2 = P ^ s P ^ (-s) U ^ 2 = U ^ 2` for every `s`.
  have key (s : ℝ) : P ^ s * U * (P ^ s * U) = U * U := by
    have h := Units.polarUnitary_mul_rpow_mul_star_of_mul_self_eq_neg_one A hA s
    calc P ^ s * U * (P ^ s * U) = P ^ s * U * P ^ s * (star U * U) * U := by
          rw [hU]; noncomm_ring
      _ = P ^ s * (U * P ^ s * star U) * (U * U) := by noncomm_ring
      _ = U * U := by rw [h, CFC.rpow_mul_rpow_neg s hP, one_mul]
  rw [coe_polarDeformation, key, ← key 1, CFC.rpow_one P hP.nonneg,
    Units.sqrt_mul_star_mul_polarUnitary, hA]

/-- **The polar deformation of a positive semidefinite matrix.** If `A ≥ 0`, then its polar
deformation at time `t` is the power `A ^ (1 - t)`. -/
theorem coe_polarDeformation_of_nonneg {A : GL n 𝕜} (hA : 0 ≤ (A : Matrix n n 𝕜)) (t : ℝ) :
    (polarDeformation A t : Matrix n n 𝕜) = (A : Matrix n n 𝕜) ^ (1 - t) := by
  rw [coe_polarDeformation, Units.polarUnitary_eq_one hA, hA.isSelfAdjoint.star_eq,
    CFC.sqrt_mul_self _ hA, OneMemClass.coe_one, mul_one]

end Matrix.GeneralLinearGroup

end
