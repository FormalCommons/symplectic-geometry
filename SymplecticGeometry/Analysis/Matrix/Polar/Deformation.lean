/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.Matrix.Polar.Basic
public import TauCeti.Analysis.Matrix.Polar.Deformation

/-!
# The polar deformation of an invertible matrix in right form

Tau Ceti's polar deformation of `A : GL n 𝕜`, over `𝕜 = ℝ` or `ℂ`, is
`Matrix.GeneralLinearGroup.polarDeformation A t = √(A Aᴴ) ^ (1 - t) U`, where `A = √(A Aᴴ) U` is
the left polar decomposition. This file writes it in the right form `A (Aᴴ A) ^ (-t / 2)`, which
involves `A` alone: conjugating by the unitary factor turns `√(A Aᴴ)` into `√(Aᴴ A)`.

## Main results

* `Matrix.GeneralLinearGroup.coe_polarDeformation_eq_mul_rpow`: the polar deformation at time
  `t` is `A (Aᴴ A) ^ (-t / 2)`.

## References

* Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition, Graduate Texts
  in Mathematics 222, Springer, 2015, Section 2.5.
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Section 2.2, Proposition 2.2.4.
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

end Matrix.GeneralLinearGroup

end
