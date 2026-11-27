/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Polar
import SymplecticGeometry.Algebra.Star.Basic

/-!
# The polar decomposition of a unit of square `-1`

Let `a = p u` be the polar decomposition of a unit `a` of a C⋆-algebra (or of any algebra in the
generality of Tau Ceti's `Units.polarUnitary`), with `p = √(a a⋆)` and `u` unitary. If `a * a = -1`
then `a⋆ a = (a a⋆)⁻¹`; since `a⋆ a = u⋆ p² u`, conjugation by `u` inverts `p`,
and hence all its real powers: `u p ^ s u⋆ = p ^ (-s)`.

For matrices, this is the step that keeps the polar deformation of a complex structure among the
complex structures.

## Main results

* `Units.polarUnitary_mul_rpow_mul_star_of_mul_self_eq_neg_one`: for a unit `a` with `a * a = -1`,
  conjugation by its unitary polar factor sends `√(a a⋆) ^ s` to `√(a a⋆) ^ (-s)`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Section 2.5.
-/

public section

open Ring

variable {A : Type*} [PartialOrder A] [Ring A] [StarRing A] [StarOrderedRing A]
  [TopologicalSpace A] [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A] [IsSemitopologicalRing A] [T2Space A]

namespace Units

/-- **Conjugation by the polar unitary factor inverts the positive factor** of a unit `a` of
square `-1`: if `a = √(a a⋆) u` with `u` unitary and `a * a = -1`, then
`u √(a a⋆) ^ s u⋆ = √(a a⋆) ^ (-s)` for every real `s`. -/
theorem polarUnitary_mul_rpow_mul_star_of_mul_self_eq_neg_one (a : Aˣ) (ha : (a : A) * a = -1)
    (s : ℝ) :
    (a.polarUnitary : A) * CFC.sqrt ((a : A) * star (a : A)) ^ s * star (a.polarUnitary : A) =
      CFC.sqrt ((a : A) * star (a : A)) ^ (-s) := by
  set P := CFC.sqrt ((a : A) * star (a : A))
  set u := a.polarUnitary
  have hP : IsStrictlyPositive P := isStrictlyPositive_sqrt_mul_star a
  have hu : (u : A) * star (u : A) = 1 := Unitary.mul_star_self_of_mem u.property
  -- `u⋆ P u = √(a⋆ a) = √((a a⋆)⁻¹) = P⁻¹`.
  have hsqrt : star (u : A) * P * u = P⁻¹ʳ := by
    rw [← sqrt_star_mul_eq, SymplecticGeometry.star_mul_self_eq_inverse_of_mul_self_eq_neg_one ha,
      CFC.sqrt_ringInverse]
  have hconj : P = u * P⁻¹ʳ * star (u : A) := by
    rw [← hsqrt]
    calc P = (u * star (u : A)) * P * (u * star (u : A)) := by rw [hu, one_mul, mul_one]
      _ = _ := by noncomm_ring
  conv_rhs => rw [hconj, CFC.rpow_unitary_mul_mul_star, CFC.inverse_eq_rpow_neg_one hP,
    CFC.rpow_rpow P _ _ hP, neg_one_mul, neg_neg]

end Units

end
