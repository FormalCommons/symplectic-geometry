/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Signature
import SymplecticGeometry.LinearAlgebra.QuadraticForm.Signature
import TauCeti.LinearAlgebra.TotallyReal.QuadraticForm

/-!
# Lower bounds for the negative index from negativity along a linear map

Let `Q` be a quadratic form over a linearly ordered field and `T` a linear endomorphism. If
`Q(v) + Q(Tv) < 0` for every nonzero `v`, then the dimension of the space is at most twice the
negative index of inertia of `Q`. This is the lower-bound counterpart of Tau Ceti's
`QuadraticForm.two_mul_sigNeg_le_finrank_of_add_comp_posDef`.

The hypothesis does not make `Q` nondegenerate, so the proof does not go through the negative
index of `-Q` alone. It takes a subspace on which `Q` is nonnegative, of dimension complementary
to `sigNeg Q` (`QuadraticForm.exists_finrank_add_sigNeg_eq_and_nonneg`), and bounds it by half the
dimension with Tau Ceti's `QuadraticForm.two_mul_finrank_le_of_add_comp_posDef` applied to `-Q`.

## Main declarations

* `QuadraticForm.finrank_le_two_mul_sigNeg_of_add_comp_neg`: the dimension is at most twice the
  negative index of inertia when `Q(v) + Q(Tv) < 0` away from zero.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, Section 7.
-/

public section

open Module

namespace QuadraticForm

variable {K E : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable [AddCommGroup E] [Module K E]

/-- If `Q(v) + Q(Tv)` is negative for every nonzero `v`, for a linear endomorphism `T`, then the
dimension of `E` is at most twice the negative index of inertia of `Q`. In infinite dimension both
sides are `0`. -/
theorem finrank_le_two_mul_sigNeg_of_add_comp_neg (Q : QuadraticForm K E) (T : E →ₗ[K] E)
    (hQT : ∀ v, v ≠ 0 → Q v + Q (T v) < 0) : finrank K E ≤ 2 * sigNeg Q := by
  by_cases hfin : FiniteDimensional K E
  swap
  · simp [finrank_of_not_finite hfin]
  obtain ⟨W, hWdim, hW⟩ := exists_finrank_add_sigNeg_eq_and_nonneg Q
  have hnegT : (-Q + (-Q).comp T).PosDef := fun v hv ↦ by
    simpa [neg_add, add_comm] using neg_pos.mpr (hQT v hv)
  have h := (-Q).two_mul_finrank_le_of_add_comp_posDef T hnegT fun v hv ↦ by
    simpa using hW v hv
  omega

end QuadraticForm
