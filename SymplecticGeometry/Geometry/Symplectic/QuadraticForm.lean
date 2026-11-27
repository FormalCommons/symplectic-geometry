/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.QuadraticForm
import SymplecticGeometry.LinearAlgebra.TotallyReal.QuadraticForm

/-!
# Lower bounds for the negative index from complex negativity

Let `Q` be a real quadratic form and `J` an almost complex structure. If `Q(v) + Q(Jv) < 0` for
every nonzero `v`, then the negative index of inertia of `Q` is at least the complex dimension
defined by `J`. This is the lower-bound counterpart of Tau Ceti's
`QuadraticForm.sigNeg_le_complexFinrank_of_add_comp_posDef`. It is
`QuadraticForm.finrank_le_two_mul_sigNeg_of_add_comp_neg` for the linear map underlying `J`,
since the real dimension is twice the complex dimension.

## Main declarations

* `QuadraticForm.complexFinrank_le_sigNeg_of_add_comp_neg`: the negative index of inertia of `Q` is
  at least the complex dimension when `Q(v) + Q(Jv) < 0` away from zero.

## References

* [D. Auroux, *Asymptotically holomorphic families of symplectic submanifolds*][Auroux1997]
* J. Milnor, *Morse Theory*, Princeton University Press, 1963, Section 7.
-/

public section

namespace QuadraticForm

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- If `Q(v) + Q(Jv)` is negative for every nonzero `v`, then the negative index of inertia of `Q`
is at least the complex dimension defined by `J`. -/
theorem complexFinrank_le_sigNeg_of_add_comp_neg (Q : QuadraticForm ℝ E)
    (J : TauCeti.AlmostComplexStructure E) (hQJ : ∀ v, v ≠ 0 → Q v + Q (J v) < 0) :
    J.complexFinrank ≤ sigNeg Q := by
  have hE := J.finrank_real_eq_two_mul_complexFinrank
  have h := Q.finrank_le_two_mul_sigNeg_of_add_comp_neg J.toLinearMap hQJ
  omega

end QuadraticForm
