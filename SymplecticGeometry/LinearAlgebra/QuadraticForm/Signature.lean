/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Signature

/-!
# The signature of a quadratic form

Mathlib defines the positive and negative indices of inertia `sigPos Q` and `sigNeg Q` of a
quadratic form `Q` over a linearly ordered ring. This file names their difference.

## Main definitions

* `QuadraticForm.signature`: the integer `sigPos Q - sigNeg Q`.

## Main results

* `QuadraticForm.signature_neg`: `(-Q).signature = -Q.signature`.
* `QuadraticMap.Equivalent.signature_eq`: equivalent forms have the same signature.
-/

public section

namespace QuadraticForm

variable {R M M' : Type*} [CommRing R] [LinearOrder R] [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M']

/-- The **signature** of a quadratic form `Q`: its positive index of inertia minus its negative
index of inertia, `sigPos Q - sigNeg Q`, as an integer. -/
noncomputable def signature (Q : QuadraticForm R M) : ℤ :=
  (sigPos Q : ℤ) - sigNeg Q

theorem signature_def (Q : QuadraticForm R M) : Q.signature = (sigPos Q : ℤ) - sigNeg Q :=
  (rfl)

/-- Negating a quadratic form negates its signature. -/
@[simp]
theorem signature_neg (Q : QuadraticForm R M) : (-Q).signature = -Q.signature := by
  rw [signature_def, signature_def, sigPos_neg, sigNeg_neg, neg_sub]

end QuadraticForm

namespace QuadraticMap

variable {R M M' : Type*} [CommRing R] [LinearOrder R] [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M']

/-- Equivalent quadratic forms have the same signature. -/
theorem Equivalent.signature_eq {Q : QuadraticForm R M} {Q' : QuadraticForm R M'}
    (h : Q.Equivalent Q') : Q.signature = Q'.signature := by
  rw [QuadraticForm.signature_def, QuadraticForm.signature_def, h.sigPos_eq, h.sigNeg_eq]

end QuadraticMap

end
