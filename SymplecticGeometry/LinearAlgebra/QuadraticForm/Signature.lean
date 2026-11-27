/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Signature
public import TauCeti.LinearAlgebra.QuadraticForm.Signature

/-!
# The signature of a quadratic form

Mathlib defines the positive and negative indices of inertia `sigPos Q` and `sigNeg Q` of a
quadratic form `Q` over a linearly ordered ring. This file names their difference, and gives a
subspace on which `Q` is nonnegative whose dimension is complementary to `sigNeg Q`.

## Main definitions

* `QuadraticForm.signature`: the integer `sigPos Q - sigNeg Q`.

## Main results

* `QuadraticForm.signature_neg`: `(-Q).signature = -Q.signature`.
* `QuadraticForm.signature_smul_of_pos`: scaling by a positive scalar keeps the signature.
* `QuadraticForm.sigPos_zero_of_nontrivial`: the zero form has positive index of inertia zero.
* `QuadraticForm.signature_zero`: the zero form has signature zero.
* `QuadraticMap.Equivalent.signature_eq`: equivalent forms have the same signature.
* `QuadraticForm.exists_finrank_add_sigNeg_eq_and_nonneg`: in finite dimension there is a subspace
  on which `Q` is nonnegative, of dimension `finrank K V - sigNeg Q`.
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

/-- Multiplying a quadratic form by a positive scalar does not change its signature. -/
@[simp]
theorem signature_smul_of_pos [IsStrictOrderedRing R] (Q : QuadraticForm R M) {a : R}
    (ha : 0 < a) : (a • Q).signature = Q.signature := by
  rw [signature_def, signature_def, sigPos_smul_of_pos Q ha, sigNeg_smul_of_pos Q ha]

/-- The zero quadratic form has positive index of inertia zero. -/
@[simp]
theorem sigPos_zero_of_nontrivial [Nontrivial R] : sigPos (0 : QuadraticForm R M) = 0 := by
  obtain ⟨V, hV, hpos⟩ := exists_submodule_finrank_eq_sigPos_and_posDef (0 : QuadraticForm R M)
  have : Subsingleton V := (subsingleton_iff_forall_eq 0).mpr fun x ↦ by
    by_contra hx
    simpa using hpos x hx
  rw [← hV, Module.finrank_zero_of_subsingleton]

/-- The zero quadratic form has signature zero. -/
@[simp]
theorem signature_zero [Nontrivial R] : (0 : QuadraticForm R M).signature = 0 := by
  rw [signature_def, sigPos_zero_of_nontrivial, ← sigPos_neg, neg_zero, sigPos_zero_of_nontrivial,
    Nat.cast_zero, sub_zero]

section Field

open Module

variable {K V : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- A quadratic form on a finite-dimensional space is nonnegative on some subspace whose dimension
is that of the space minus the negative index of inertia. One such subspace is the sum of a
maximal positive-definite subspace and the radical. -/
theorem exists_finrank_add_sigNeg_eq_and_nonneg (Q : QuadraticForm K V) :
    ∃ W : Submodule K V, finrank K W + sigNeg Q = finrank K V ∧ ∀ v ∈ W, 0 ≤ Q v := by
  obtain ⟨A, hAdim, hA⟩ := exists_finrank_eq_sigPos_and_posDef Q
  have hdisj : A ⊓ Q.radical = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    by_contra hv0
    have hpos := hA ⟨v, hv.1⟩ (by simpa using hv0)
    rw [QuadraticMap.restrict_apply, (QuadraticMap.mem_radical_iff'.mp hv.2).1] at hpos
    exact hpos.false
  refine ⟨A ⊔ Q.radical, ?_, fun v hv ↦ ?_⟩
  · have hsup := Submodule.finrank_sup_add_finrank_inf_eq A Q.radical
    rw [hdisj, finrank_bot, add_zero] at hsup
    have hsig := sigPos_add_sigNeg_add_radical (Q := Q)
    omega
  · obtain ⟨a, ha, r, hr, rfl⟩ := Submodule.mem_sup.mp hv
    rw [add_comm, (QuadraticMap.mem_radical_iff'.mp hr).2]
    by_cases ha0 : a = 0
    · simp [ha0]
    · simpa using (hA ⟨a, ha⟩ (by simpa using ha0)).le

end Field

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
