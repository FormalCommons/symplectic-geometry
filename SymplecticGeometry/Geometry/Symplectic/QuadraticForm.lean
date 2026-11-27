/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.QuadraticForm

/-!
# Lower bounds for the negative index from complex negativity

Let `Q` be a real quadratic form and `J` an almost complex structure. If `Q(v) + Q(Jv) < 0` for
every nonzero `v`, then the negative index of inertia of `Q` is at least the complex dimension
defined by `J`. This is the lower-bound counterpart of Tau Ceti's
`QuadraticForm.sigNeg_le_complexFinrank_of_add_comp_posDef`.

The hypothesis does not make `Q` nondegenerate, so the proof does not go through the negative
index of `-Q` alone. Instead it uses a subspace on which `Q` is nonnegative and whose dimension is
complementary to `sigNeg Q`: the sum of a maximal positive-definite subspace and the radical
(`QuadraticForm.exists_finrank_add_sigNeg_eq_and_nonneg`). Tau Ceti's
`QuadraticForm.two_mul_finrank_le_of_add_comp_posDef`, applied to `-Q`, bounds the dimension of
that subspace by half the real dimension.

## Main declarations

* `QuadraticForm.exists_finrank_add_sigNeg_eq_and_nonneg`: in finite dimension there is a subspace
  on which `Q` is nonnegative, of dimension `finrank K M - sigNeg Q`.
* `QuadraticForm.complexFinrank_le_sigNeg_of_add_comp_neg`: the negative index of inertia of `Q` is
  at least the complex dimension when `Q(v) + Q(Jv) < 0` away from zero.

## References

* [D. Auroux, *Asymptotically holomorphic families of symplectic submanifolds*][Auroux1997]
* J. Milnor, *Morse Theory*, Princeton University Press, 1963, Section 7.
-/

public section

open Module

namespace QuadraticForm

section Field

variable {K M : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable [AddCommGroup M] [Module K M] [FiniteDimensional K M]

/-- A quadratic form on a finite-dimensional space is nonnegative on some subspace whose dimension
is that of the space minus the negative index of inertia. One such subspace is the sum of a
maximal positive-definite subspace and the radical. -/
theorem exists_finrank_add_sigNeg_eq_and_nonneg (Q : QuadraticForm K M) :
    ∃ W : Submodule K M, finrank K W + sigNeg Q = finrank K M ∧ ∀ v ∈ W, 0 ≤ Q v := by
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

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- If `Q(v) + Q(Jv)` is negative for every nonzero `v`, then the negative index of inertia of `Q`
is at least the complex dimension defined by `J`. -/
theorem complexFinrank_le_sigNeg_of_add_comp_neg (Q : QuadraticForm ℝ E)
    (J : TauCeti.AlmostComplexStructure E) (hQJ : ∀ v, v ≠ 0 → Q v + Q (J v) < 0) :
    J.complexFinrank ≤ sigNeg Q := by
  have hE := J.finrank_real_eq_two_mul_complexFinrank
  by_cases hfin : FiniteDimensional ℝ E
  swap
  · rw [finrank_of_not_finite hfin] at hE
    omega
  obtain ⟨W, hWdim, hW⟩ := exists_finrank_add_sigNeg_eq_and_nonneg Q
  have hnegJ : (-Q + (-Q).comp J.toLinearMap).PosDef := fun v hv ↦ by
    simpa [neg_add, add_comm] using neg_pos.mpr (hQJ v hv)
  have h := (-Q).two_mul_finrank_le_of_add_comp_posDef J.toLinearMap hnegJ fun v hv ↦ by
    simpa using hW v hv
  omega

end QuadraticForm
