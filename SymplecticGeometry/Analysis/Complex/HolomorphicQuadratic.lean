/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Complex.QuadraticLeviForm

/-!
# Nondegeneracy of the real part of a holomorphic quadratic form

For a continuous complex bilinear form `q` on a finite-dimensional complex normed space `V`,
this file shows that the origin is a nondegenerate critical point of `z ↦ Re (q z z)` as soon as
the polarization `q.flip + q` is injective. It complements Tau Ceti's
`ContinuousLinearMap.morseIndex_re_apply_self_of_ker_eq_bot`, which computes the Morse index of
that critical point, and its proof uses Tau Ceti's
`ContinuousLinearMap.radical_hessianQuadraticForm_re_apply_self`.

## Main results

* `ContinuousLinearMap.isNondegenerateCriticalPoint_re_apply_self_of_ker_eq_bot`: if
  `q.flip + q` is injective, then `0` is a nondegenerate critical point of `z ↦ Re (q z z)`.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963.
-/

public section

open TauCeti

namespace ContinuousLinearMap

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-- If the polarization `q.flip + q` of a continuous complex bilinear form `q` on a
finite-dimensional complex space is injective, then the origin is a nondegenerate critical point
of the real part `z ↦ Re (q z z)` of the holomorphic quadratic form. -/
theorem isNondegenerateCriticalPoint_re_apply_self_of_ker_eq_bot (q : V →L[ℂ] V →L[ℂ] ℂ)
    (hq : LinearMap.ker (q.flip + q).toLinearMap = ⊥) :
    IsNondegenerateCriticalPoint (fun z ↦ (q z z).re) 0 := by
  have : FiniteDimensional ℝ V := FiniteDimensional.complexToReal V
  refine isNondegenerateCriticalPoint_iff_hessianQuadraticForm_nondegenerate.2
    ⟨(Complex.reCLM.contDiff.comp (q.contDiff_apply_self.restrict_scalars ℝ)).contDiffAt, ?_, ?_⟩
  · have h := Complex.reCLM.hasFDerivAt.comp (0 : V)
      ((q.hasFDerivAt_apply_self 0).restrictScalars ℝ)
    simpa [Function.comp_def] using h.fderiv
  · rw [QuadraticMap.nondegenerate_iff_radical_eq_bot,
      q.radical_hessianQuadraticForm_re_apply_self, hq, Submodule.restrictScalars_bot]

end ContinuousLinearMap

end
