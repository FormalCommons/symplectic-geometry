/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.MeasureTheory.Measure.MvPolynomialZeroLocus

/-!
# Averages of `log ‖P‖` over balls for complex polynomials

This file is about the averages of `log ‖eval v.ofLp P‖` over balls of `EuclideanSpace ℂ ι`, for a
multivariate polynomial `P` with complex coefficients. Its aim is the comparison between such an
average and the logarithm of the largest value of `‖P‖` on the ball, a form of the
Bernstein–Walsh inequality, which bounds the growth of a polynomial of degree `d` away from a
compact set by the `d`-th power of the Siciak extremal function.

It starts with the null-set facts that the averages need:

* `MvPolynomial.ae_eval_ne_zero`: a nonzero polynomial does not vanish at almost every point of
  `EuclideanSpace ℂ ι`;
* `MvPolynomial.exists_mem_ball_eval_ne_zero`: every ball of positive radius has a point where a
  nonzero polynomial does not vanish.

The first transfers Tau Ceti's `MvPolynomial.volume_setOfPred_eval_eq_zero` from `ι → ℂ` to
`EuclideanSpace ℂ ι` along Tau Ceti's `PiLp.volume_preserving_symm_measurableEquiv_toLp`, by which
`ofLp` preserves the volume.

## References

* [M. Klimek, *Pluripotential Theory*, Oxford University Press, 1991], §5.2 (the
  Bernstein–Walsh inequality)
-/

public section

open MeasureTheory

namespace MvPolynomial

variable {ι : Type*} [Fintype ι]

/-- A nonzero polynomial in the coordinates of `EuclideanSpace ℂ ι` is nonzero at almost every
point. -/
theorem ae_eval_ne_zero {Q : MvPolynomial ι ℂ} (hQ : Q ≠ 0) :
    ∀ᵐ v : EuclideanSpace ℂ ι, eval v.ofLp Q ≠ 0 := by
  have h := (PiLp.volume_preserving_symm_measurableEquiv_toLp
    (F := fun _ : ι => ℂ)).quasiMeasurePreserving.preimage_null
    (volume_setOfPred_eval_eq_zero Q hQ)
  exact measure_mono_null (fun v hv => by simpa using hv) h

/-- A nonzero polynomial in the coordinates of `EuclideanSpace ℂ ι` is nonzero at some point of
every ball of positive radius. -/
theorem exists_mem_ball_eval_ne_zero {Q : MvPolynomial ι ℂ} (hQ : Q ≠ 0)
    (c : EuclideanSpace ℂ ι) {r : ℝ} (hr : 0 < r) :
    ∃ v ∈ Metric.ball c r, eval v.ofLp Q ≠ 0 := by
  by_contra! h
  refine (Metric.measure_ball_pos volume c hr).ne' (measure_mono_null (fun v hv => ?_)
    (ae_iff.mp (ae_eval_ne_zero hQ)))
  simpa using h v hv

end MvPolynomial

end
