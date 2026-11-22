/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Preserving
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Maps of a real normed space with positive Jacobian determinant

A map of a finite-dimensional real normed space `E` whose derivative at `v` has positive
determinant preserves every orientation of `E` at `v`
(`TauCeti.Manifold.Orientation.isOrientationPreservingAt_of_det_fderiv_pos`). This is the
counterpart of Tau Ceti's `TauCeti.Manifold.Orientation.isOrientationReversingAt_of_det_fderiv_neg`,
and its proof is that of Tau Ceti's lemma with the sign changed.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 15.
-/

public section

open scoped Manifold

namespace TauCeti.Manifold.Orientation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]

/-- **A positive Jacobian determinant preserves orientation.** A map of a finite-dimensional real
normed space whose derivative at `v` has positive determinant preserves every orientation there. -/
theorem isOrientationPreservingAt_of_det_fderiv_pos (o : Manifold.Orientation 𝓘(ℝ, E) E ι)
    {f : E → E} {v : E} (hdet : 0 < (fderiv ℝ f v).det) : IsOrientationPreservingAt o o f v := by
  let D : E ≃L[ℝ] E := (fderiv ℝ f v).toContinuousLinearEquivOfDetNeZero hdet.ne'
  refine (isOrientationPreservingAt_iff_of_coe_eq o o _ v D ?_).mpr ?_
  · rw [mfderiv_eq_fderiv]
    exact (fderiv ℝ f v).coe_toContinuousLinearEquivOfDetNeZero hdet.ne'
  · rw [orientationAt_eq_orientationAt o (f v) v]
    exact (_root_.Orientation.map_eq_iff_det_pos _ _ o.card_eq).mpr hdet

end TauCeti.Manifold.Orientation

end
