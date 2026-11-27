/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Preserving
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Orientation-preserving maps between a manifold and its model space

A map of a finite-dimensional real normed space `E` whose derivative at `v` has positive
determinant preserves every orientation of `E` at `v`
(`TauCeti.Manifold.Orientation.isOrientationPreservingAt_of_det_fderiv_pos`). This is the
counterpart of Tau Ceti's `TauCeti.Manifold.Orientation.isOrientationReversingAt_of_det_fderiv_neg`,
and its proof is that of Tau Ceti's lemma with the sign changed.

The inverse of a chart of the maximal `C¹` atlas of a manifold modelled on `E` preserves
orientation at a point of its target when the chart preserves it at the corresponding point of its
source (`TauCeti.Manifold.Orientation.IsOrientationPreservingAt.symm_of_mem_maximalAtlas`). It
reads the chart as a partial diffeomorphism and applies Tau Ceti's
`TauCeti.Manifold.Orientation.IsOrientationPreservingAt.partialDiffeomorph_symm`.

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

/-- **The inverse of an oriented smooth chart preserves orientation.** If a chart `e` of the
maximal `C¹` atlas of a manifold `M` modelled on `E` preserves orientations at `e.symm y`, from
`o` to an orientation `o'` of `E`, then its inverse preserves them at `y`, from `o'` to `o`. -/
theorem IsOrientationPreservingAt.symm_of_mem_maximalAtlas {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] {o : Manifold.Orientation 𝓘(ℝ, E) M ι}
    {o' : Manifold.Orientation 𝓘(ℝ, E) E ι} {e : OpenPartialHomeomorph M E} {y : E}
    (h : IsOrientationPreservingAt o o' e (e.symm y))
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M) (hy : y ∈ e.target) :
    IsOrientationPreservingAt o' o e.symm y := by
  -- Read `e` as a partial diffeomorphism, whose inverse is `e.symm`.
  let Φ := e.toPartialDiffeomorphOfMemMaximalAtlas he
  have hΦ : ⇑Φ = ⇑e := funext fun x ↦ by simp [Φ]
  have hΦs : ⇑Φ.symm = ⇑e.symm := funext fun v ↦ by simp [Φ]
  have h' := IsOrientationPreservingAt.partialDiffeomorph_symm (Φ := Φ) (o := o) (o' := o')
    (by simpa [Φ] using hy) (by rwa [hΦ, hΦs]) one_ne_zero
  rwa [hΦs] at h'

end TauCeti.Manifold.Orientation

end
