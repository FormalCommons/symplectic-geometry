/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Degree.Global

/-!
# The mapping degree at a fibre of one point

Supplements to Tau Ceti's `TauCeti.Geometry.Manifold.Degree.Global`. When the fibre of a proper
smooth map `f` over a point `y` consists of a single point `x` at which the derivative of `f` is
invertible, the point `y` is a regular value and the mapping degree `TauCeti.degree` of `f` is
the orientation sign of `f` at `x`.

## Main results

* `TauCeti.degree_eq_orientationSign_of_preimage_eq_singleton`: if the fibre of a proper smooth map
  over a point `y` is a single point `x` where the derivative is invertible, the degree is the
  orientation sign at `x`.

## References

* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5.
-/

public section

open Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E H H' M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M]
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J ∞ N] [BoundarylessManifold J N] [T2Space N] [SigmaCompactSpace N]
  [ConnectedSpace N] {k : ℕ}

/-- If the fibre of a proper smooth map `f` over `y` is a single point `x` at which the derivative
of `f` is invertible, then `y` is a regular value, and the degree of `f` is the orientation sign
of `f` at `x`. -/
theorem degree_eq_orientationSign_of_preimage_eq_singleton (o : Manifold.Orientation I M (Fin k))
    (o' : Manifold.Orientation J N (Fin k)) {f : M → N} (hf : ContMDiff I J ∞ f)
    (hfp : IsProperMap f) {x : M} {y : N} (hxy : f ⁻¹' {y} = {x})
    (hx : (mfderiv I J f x).IsInvertible) :
    degree o o' f = Manifold.Orientation.orientationSign o o' f x := by
  have hy : IsRegularValue I J f y := isRegularValue_iff.2 fun x' hx' ↦ by
    obtain rfl : x' = x := by
      rw [← mem_singleton_iff, ← hxy]
      exact hx'
    exact (isRegularPoint_iff_isInvertible_mfderiv rfl).2 hx
  rw [degree_eq_degreeAtRegularValue o o' hf hfp hy,
    degreeAtRegularValue_eq_sum (s := {x}) fun x' ↦ by
      rw [Finset.mem_singleton, ← mem_singleton_iff, ← hxy, mem_preimage, mem_singleton_iff],
    Finset.sum_singleton]

end TauCeti

end
