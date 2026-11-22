/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Pow
import SymplecticGeometry.Topology.Algebra.Module.Alternating.Wedge.TwoForm

/-!
# The first wedge power of a smooth two-form

The first wedge power of a smooth real two-form `σ` is `σ` itself
(`TauCeti.SmoothForm.wedgePow_one`). It holds pointwise, by
`ContinuousAlternatingMap.wedgePow_one` and Tau Ceti's `TauCeti.SmoothForm.wedgePow_apply`.

## Main results

* `TauCeti.SmoothForm.wedgePow_one`: `wedgePow σ 1 = σ` for a smooth two-form `σ`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 14.
-/

public section

namespace TauCeti

namespace SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H} [IsManifold I 1 M]

/-- The first wedge power of a smooth two-form is the form itself. -/
@[simp]
theorem wedgePow_one (σ : SmoothForm I M ℝ 2) : σ.wedgePow 1 = σ :=
  Subtype.ext (funext fun x ↦ by rw [wedgePow_apply, ContinuousAlternatingMap.wedgePow_one])

end SmoothForm

end TauCeti

end
