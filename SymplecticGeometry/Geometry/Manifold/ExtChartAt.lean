/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.ExtChartAt

/-!
# Extended charts of an open subset, read in the ambient manifold

An open subset `U` of a manifold `M` inherits its charts from `M`. Near the coordinates of a point
`x : U`, the inverse of the extended chart of `M` at `x` is the inverse of the extended chart of
`U` at `x` followed by `Subtype.val` (`TauCeti.extChartAt_subtype_val_symm_eventuallyEq`). This is
the counterpart, for the inclusion of `U` into `M` itself, of Tau Ceti's
`TauCeti.extChartAt_inclusion_symm_eventuallyEq` for two nested open subsets, and its proof
follows that one, with Mathlib's `TopologicalSpace.Opens.chartAt_subtypeVal_symm_eventuallyEq`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 1.
-/

public section

open Filter TopologicalSpace
open scoped Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- Near the coordinates of a point `x` of an open subset `U`, the inverse of the extended chart of
`M` at `x` is the inverse of the extended chart of `U` at `x` followed by the inclusion of `U`. -/
theorem extChartAt_subtype_val_symm_eventuallyEq (U : Opens M) (x : U) :
    (extChartAt I (x : M)).symm =ᶠ[𝓝 (extChartAt I x x)]
      Subtype.val ∘ (extChartAt I x).symm := by
  have hc : Tendsto I.symm (𝓝 (extChartAt I x x)) (𝓝 (chartAt H (x : M) x)) := by
    simpa [extChartAt, Opens.chartAt_eq] using I.continuous_symm.tendsto (extChartAt I x x)
  exact (Opens.chartAt_subtypeVal_symm_eventuallyEq U).comp_tendsto hc

end TauCeti

end
