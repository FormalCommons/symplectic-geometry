/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Biproduct

/-!
# Whitney sums of finite-rank cores in charts

Tau Ceti's `TauCeti.FiniteRankBundleCore.whitneySum A D` has the concatenated coordinates
`Fin (A.rank + D.rank) → 𝕜`, split into the two blocks by `TauCeti.splitCoords`. This file
computes chart expressions in charts of Whitney sums.

## Main results

* `TauCeti.FiniteRankBundleCore.inChartCoordinates_whitneySum_prodMap`: in charts of Whitney
  sums, the chart expression of a block-diagonal map is the block-diagonal map of the chart
  expressions of its blocks.

The proof follows Tau Ceti's `TauCeti.FiniteRankBundleCore.inChartCoordinates_tensor_kronecker`,
which computes the chart expression of a Kronecker product in charts of tensor products.
-/

public section

noncomputable section

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]

/-- Read in charts of Whitney sums, a block-diagonal map is block diagonal, with the chart
expressions of its blocks as blocks. -/
theorem inChartCoordinates_whitneySum_prodMap
    (A A' D D' : FiniteRankBundleCore 𝕜 B)
    (f : (Fin A.rank → 𝕜) →L[𝕜] (Fin A'.rank → 𝕜))
    (g : (Fin D.rank → 𝕜) →L[𝕜] (Fin D'.rank → 𝕜)) (i j x : B) :
    (whitneySum A D).core.inChartCoordinates (whitneySum A' D').core i j x
        ((splitCoords (𝕜 := 𝕜) A'.rank D'.rank).symm.toContinuousLinearMap.comp
          ((f.prodMap g).comp (splitCoords (𝕜 := 𝕜) A.rank D.rank).toContinuousLinearMap)) =
      (splitCoords (𝕜 := 𝕜) A'.rank D'.rank).symm.toContinuousLinearMap.comp
        (((A.core.inChartCoordinates A'.core i j x f).prodMap
            (D.core.inChartCoordinates D'.core i j x g)).comp
          (splitCoords (𝕜 := 𝕜) A.rank D.rank).toContinuousLinearMap) := by
  refine (inChartCoordinates_core _ _ i j x _).trans ?_
  rw [inChartCoordinates_core, inChartCoordinates_core]
  -- Unfold the transitions of the Whitney sums, whose fibre models are the concatenated
  -- coordinates.
  dsimp +instances only [whitneySum]
  ext v : 1
  simp

end TauCeti.FiniteRankBundleCore

end
