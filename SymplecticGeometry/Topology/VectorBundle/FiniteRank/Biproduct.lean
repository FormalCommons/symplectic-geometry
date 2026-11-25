/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Determinant
public import TauCeti.Topology.VectorBundle.FiniteRank.Biproduct
import TauCeti.Topology.Algebra.Module.Determinant

/-!
# Whitney sums of finite-rank cores in charts

Tau Ceti's `TauCeti.FiniteRankBundleCore.whitneySum A D` has the concatenated coordinates
`Fin (A.rank + D.rank) → 𝕜`, split into the two blocks by `TauCeti.splitCoords`. This file
computes chart expressions in charts of Whitney sums, and the determinants of the transitions of
a Whitney sum.

## Main results

* `TauCeti.FiniteRankBundleCore.inChartCoordinates_whitneySum_prodMap`: in charts of Whitney
  sums, the chart expression of a block-diagonal map is the block-diagonal map of the chart
  expressions of its blocks;
* `TauCeti.FiniteRankBundleCore.det_coordChange_whitneySum`: the transitions of a Whitney sum
  are block diagonal, so their determinants are the products of the determinants of the
  transitions of the summands.

The proof of `inChartCoordinates_whitneySum_prodMap` follows Tau Ceti's
`TauCeti.FiniteRankBundleCore.inChartCoordinates_tensor_kronecker`, which computes the chart
expression of a Kronecker product in charts of tensor products.
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

/-- The transition maps of a Whitney sum are block diagonal, so their determinants are the
products of the determinants of the transition maps of the two summands. -/
theorem det_coordChange_whitneySum (A D : FiniteRankBundleCore 𝕜 B) (i j x : B) :
    ((whitneySum A D).core.coordChange i j x).det =
      (A.core.coordChange i j x).det * (D.core.coordChange i j x).det := by
  -- The statement for an operator on `Fin (A.rank + D.rank) → 𝕜` acting blockwise, stated on
  -- this coordinate space, where the rewriting lemmas apply.
  have key (f : (Fin (A.rank + D.rank) → 𝕜) →L[𝕜] (Fin (A.rank + D.rank) → 𝕜))
      (hf : ∀ u w, f ((splitCoords (𝕜 := 𝕜) A.rank D.rank).symm (u, w)) =
        (splitCoords (𝕜 := 𝕜) A.rank D.rank).symm
          (A.core.coordChange i j x u, D.core.coordChange i j x w)) :
      f.det = (A.core.coordChange i j x).det * (D.core.coordChange i j x).det := by
    set e := splitCoords (𝕜 := 𝕜) (M := 𝕜) A.rank D.rank
    have h : (e : _ →L[𝕜] _) ∘L f ∘L (e.symm : _ →L[𝕜] _) =
        (A.core.coordChange i j x).prodMap (D.core.coordChange i j x) :=
      ContinuousLinearMap.ext fun ⟨u, w⟩ ↦ (congrArg e (hf u w)).trans (by simp [e])
    rw [← ContinuousLinearMap.det_conj f e, h, ContinuousLinearMap.det_prodMap]
  exact key _ (coordChange_whitneySum_splitCoords_symm A D i j x)

end TauCeti.FiniteRankBundleCore

end
