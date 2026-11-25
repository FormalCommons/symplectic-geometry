/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import SymplecticGeometry.Topology.CoveringDimension.Euclidean
public import SymplecticGeometry.Topology.CoveringDimension.Union

/-!
# The covering dimension of compact subsets of manifolds

For a space `M` charted on `H`, with a model with corners `I : ModelWithCorners ℝ E H` and `E`
finite-dimensional, every compact subset `K` of a Hausdorff `M` satisfies
`CoveringDimLE K (finrank ℝ E)`.

Finitely many chart sources cover `K`, and Mathlib's `IsCompact.finite_compact_cover` writes
`K` as a finite union of compact pieces, each inside one of these sources. The chart, followed
by `I`, embeds its source into `E`, so each piece satisfies the bound of
`IsCompact.coveringDimLE_finrank`, and `CoveringDimLE.biUnion` combines the pieces, which are
closed since `M` is Hausdorff.

## Main declarations

* `IsCompact.coveringDimLE_finrank_of_subset_chartAt_source`: a compact subset of one chart
  source.
* `IsCompact.coveringDimLE_finrank_of_chartedSpace`: any compact subset.

## References

* J. R. Munkres, *Topology*, 2nd ed., Prentice Hall, 2000, §50
-/

public section

open Set Module SymplecticGeometry

namespace IsCompact

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]

/-- A compact subset `K` of the source of a chart of `M` satisfies
`CoveringDimLE K (finrank ℝ E)`, for a model with corners `I` on `H` and `E`
finite-dimensional. -/
theorem coveringDimLE_finrank_of_subset_chartAt_source (I : ModelWithCorners ℝ E H) {x : M}
    {K : Set M} (hK : IsCompact K) (hKs : K ⊆ (chartAt H x).source) :
    CoveringDimLE K (finrank ℝ E) := by
  set e := chartAt H x
  let f : e.source → E := I ∘ e.source.domRestrict e
  have hf : Topology.IsInducing f :=
    I.isClosedEmbedding.isInducing.comp e.isOpenEmbedding_restrict.isInducing
  have hK' : IsCompact ((↑) ⁻¹' K : Set e.source) := by
    rwa [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.2 hKs]
  have h := (Topology.IsInducing.subtypeVal.coveringDimLE_image_iff (n := finrank ℝ E)).2
    (CoveringDimLE.of_isInducing hf ((hK'.image hf.continuous).coveringDimLE_finrank))
  rwa [Subtype.image_preimage_coe, inter_eq_right.2 hKs] at h

/-- Every compact subset `K` of a Hausdorff space `M` charted on `H`, with a model with corners
`I : ModelWithCorners ℝ E H` and `E` finite-dimensional, satisfies
`CoveringDimLE K (finrank ℝ E)`. -/
theorem coveringDimLE_finrank_of_chartedSpace (I : ModelWithCorners ℝ E H) [T2Space M]
    {K : Set M} (hK : IsCompact K) : CoveringDimLE K (finrank ℝ E) := by
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : M => (chartAt H x).source)
    (fun x => (chartAt H x).open_source)
    (fun y _ => mem_iUnion.2 ⟨y, mem_chart_source H y⟩)
  obtain ⟨L, hLc, hLs, rfl⟩ := hK.finite_compact_cover t (fun x : M => (chartAt H x).source)
    (fun x _ => (chartAt H x).open_source) ht
  exact CoveringDimLE.biUnion (fun x _ => (hLc x).isClosed)
    fun x _ => (hLc x).coveringDimLE_finrank_of_subset_chartAt_source I (hLs x)

end IsCompact

end
