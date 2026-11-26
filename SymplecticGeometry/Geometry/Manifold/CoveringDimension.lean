/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import TauCeti.Topology.Dimension.Covering
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import SymplecticGeometry.Topology.CoveringDimension.Euclidean
import SymplecticGeometry.Topology.CoveringDimension.Union

/-!
# The covering dimension of compact subsets of manifolds

For a space `M` charted on `H`, with a model with corners `I : ModelWithCorners ℝ E H` and `E`
finite-dimensional, every compact subset `K` of a Hausdorff `M` has covering dimension at most
`finrank ℝ E` (`TauCeti.HasCoveringDimensionLE`).

Finitely many chart sources cover `K`, and Mathlib's `IsCompact.finite_compact_cover` writes
`K` as a finite union of compact pieces, each inside one of these sources. The chart, followed
by `I`, maps such a piece continuously and injectively, hence homeomorphically, onto a compact
subset of `E`, so each piece has the bound of `IsCompact.hasCoveringDimensionLE_finrank`, and
`TauCeti.hasCoveringDimensionLE_biUnion` combines the pieces, which are closed since `M` is
Hausdorff.

## Main declarations

* `IsCompact.hasCoveringDimensionLE_finrank_of_subset_source`: a compact subset of the source of
  an open partial homeomorphism from `M` to `H`.
* `IsCompact.hasCoveringDimensionLE_finrank_of_chartedSpace`: any compact subset.

## References

* J. R. Munkres, *Topology*, 2nd ed., Prentice Hall, 2000, §50
-/

public section

open Set Module TauCeti

namespace IsCompact

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] [TopologicalSpace M]

/-- A compact subset `K` of the source of an open partial homeomorphism `e` from `M` to `H` has
covering dimension at most `finrank ℝ E`, for a model with corners `I` on `H` and `E`
finite-dimensional. -/
theorem hasCoveringDimensionLE_finrank_of_subset_source (I : ModelWithCorners ℝ E H)
    (e : OpenPartialHomeomorph M H) {K : Set M} (hK : IsCompact K) (hKs : K ⊆ e.source) :
    HasCoveringDimensionLE K (finrank ℝ E) := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hc : ContinuousOn (I ∘ e) K := I.continuous.comp_continuousOn (e.continuousOn.mono hKs)
  -- `I ∘ e` maps `K` continuously and injectively onto the compact set `(I ∘ e) '' K`.
  let g : K → (I ∘ e) '' K := fun x => ⟨I (e x), mem_image_of_mem _ x.property⟩
  have hg : Continuous g := (continuousOn_iff_continuous_domRestrict.1 hc).subtype_mk _
  refine (hg.isClosedEmbedding fun x y hxy => Subtype.ext (e.injOn (hKs x.property)
    (hKs y.property) (I.injective (congrArg Subtype.val hxy)))).hasCoveringDimensionLE ?_
  exact (hK.image_of_continuousOn hc).hasCoveringDimensionLE_finrank

/-- Every compact subset `K` of a Hausdorff space `M` charted on `H`, with a model with corners
`I : ModelWithCorners ℝ E H` and `E` finite-dimensional, has covering dimension at most
`finrank ℝ E`. -/
theorem hasCoveringDimensionLE_finrank_of_chartedSpace (I : ModelWithCorners ℝ E H)
    [ChartedSpace H M] [T2Space M] {K : Set M} (hK : IsCompact K) :
    HasCoveringDimensionLE K (finrank ℝ E) := by
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : M => (chartAt H x).source)
    (fun x => (chartAt H x).open_source)
    (fun y _ => mem_iUnion.2 ⟨y, mem_chart_source H y⟩)
  obtain ⟨L, hLc, hLs, rfl⟩ := hK.finite_compact_cover t (fun x : M => (chartAt H x).source)
    (fun x _ => (chartAt H x).open_source) ht
  exact hasCoveringDimensionLE_biUnion (fun x _ => (hLc x).isClosed)
    fun x _ => (hLc x).hasCoveringDimensionLE_finrank_of_subset_source I (chartAt H x) (hLs x)

end IsCompact

end
