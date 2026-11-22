/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cohomology.CompactSupport.Euclidean.Basic
public import SymplecticGeometry.Geometry.Manifold.ChartedSpace
public import TauCeti.Topology.OpenPartialHomeomorph.Constructions

/-!
# Vanishing of cohomology with compact supports of a manifold above the dimension

Let `M` be a Hausdorff space with charts in a finite-dimensional real normed space `F`, that is,
a topological manifold without boundary of dimension `finrank ℝ F`. Then `Hᵐ_c(M; R, N) = 0` for
`m > finrank ℝ F`, for projective coefficients `R`
(`TopCat.isZero_compactSupportCohomology_of_chartedSpace`). No compactness or countability is
needed.

The proof follows that of `TopCat.isZero_compactSupportCohomology_of_isOpenEmbedding`, with the
open sets of `M` lying in one chart in place of those with convex image. Such open sets are
closed under intersection (`TopologicalSpace.Opens.infClosed_setOf_subset_chartAt_source`), and
each embeds openly into `F` through its chart (`OpenPartialHomeomorph.isOpenEmbedding_comp`), so
that the vanishing holds for them by `TopCat.isZero_compactSupportCohomology_of_isOpenEmbedding`.
They cover `M` (`TopologicalSpace.Opens.sSup_setOf_subset_chartAt_source_eq_top`), so the
vanishing holds on `M` by `TopCat.isZero_compactSupportCohomology_of_infClosed`.

## Main results

* `TopCat.isZero_compactSupportCohomology_of_chartedSpace`: `Hᵐ_c(M) = 0` above the dimension.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3, the proof of
  Theorem 3.35.
-/

public section

noncomputable section

open CategoryTheory Limits Module TopologicalSpace Topology

universe v

namespace TopCat

variable {k : Type v} [CommRing k] (R N : ModuleCat.{v} k) [Module.Projective k R]
  {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type v} [TopologicalSpace M] [T2Space M] [ChartedSpace F M]

/-- **Cohomology with compact supports of a manifold vanishes above the dimension.** For a
Hausdorff space `M` with charts in a finite-dimensional real normed space `F`,
`Hᵐ_c(M; R, N) = 0` for `m > finrank ℝ F`, for projective coefficients `R`. -/
theorem isZero_compactSupportCohomology_of_chartedSpace {m : ℕ} (hm : finrank ℝ F < m) :
    IsZero ((of M).compactSupportCohomology R k N m) := by
  refine isZero_compactSupportCohomology_of_infClosed R k N
    (Opens.infClosed_setOf_subset_chartAt_source F)
    (Opens.sSup_setOf_subset_chartAt_source_eq_top F) ?_ hm
  rintro W ⟨x, hx⟩ m hm
  exact isZero_compactSupportCohomology_of_isOpenEmbedding R N
    ((chartAt F x).isOpenEmbedding_comp W.isOpenEmbedding' (by rwa [Subtype.range_coe])) hm

end TopCat

end
