/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cohomology.CompactSupport.Euclidean.Duality

/-!
# Poincaré duality for manifolds

Let `M` be a Hausdorff space with charts in a finite-dimensional real normed space `E` of
dimension `n`, that is, a topological `n`-manifold without boundary, and `L` an abelian group.

* For a homological orientation of `M` and `p + q = n`, the duality map
  `D_M : Hᵖ_c(M; L) ⟶ H_q(M; L)` is a bijection
  (`TauCeti.HomologicalOrientation.bijective_dualityMap`).
* For compact `M`, capping with the fundamental class `[M]` is therefore a bijection
  `Hᵖ(M; L) ⟶ H_q(M; L)`
  (`TauCeti.HomologicalOrientation.bijective_singularCap_fundamentalClass`),
  by `TauCeti.HomologicalOrientation.dualityMap_compactSupportCohomologyIsoOfCompactSpace_inv`.

No compactness or countability is needed for the first, as in Hatcher's Theorem 3.35. The proof
follows that of `TauCeti.HomologicalOrientation.bijective_dualityMap_of_isOpenEmbedding`, with the
open sets of `M` lying in one chart in place of those with convex image, as the proof of
`TopCat.isZero_compactSupportCohomology_of_chartedSpace` in `CompactSupport/Manifold.lean` does.
Such open sets are closed under intersection
(`TopologicalSpace.Opens.infClosed_setOf_subset_chartAt_source`), and each embeds openly into `E`
through its chart (`OpenPartialHomeomorph.isOpenEmbedding_comp`), so that duality holds for them
by `TauCeti.HomologicalOrientation.bijective_dualityMap_of_isOpenEmbedding`. They cover `M`
(`TopologicalSpace.Opens.sSup_setOf_subset_chartAt_source_eq_top`), so duality holds on `M` by
the Mayer–Vietoris induction `TauCeti.HomologicalOrientation.bijective_dualityMap_of_infClosed`.

## Main results

* `TauCeti.HomologicalOrientation.bijective_dualityMap`: Poincaré duality for an oriented
  manifold.
* `TauCeti.HomologicalOrientation.bijective_singularCap_fundamentalClass`: Poincaré duality for a
  compact oriented manifold, as capping with the fundamental class.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3, Theorem 3.30
  and the proof of Theorem 3.35.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Module TopologicalSpace Topology

namespace TauCeti

attribute [local instance] MonoidalPreadditive.monoidalLinearInt

namespace HomologicalOrientation

variable {M E : Type} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {n : ℕ} (o : HomologicalOrientation M E n) (hn : finrank ℝ E = n) (L : ModuleCat.{0} ℤ)

/-- **Poincaré duality.** For a homologically oriented `n`-manifold `M` without boundary, the
duality map `Hᵖ_c(M; L) ⟶ H_q(M; L)` is a bijection whenever `p + q = n`, for every abelian
group `L`. -/
theorem bijective_dualityMap {p q : ℕ} (h : p + q = n) :
    Function.Bijective (o.dualityMap hn L p q h) := by
  refine o.bijective_dualityMap_of_infClosed hn L (Opens.infClosed_setOf_subset_chartAt_source E)
    (Opens.sSup_setOf_subset_chartAt_source_eq_top E) ?_ h
  rintro W ⟨x, hx⟩ p q h
  exact (o.comap W.isOpenEmbedding').bijective_dualityMap_of_isOpenEmbedding hn L
    ((chartAt E x).isOpenEmbedding_comp W.isOpenEmbedding' (by rwa [Subtype.range_coe])) h

/-- **Poincaré duality for a compact manifold.** For a compact homologically oriented
`n`-manifold `M` without boundary, capping with the fundamental class,
`α ↦ [M] ⌢ α : Hᵖ(M; L) ⟶ H_q(M; L)`, is a bijection whenever `p + q = n`, for every abelian
group `L`. -/
theorem bijective_singularCap_fundamentalClass [CompactSpace M] {p q : ℕ} (h : p + q = n) :
    Function.Bijective fun α : (TopCat.of M).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
        L p ↦ ((TopCat.of M).singularCap ℤ (ρ_ _).inv (ρ_ L).hom p q n h α).hom
          (o.fundamentalClass hn) := by
  convert (o.bijective_dualityMap hn L h).comp (ConcreteCategory.bijective_of_isIso
    (TopCat.compactSupportCohomologyIsoOfCompactSpace p).inv) using 1
  funext α
  exact (o.dualityMap_compactSupportCohomologyIsoOfCompactSpace_inv hn L p q h α).symm

end HomologicalOrientation

end TauCeti
