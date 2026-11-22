/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cohomology.CompactSupport.Euclidean.Duality
public import SymplecticGeometry.Geometry.Manifold.ChartedSpace
public import TauCeti.Topology.OpenPartialHomeomorph.Constructions

/-!
# Poincaré duality for manifolds

Let `M` be a Hausdorff space with charts in a finite-dimensional real normed space `E` of
dimension `n`, that is, a topological `n`-manifold without boundary, and `L` an abelian group.

* `Hᵐ_c(M; R, N) = 0` for `m > n`, for projective coefficients `R`
  (`TopCat.isZero_compactSupportCohomology_of_chartedSpace`).
* For a homological orientation of `M` and `p + q = n`, the duality map
  `D_M : Hᵖ_c(M; L) ⟶ H_q(M; L)` is a bijection
  (`TauCeti.HomologicalOrientation.bijective_dualityMap`).
* For compact `M`, capping with the fundamental class `[M]` is therefore a bijection
  `Hᵖ(M; L) ⟶ H_q(M; L)`
  (`TauCeti.HomologicalOrientation.bijective_singularCap_fundamentalClass`),
  by `TauCeti.HomologicalOrientation.dualityMap_compactSupportCohomologyIsoOfCompactSpace_inv`.

No compactness or countability is needed for the first two, as in Hatcher's Theorem 3.35. Both
are proved by the same induction, which follows the proof of
`TauCeti.HomologicalOrientation.bijective_dualityMap_of_isOpenEmbedding` (and of
`TopCat.isZero_compactSupportCohomology_of_isOpenEmbedding`) with the open sets of `M` lying in
one chart in place of those with convex image. Such open sets are closed under intersection
(`TopologicalSpace.Opens.infClosed_setOf_subset_chartAt_source`), and each embeds openly into `E`
through its chart (`OpenPartialHomeomorph.isOpenEmbedding_comp`), so that the
statements hold for them by
`TauCeti.HomologicalOrientation.bijective_dualityMap_of_isOpenEmbedding` and
`TopCat.isZero_compactSupportCohomology_of_isOpenEmbedding`. They pass to finite unions by
Mayer–Vietoris (`TauCeti.HomologicalOrientation.bijective_dualityMap_comap_sup`,
`TopCat.isZero_compactSupportCohomology_sup`, `InfClosed.finset_sup_induction`); for duality, the
vanishing of `Hⁿ⁺¹_c(V ∩ W)` that this step needs is the first result, applied to the manifold
`V ∩ W`. Finally, these finite unions form a directed family covering `M`
(`TopologicalSpace.Opens.iSup_finset_sup_subset_chartAt_source_eq_top`), and both statements pass
to directed unions (`TauCeti.HomologicalOrientation.bijective_dualityMap_of_iSup_eq_top`,
`TopCat.isZero_compactSupportCohomology_of_iSup_eq_top`).

## Main results

* `TopCat.isZero_compactSupportCohomology_of_chartedSpace`: `Hᵐ_c(M) = 0` above the dimension.
* `TauCeti.HomologicalOrientation.bijective_dualityMap`: Poincaré duality for an oriented
  manifold.
* `TauCeti.HomologicalOrientation.bijective_singularCap_fundamentalClass`: Poincaré duality for a
  compact oriented manifold, as capping with the fundamental class.

## Implementation notes

The duality maps are stated with the `ℤ`-linear structure of `ModuleCat ℤ` as a preadditive
category, while the vanishing theorem is proved for the structure of a category of modules; the
two agree since a `ℤ`-module structure is unique (`CategoryTheory.Linear.subsingletonInt`), as in
`TauCeti.HomologicalOrientation.bijective_dualityMap_of_isOpenEmbedding`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3, Theorem 3.30
  and the proof of Theorem 3.35.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Module TopologicalSpace Topology

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
  -- Vanishing passes to finite unions of open sets lying in one chart, by Mayer–Vietoris.
  have hT (s : Finset {W : Opens M | ∃ x, (W : Set M) ⊆ (chartAt F x).source}) :
      ∀ m, finrank ℝ F < m →
        IsZero ((of ↥(s.sup Subtype.val)).compactSupportCohomology R k N m) := by
    refine (Opens.infClosed_setOf_subset_chartAt_source F).finset_sup_induction
      (fun W : Opens M ↦ ∀ m, finrank ℝ F < m → IsZero ((of W).compactSupportCohomology R k N m))
      ?_ ?_ ?_ s
    · have : IsEmpty ↥(⊥ : Opens M) := ⟨fun x ↦ x.property⟩
      exact fun m _ ↦ isZero_compactSupportCohomology_of_isEmpty R k N _ m
    · rintro W ⟨x, hx⟩ m hm
      exact isZero_compactSupportCohomology_of_isOpenEmbedding R N
        ((chartAt F x).isOpenEmbedding_comp W.isOpenEmbedding' (by rwa [Subtype.range_coe])) hm
    · exact fun V W hV hW hVW m hm ↦ isZero_compactSupportCohomology_sup R k N (hV m hm)
        (hW m hm) (hVW (m + 1) (by omega))
  -- They form a directed family covering `M`; `(Opens.toTopCat (of M)).obj W` is `of W` by
  -- definition.
  exact isZero_compactSupportCohomology_of_iSup_eq_top R k N (X := of M)
    (U := fun s : Finset {W : Opens M | ∃ x, (W : Set M) ⊆ (chartAt F x).source} ↦
      s.sup Subtype.val)
    (fun _ _ hst ↦ Finset.sup_mono hst) (Opens.iSup_finset_sup_subset_chartAt_source_eq_top F)
    fun s ↦ hT s m hm

end TopCat

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
  -- Duality in every degree, for the orientation restricted from `M`, passes to finite unions of
  -- open sets lying in one chart, by Mayer–Vietoris.
  have hT (s : Finset {W : Opens M | ∃ x, (W : Set M) ⊆ (chartAt E x).source}) :
      ∀ p q (h : p + q = n), Function.Bijective
        ((o.comap (s.sup Subtype.val).isOpenEmbedding').dualityMap hn L p q h) := by
    refine (Opens.infClosed_setOf_subset_chartAt_source E).finset_sup_induction
      (fun W : Opens M ↦ ∀ p q (h : p + q = n), Function.Bijective
        ((o.comap W.isOpenEmbedding').dualityMap hn L p q h)) ?_ ?_ ?_ s
    · have : IsEmpty ↥(⊥ : Opens M) := ⟨fun x ↦ x.property⟩
      exact fun p q h ↦ (o.comap _).bijective_dualityMap_of_isEmpty hn L h
    · rintro W ⟨x, hx⟩ p q h
      exact (o.comap W.isOpenEmbedding').bijective_dualityMap_of_isOpenEmbedding hn L
        ((chartAt E x).isOpenEmbedding_comp W.isOpenEmbedding' (by rwa [Subtype.range_coe])) h
    · intro V W hV hW hVW p q h
      -- `TopCat.isZero_compactSupportCohomology_of_chartedSpace` uses the `ℤ`-linear structure
      -- of `ModuleCat ℤ` as a category of modules; it agrees with the one of a preadditive
      -- category used here, as a `ℤ`-module structure is unique.
      have := Linear.subsingletonInt (ModuleCat.{0} ℤ)
      refine o.bijective_dualityMap_comap_sup hn L hV hW hVW ?_ h
      convert TopCat.isZero_compactSupportCohomology_of_chartedSpace
        (ModuleCat.of ℤ (ULift ℤ : Type)) L (F := E) (M := ↥(V ⊓ W))
        (show finrank ℝ E < n + 1 by omega)
  -- They form a directed family covering `M`.
  exact o.bijective_dualityMap_of_iSup_eq_top hn L h (fun _ _ hst ↦ Finset.sup_mono hst)
    (Opens.iSup_finset_sup_subset_chartAt_source_eq_top E) fun s ↦ hT s p q h

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
