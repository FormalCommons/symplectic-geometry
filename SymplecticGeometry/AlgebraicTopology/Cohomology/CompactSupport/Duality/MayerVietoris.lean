/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cohomology.CompactSupport.Duality.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.MayerVietoris

/-!
# The duality maps and the first two Mayer–Vietoris maps

Fix a boundaryless `n`-manifold `M` with a homological orientation `o`, `L` an abelian
group, and give every open set of `M` the restricted orientation
(`TauCeti.HomologicalOrientation.comap`). For opens `U` and `V` of `M`, the duality maps
`D : Hᵖ_c(-; L) ⟶ H_q(-; L)`, `p + q = n`, of `U ∩ V`, `U`, `V` and `M` connect the Mayer–Vietoris
sequence of cohomology with compact supports to that of singular homology:

```
Hᵖ_c(U ∩ V) ⟶ Hᵖ_c(U) ⊞ Hᵖ_c(V) ⟶ Hᵖ_c(M)
     ↓                ↓                ↓
H_q(U ∩ V)  ⟶  H_q(U) ⊞ H_q(V)  ⟶  H_q(M)
```

This file proves that both squares commute. In both rows the first map is the pair of the map
induced by the inclusion into `U` and minus the map induced by the inclusion into `V`, and the
second map is the sum of the maps induced by the inclusions; so each square is, component by
component, the naturality of the duality map along the inclusion of an open set
(`TauCeti.HomologicalOrientation.compactSupportCohomologyExtend_inclusion'_dualityMap` and
`TauCeti.HomologicalOrientation.compactSupportCohomologyExtend_toTopCat_map_dualityMap`). Neither
square needs `U ∪ V = M`; that hypothesis is needed only for the exactness of the rows.

## Main results

* `TauCeti.HomologicalOrientation.compactSupportCohomologyMayerVietorisToBiprod_dualityMap`: the
  square at `Hᵖ_c(U ∩ V) ⟶ Hᵖ_c(U) ⊞ Hᵖ_c(V)`.
* `TauCeti.HomologicalOrientation.compactSupportCohomologyMayerVietorisFromBiprod_dualityMap`:
  the square at `Hᵖ_c(U) ⊞ Hᵖ_c(V) ⟶ Hᵖ_c(M)`.

## Provenance

The statements and proofs are those of Tau Ceti's main branch, in
`TauCeti/AlgebraicTopology/Cohomology/CompactSupport/Duality/MayerVietoris.lean`, under the same
names, as of the commit `a2b27244398126b7be07d28c3ce0d849e4ca2458`
(TauCetiProject/TauCeti#42569); no tagged release has them yet. They are stated here under their
Tau Ceti names and namespace, so that moving Tau Ceti past them deletes this file without renames.

## Implementation notes

The open sets are elements of `Opens (TopCat.of M)`, as in
`TopCat.compactSupportCohomologyMayerVietorisToBiprod`, with the charts of
`TopologicalSpace.Opens.instChartedSpaceToTopCatObj`. The homology row uses the maps
`SSet.mayerVietorisToBiprod` and `SSet.mayerVietorisFromBiprod` of the Mayer–Vietoris sequence of
simplicial sets, which are those of singular homology (`TopCat.mayerVietoris_exact₂`).

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, the diagram of Mayer–Vietoris sequences in the proof of Lemma 3.36.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace Topology Opens

namespace TauCeti

attribute [local instance] MonoidalPreadditive.monoidalLinearInt

namespace HomologicalOrientation

variable {M E : Type} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {n : ℕ} (o : HomologicalOrientation M E n) (hn : Module.finrank ℝ E = n) (L : ModuleCat.{0} ℤ)

variable {p q : ℕ} (h : p + q = n)

variable (U V : Opens (TopCat.of M))

/-- **The duality maps commute with the first Mayer–Vietoris maps**: for any opens `U` and `V` of
`M`, not necessarily covering `M`, the map `Hᵖ_c(U ∩ V) ⟶ Hᵖ_c(U) ⊞ Hᵖ_c(V)` of the Mayer–Vietoris
sequence of cohomology with compact supports, followed by the duality maps of `U` and `V`, is the
duality map of `U ∩ V` followed by the map `H_q(U ∩ V) ⟶ H_q(U) ⊞ H_q(V)` of the Mayer–Vietoris
sequence of singular homology. Both maps have components the map induced by the inclusion into `U`
and minus the map induced by the inclusion into `V`. -/
@[reassoc]
theorem compactSupportCohomologyMayerVietorisToBiprod_dualityMap :
    TopCat.compactSupportCohomologyMayerVietorisToBiprod (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L U V p ≫
        biprod.map ((o.comap U.isOpenEmbedding).dualityMap hn L p q h)
          ((o.comap V.isOpenEmbedding).dualityMap hn L p q h) =
      (o.comap (U ⊓ V).isOpenEmbedding).dualityMap hn L p q h ≫
        SSet.mayerVietorisToBiprod L
          (TopCat.toSSet.map ((Opens.toTopCat (TopCat.of M)).map (homOfLE inf_le_left)))
          (TopCat.toSSet.map ((Opens.toTopCat (TopCat.of M)).map (homOfLE inf_le_right))) q := by
  apply biprod.hom_ext
  · rw [Category.assoc, biprod.map_fst,
      TopCat.compactSupportCohomologyMayerVietorisToBiprod_fst_assoc,
      compactSupportCohomologyExtend_toTopCat_map_dualityMap, singularHomologyFunctor_obj_map]
    -- The duality map lands in `((singularHomologyFunctor _ q).obj L).obj X`, which is
    -- `(TopCat.toSSet.obj X).homology L q` only after unfolding `singularHomologyFunctor`, so the
    -- composite on the right is type-correct only up to that unfolding: `rw` cannot reassociate
    -- it, and `erw` is needed for these two steps.
    erw [Category.assoc, SSet.mayerVietorisToBiprod_fst]
  · rw [Category.assoc, biprod.map_snd,
      TopCat.compactSupportCohomologyMayerVietorisToBiprod_snd_assoc, Preadditive.neg_comp,
      compactSupportCohomologyExtend_toTopCat_map_dualityMap, singularHomologyFunctor_obj_map]
    -- As in the first component, only up to unfolding `singularHomologyFunctor`.
    erw [Category.assoc, SSet.mayerVietorisToBiprod_snd, Preadditive.comp_neg]

/-- **The duality maps commute with the second Mayer–Vietoris maps**: for any opens `U` and `V` of
`M`, not necessarily covering `M`, the map `Hᵖ_c(U) ⊞ Hᵖ_c(V) ⟶ Hᵖ_c(M)` of the Mayer–Vietoris
sequence of cohomology with compact supports, followed by the duality map of `M`, is the duality
maps of `U` and `V` followed by the map `H_q(U) ⊞ H_q(V) ⟶ H_q(M)` of the Mayer–Vietoris sequence of
singular homology. Both maps are the sums of the maps induced by the inclusions. -/
@[reassoc]
theorem compactSupportCohomologyMayerVietorisFromBiprod_dualityMap :
    TopCat.compactSupportCohomologyMayerVietorisFromBiprod (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L U V
        p ≫ o.dualityMap hn L p q h =
      biprod.map ((o.comap U.isOpenEmbedding).dualityMap hn L p q h)
          ((o.comap V.isOpenEmbedding).dualityMap hn L p q h) ≫
        SSet.mayerVietorisFromBiprod L (TopCat.toSSet.map (Opens.inclusion' U))
          (TopCat.toSSet.map (Opens.inclusion' V)) q := by
  apply biprod.hom_ext'
  · rw [TopCat.inl_compactSupportCohomologyMayerVietorisFromBiprod_assoc,
      compactSupportCohomologyExtend_inclusion'_dualityMap, singularHomologyFunctor_obj_map]
    -- As in `compactSupportCohomologyMayerVietorisToBiprod_dualityMap`, the composite on the right
    -- is type-correct only up to unfolding `singularHomologyFunctor`.
    erw [biprod.inl_map_assoc, SSet.inl_mayerVietorisFromBiprod]
  · rw [TopCat.inr_compactSupportCohomologyMayerVietorisFromBiprod_assoc,
      compactSupportCohomologyExtend_inclusion'_dualityMap, singularHomologyFunctor_obj_map]
    erw [biprod.inr_map_assoc, SSet.inr_mayerVietorisFromBiprod]

end HomologicalOrientation

end TauCeti
