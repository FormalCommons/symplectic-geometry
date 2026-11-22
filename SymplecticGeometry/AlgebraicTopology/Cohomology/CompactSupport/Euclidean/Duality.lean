/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Euclidean.Duality
public import TauCeti.CategoryTheory.Linear.Int
public import SymplecticGeometry.AlgebraicTopology.Cohomology.CompactSupport.Duality.Union
public import SymplecticGeometry.AlgebraicTopology.Cohomology.CompactSupport.Euclidean.Basic

/-!
# Poincaré duality for open subsets of a finite-dimensional real normed space

Let `F` be a finite-dimensional real normed space of dimension `d`, and `L` an abelian group. For
an open embedding `j : U → F` and any homological orientation of `U`, the duality map
`D_U : Hᵖ_c(U; L) ⟶ H_q(U; L)`, `p + q = d`, is bijective
(`TauCeti.HomologicalOrientation.bijective_dualityMap_of_isOpenEmbedding`). Tau Ceti proves this
when the image of `j` is convex (`TauCeti.HomologicalOrientation.bijective_dualityMap_of_convex`);
this file removes that hypothesis.

The argument is Hatcher's, run inside `U` with its given orientation rather than among the open
sets of `F`, since an orientation of a disconnected `U` need not be restricted from one of `F`.
The open sets of `U` with convex image under `j` are closed under intersection
(`TopologicalSpace.Opens.infClosed_setOf_convex_image`), and for each of them the duality map,
for the orientation restricted from `U`, is bijective in every degree, by
`TauCeti.HomologicalOrientation.bijective_dualityMap_of_convex` along `j ∘ Subtype.val`. Their
finite unions cover `U` (`Topology.IsOpenEmbedding.iSup_finset_sup_convex_image_eq_top`), and
`Hᵈ⁺¹_c(W) = 0` for every open set `W` of `U`
(`TopCat.isZero_compactSupportCohomology_of_isOpenEmbedding`), so duality holds on `U` by the
Mayer–Vietoris induction `TauCeti.HomologicalOrientation.bijective_dualityMap_of_infClosed`.

## Main results

* `TauCeti.HomologicalOrientation.bijective_dualityMap_of_isOpenEmbedding`: Poincaré duality for
  an open subset of a finite-dimensional real normed space.

## Implementation notes

The duality maps are stated with the `ℤ`-linear structure of `ModuleCat ℤ` as a preadditive
category, while the vanishing theorem is proved for the structure of a category of modules; the
two agree since a `ℤ`-module structure is unique (`CategoryTheory.Linear.subsingletonInt`), as in
Tau Ceti's `TauCeti.HomologicalOrientation.bijective_singularCap_fundamentalClassOn_of_starConvex`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3, Lemma 3.36 and
  the case of open subsets of `ℝⁿ` in the proof of Theorem 3.35.
-/

public section

noncomputable section

open CategoryTheory Limits Module TopologicalSpace Topology Set

namespace TauCeti

attribute [local instance] MonoidalPreadditive.monoidalLinearInt

namespace HomologicalOrientation

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {d : ℕ}
  (hd : finrank ℝ F = d) (L : ModuleCat.{0} ℤ)
  {U : Type} [TopologicalSpace U] [T2Space U] [ChartedSpace F U]
  (oU : HomologicalOrientation U F d) {j : U → F}

/-- **Poincaré duality for an open subset of a finite-dimensional real normed space**: for an open
embedding `j : U → F`, the duality map `Hᵖ_c(U; L) ⟶ H_q(U; L)`, `p + q = d`, of any homological
orientation of `U` is bijective. -/
theorem bijective_dualityMap_of_isOpenEmbedding (hj : IsOpenEmbedding j) {p q : ℕ}
    (h : p + q = d) : Function.Bijective (oU.dualityMap hd L p q h) := by
  refine oU.bijective_dualityMap_of_infClosed hd L (Opens.infClosed_setOf_convex_image hj.injective)
    hj.iSup_finset_sup_convex_image_eq_top (fun W _ p q h ↦ ?_) (fun W ↦ ?_) h
  · refine (oU.comap W.isOpenEmbedding').bijective_dualityMap_of_convex hd L h
      (hj.comp W.isOpenEmbedding') ?_
    rwa [range_comp, Subtype.range_coe]
  · -- `TopCat.isZero_compactSupportCohomology_of_isOpenEmbedding` uses the `ℤ`-linear structure
    -- of `ModuleCat ℤ` as a category of modules; it agrees with the one of a preadditive
    -- category used here, as a `ℤ`-module structure is unique.
    have := Linear.subsingletonInt (ModuleCat.{0} ℤ)
    convert TopCat.isZero_compactSupportCohomology_of_isOpenEmbedding
      (ModuleCat.of ℤ (ULift ℤ : Type)) L (hj.comp W.isOpenEmbedding')
      (show finrank ℝ F < d + 1 by omega)

end HomologicalOrientation

end TauCeti
