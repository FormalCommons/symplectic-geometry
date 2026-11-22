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
`TauCeti.HomologicalOrientation.bijective_dualityMap_of_convex` along `j ∘ Subtype.val`.
Duality passes from `V`, `W` and `V ∩ W` to `V ∪ W`
(`TauCeti.HomologicalOrientation.bijective_dualityMap_comap_sup`), given `Hᵈ⁺¹_c(V ∩ W) = 0`
(`TopCat.isZero_compactSupportCohomology_of_isOpenEmbedding`), hence to all finite unions of
these sets (`InfClosed.finset_sup_induction`). These finite unions form a directed family that
covers `U` (`Topology.IsOpenEmbedding.iSup_finset_sup_convex_image_eq_top`), and duality passes to
their union (`TauCeti.HomologicalOrientation.bijective_dualityMap_of_iSup_eq_top`).

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
  -- Duality in every degree, for the orientation restricted from `U`, passes to finite unions of
  -- open sets with convex images, by Mayer–Vietoris.
  have hT (s : Finset {W : Opens U | Convex ℝ (j '' W)}) :
      ∀ p q (h : p + q = d), Function.Bijective
        ((oU.comap (s.sup Subtype.val).isOpenEmbedding').dualityMap hd L p q h) := by
    refine (Opens.infClosed_setOf_convex_image hj.injective).finset_sup_induction
      (fun W : Opens U ↦ ∀ p q (h : p + q = d), Function.Bijective
        ((oU.comap W.isOpenEmbedding').dualityMap hd L p q h)) ?_ ?_ ?_ s
    · have : IsEmpty ↥(⊥ : Opens U) := ⟨fun x ↦ x.property⟩
      exact fun p q h ↦ (oU.comap _).bijective_dualityMap_of_isEmpty hd L h
    · intro W hW p q h
      refine (oU.comap W.isOpenEmbedding').bijective_dualityMap_of_convex hd L h
        (hj.comp W.isOpenEmbedding') ?_
      rwa [range_comp, Subtype.range_coe]
    · intro V W hV hW hVW p q h
      -- `TopCat.isZero_compactSupportCohomology_of_isOpenEmbedding` uses the `ℤ`-linear structure
      -- of `ModuleCat ℤ` as a category of modules; it agrees with the one of a preadditive
      -- category used here, as a `ℤ`-module structure is unique.
      have := Linear.subsingletonInt (ModuleCat.{0} ℤ)
      refine oU.bijective_dualityMap_comap_sup hd L hV hW hVW ?_ h
      convert TopCat.isZero_compactSupportCohomology_of_isOpenEmbedding
        (ModuleCat.of ℤ (ULift ℤ : Type)) L (hj.comp (V ⊓ W).isOpenEmbedding')
        (show finrank ℝ F < d + 1 by omega)
  -- They form a directed family covering `U`.
  exact oU.bijective_dualityMap_of_iSup_eq_top hd L h (fun _ _ hst ↦ Finset.sup_mono hst)
    hj.iSup_finset_sup_convex_image_eq_top fun s ↦ hT s p q h

end HomologicalOrientation

end TauCeti
