/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Euclidean.Basic
public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Euclidean.Duality
public import TauCeti.CategoryTheory.Linear.Int
public import TauCeti.Order.SupClosed
public import SymplecticGeometry.Analysis.Convex.GaugeRescale
public import SymplecticGeometry.AlgebraicTopology.Cohomology.CompactSupport.Duality.Union

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
Call an open set `W` of `U` *convex* if `j '' W` is convex and bounded. Such sets are closed under
intersection and cover `U`, since every point has such a neighbourhood, the preimage of a ball of
`F` contained in the image of `j`. For each of them

* the duality map, for the orientation restricted from `U`, is bijective in every degree, by
  `TauCeti.HomologicalOrientation.bijective_dualityMap_of_convex` along `j ∘ Subtype.val`;
* `Hᵐ_c(W) = 0` for `m ≠ d`, since `W` is empty or homeomorphic to `F`
  (`TopCat.isZero_compactSupportCohomology_of_isOpenEmbedding_of_convex`).

Vanishing in the degrees `m > d` passes from `V`, `W` and `V ∩ W` to `V ∪ W`
(`TopCat.isZero_compactSupportCohomology_sup`), and so does duality
(`TauCeti.HomologicalOrientation.bijective_dualityMap_comap_sup`), given `Hᵈ⁺¹_c(V ∩ W) = 0`.
As the intersection of a convex open set with a union of `k` of them is a union of `k` of them,
both pass to all finite unions of convex open sets (`TauCeti.finset_sup_of_inf_closed`). These
form a directed family covering `U`, and both pass to directed unions
(`TopCat.isZero_compactSupportCohomology_of_iSup_eq_top` and
`TauCeti.HomologicalOrientation.bijective_dualityMap_of_iSup_eq_top`). The vanishing is proved
first, for every space that embeds openly in `F`
(`TopCat.isZero_compactSupportCohomology_of_isOpenEmbedding`), so that the induction for duality
can use it on `V ∩ W`.

## Main results

* `TopCat.isZero_compactSupportCohomology_of_isOpenEmbedding_of_convex`: `Hⁿ_c(X) = 0` for
  `n ≠ finrank ℝ F` when `X` embeds openly in `F` with bounded convex image.
* `TopCat.isZero_compactSupportCohomology_of_isOpenEmbedding`: `Hⁿ_c(X) = 0` for
  `n > finrank ℝ F` when `X` embeds openly in `F`.
* `TauCeti.HomologicalOrientation.bijective_dualityMap_of_isOpenEmbedding`: Poincaré duality for
  an open subset of a finite-dimensional real normed space.

## Implementation notes

The induction for duality uses the vanishing theorem with the `ℤ`-linear structure of
`ModuleCat ℤ` as a preadditive category, under which the duality maps are stated, while the
vanishing theorem is proved for the structure of a category of modules; the two agree since a
`ℤ`-module structure is unique (`CategoryTheory.Linear.subsingletonInt`), as in Tau Ceti's
`TauCeti.HomologicalOrientation.bijective_singularCap_fundamentalClassOn_of_starConvex`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3, Lemma 3.36 and
  the case of open subsets of `ℝⁿ` in the proof of Theorem 3.35.
-/

public section

noncomputable section

open CategoryTheory Limits Module TopologicalSpace Topology Set Bornology Metric

universe v

namespace TopCat

/-! ### Open sets with bounded convex image -/

section ConvexOpens

variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F] {X : Type v} [TopologicalSpace X]

/-- The open sets of `X` whose images under `j` are bounded and convex. -/
private def convexOpens (j : X → F) : Set (Opens X) :=
  {W | Convex ℝ (j '' W) ∧ IsBounded (j '' W)}

/-- For `W` in `convexOpens j`, the image of the open embedding `j ∘ Subtype.val : W → F` is
convex and bounded. -/
private lemma convex_isBounded_range_of_mem_convexOpens {j : X → F} {W : Opens X}
    (hW : W ∈ convexOpens j) :
    Convex ℝ (range (j ∘ Subtype.val : W → F)) ∧ IsBounded (range (j ∘ Subtype.val : W → F)) := by
  have h : range (j ∘ Subtype.val : W → F) = j '' W := by rw [range_comp, Subtype.range_coe]
  rw [h]
  exact hW

/-- The intersection of two open sets with bounded convex images has bounded convex image. -/
private lemma infClosed_convexOpens {j : X → F} (hj : Function.Injective j) :
    InfClosed (convexOpens j) := by
  rintro V ⟨hVc, hVb⟩ W ⟨hWc, -⟩
  simp only [convexOpens, mem_ofPred_eq, Opens.coe_inf, image_inter hj]
  exact ⟨hVc.inter hWc, hVb.subset inter_subset_left⟩

/-- A property of open sets that holds for `⊥` and for the open sets with bounded convex images,
and passes from `V`, `W` and `V ⊓ W` to `V ⊔ W`, holds for their finite unions. -/
private lemma finsetSup_convexOpens_induction {j : X → F} (hj : Function.Injective j)
    (P : Opens X → Prop) (hbot : P ⊥) (hbase : ∀ W ∈ convexOpens j, P W)
    (hsup : ∀ V W, P V → P W → P (V ⊓ W) → P (V ⊔ W)) (s : Finset (convexOpens j)) :
    P (s.sup Subtype.val) := by
  classical
  -- `s.sup Subtype.val` is the union of the finite set `s.image Subtype.val` of open sets.
  rw [← Function.id_comp Subtype.val, ← Finset.sup_image]
  refine TauCeti.finset_sup_of_inf_closed P (infClosed_convexOpens hj) hbot hbase hsup _
    fun _ hV ↦ ?_
  obtain ⟨W, -, rfl⟩ := Finset.mem_image.1 hV
  exact W.property

/-- The finite unions of open sets with bounded convex images cover `X`: every point has such a
neighbourhood, the preimage of a ball of `F` contained in the image of `j`. -/
private lemma iSup_finsetSup_convexOpens {j : X → F} (hj : IsOpenEmbedding j) :
    ⨆ s : Finset (convexOpens j), s.sup Subtype.val = ⊤ := by
  refine eq_top_iff.2 fun x _ ↦ ?_
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hj.isOpen_range (j x) ⟨x, rfl⟩
  let W : Opens X := ⟨j ⁻¹' Metric.ball (j x) r, isOpen_ball.preimage hj.continuous⟩
  have hW : j '' W = Metric.ball (j x) r := image_preimage_eq_of_subset hball
  refine Opens.mem_iSup.2 ⟨{⟨W, hW ▸ convex_ball _ _, hW ▸ isBounded_ball⟩}, ?_⟩
  simpa [W] using hr

end ConvexOpens

/-! ### Vanishing above the dimension -/

variable {k : Type v} [CommRing k] (R N : ModuleCat.{v} k) [Module.Projective k R]
  {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **Cohomology with compact supports of a bounded convex open set.** If `X` embeds openly in a
finite-dimensional real normed space `F` with bounded convex image, then `Hⁿ_c(X; R, N) = 0` for
`n ≠ finrank ℝ F`, for projective coefficients `R`. -/
theorem isZero_compactSupportCohomology_of_isOpenEmbedding_of_convex {X : Type v}
    [TopologicalSpace X] {j : X → F} (hj : IsOpenEmbedding j) (hc : Convex ℝ (range j))
    (hb : IsBounded (range j)) {n : ℕ} (hn : n ≠ finrank ℝ F) :
    IsZero ((of X).compactSupportCohomology R k N n) := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x⟩⟩
  · exact isZero_compactSupportCohomology_of_isEmpty R k N (of X) n
  obtain ⟨e⟩ := hc.nonempty_homeomorph_of_isOpen_of_isBounded hj.isOpen_range ⟨j x, x, rfl⟩ hb
  exact (isZero_compactSupportCohomology_iff_of_homeomorph R k N (X := of X) (Y := of F)
    (hj.isEmbedding.toHomeomorph.trans e) n).2 (isZero_compactSupportCohomology_euclidean R N hn)

/-- **Cohomology with compact supports of an open subset of `F` vanishes above the dimension.**
If `X` embeds openly in a finite-dimensional real normed space `F`, then `Hⁿ_c(X; R, N) = 0` for
`n > finrank ℝ F`, for projective coefficients `R`. -/
theorem isZero_compactSupportCohomology_of_isOpenEmbedding {X : Type v} [TopologicalSpace X]
    {j : X → F} (hj : IsOpenEmbedding j) {n : ℕ} (hn : finrank ℝ F < n) :
    IsZero ((of X).compactSupportCohomology R k N n) := by
  have := hj.isEmbedding.t2Space
  -- Vanishing passes to finite unions of open sets with bounded convex images, by Mayer–Vietoris.
  have hT (s : Finset (convexOpens j)) (m : ℕ) (hm : finrank ℝ F < m) :
      IsZero ((of ↥(s.sup Subtype.val)).compactSupportCohomology R k N m) := by
    refine finsetSup_convexOpens_induction hj.injective (fun W : Opens X ↦ ∀ m, finrank ℝ F < m →
        IsZero ((of W).compactSupportCohomology R k N m)) ?_ ?_ ?_ s m hm
    · have : IsEmpty ↥(⊥ : Opens X) := ⟨fun x ↦ x.property⟩
      exact fun m _ ↦ isZero_compactSupportCohomology_of_isEmpty R k N _ m
    · intro W hW m hm
      exact isZero_compactSupportCohomology_of_isOpenEmbedding_of_convex R N
        (hj.comp W.isOpenEmbedding') (convex_isBounded_range_of_mem_convexOpens hW).1
        (convex_isBounded_range_of_mem_convexOpens hW).2 (by omega)
    · exact fun V W hV hW hVW m hm ↦ isZero_compactSupportCohomology_sup R k N (hV m hm)
        (hW m hm) (hVW (m + 1) (by omega))
  -- They form a directed family covering `X`; `(Opens.toTopCat (of X)).obj W` is `of W` by
  -- definition.
  exact isZero_compactSupportCohomology_of_iSup_eq_top R k N (X := of X)
    (U := fun s : Finset (convexOpens j) ↦ s.sup Subtype.val) (fun _ _ hst ↦ Finset.sup_mono hst)
    (iSup_finsetSup_convexOpens hj) fun s ↦ hT s n hn

end TopCat

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
  -- open sets with bounded convex images, by Mayer–Vietoris.
  have hT (s : Finset (TopCat.convexOpens j)) :
      ∀ p q (h : p + q = d), Function.Bijective
        ((oU.comap (s.sup Subtype.val).isOpenEmbedding').dualityMap hd L p q h) := by
    refine TopCat.finsetSup_convexOpens_induction hj.injective (fun W : Opens U ↦
        ∀ p q (h : p + q = d), Function.Bijective
          ((oU.comap W.isOpenEmbedding').dualityMap hd L p q h)) ?_ ?_ ?_ s
    · have : IsEmpty ↥(⊥ : Opens U) := ⟨fun x ↦ x.property⟩
      exact fun p q h ↦ (oU.comap _).bijective_dualityMap_of_isEmpty hd L h
    · intro W hW p q h
      exact (oU.comap W.isOpenEmbedding').bijective_dualityMap_of_convex hd L h
        (hj.comp W.isOpenEmbedding') (TopCat.convex_isBounded_range_of_mem_convexOpens hW).1
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
    (TopCat.iSup_finsetSup_convexOpens hj) fun s ↦ hT s p q h

end HomologicalOrientation

end TauCeti
