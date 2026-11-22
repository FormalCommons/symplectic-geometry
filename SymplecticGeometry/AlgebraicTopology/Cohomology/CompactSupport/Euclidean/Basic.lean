/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Euclidean.Basic
public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Extension
public import SymplecticGeometry.AlgebraicTopology.Cohomology.CompactSupport.Vanishing
public import SymplecticGeometry.Analysis.Convex.Opens

/-!
# Vanishing of cohomology with compact supports on star-convex open sets

Let `F` be a finite-dimensional real normed space and `j : U → F` an open embedding whose image is
star-convex about `y`. Then `Hⁿ_c(U; R, N) = 0` for every `n ≠ finrank ℝ F`, for projective
coefficients `R` (`TopCat.isZero_compactSupportCohomology_of_starConvex`), and in particular for
an open embedding with convex image (`TopCat.isZero_compactSupportCohomology_of_convex`). This
extends Tau Ceti's `TopCat.isZero_compactSupportCohomology_euclidean`, the case `U = F`.

For empty `U` the groups vanish (`TopCat.isZero_compactSupportCohomology_of_isEmpty`). For
nonempty `U`, the point `y` lies in the image of `j`. Every class of `Hⁿ_c(U)` comes from
`Hⁿ(U, U ∖ K)` for a compact `K` whose image is the star hull about `y` of the image of a given
compact set: these star hulls stay inside the image of `j`, as in the proof of Tau Ceti's
`TauCeti.HomologicalOrientation.bijective_dualityMap_of_starConvex`, whose cofinality argument this
file adapts. By excision (`TopCat.singularCohomologyComplCompactsMapIso`) and since removing a
bounded star-convex set from `F` does not change its cohomology
(`TauCeti.isIso_singularCohomologyMap_compl_of_starConvex`), `Hⁿ(U, U ∖ K)` is the local cohomology
`Hⁿ(F, F ∖ {y})`, which vanishes outside the dimension
(`TauCeti.isZero_singularCohomology_complSingleton_of_ne`).

This vanishing above the dimension is what the Mayer–Vietoris step of Poincaré duality needs
besides duality itself, in the induction over convex open sets of Hatcher's Lemma 3.36. That
induction, run for vanishing alone, gives `Hⁿ_c(U) = 0` for `n > finrank ℝ F` and every `U` that
embeds openly in `F` (`TopCat.isZero_compactSupportCohomology_of_isOpenEmbedding`): it holds for
the open sets of `U` with convex image, which are closed under intersection
(`TopologicalSpace.Opens.infClosed_setOf_convex_image`) and which cover `U`
(`Topology.IsOpenEmbedding.sSup_setOf_convex_image_eq_top`), so it holds on `U` by
`TopCat.isZero_compactSupportCohomology_of_infClosed`.

## Main results

* `TopCat.isZero_compactSupportCohomology_of_starConvex`: `Hⁿ_c(U) = 0` for `n ≠ finrank ℝ F` and
  `U` embedded in `F` with star-convex image.
* `TopCat.isZero_compactSupportCohomology_of_convex`: the same for a convex image.
* `TopCat.isZero_compactSupportCohomology_of_isOpenEmbedding`: `Hⁿ_c(U) = 0` for
  `n > finrank ℝ F` and any `U` embedded openly in `F`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, Lemma 3.36 and the proof of Theorem 3.35.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace Topology Module Set

universe v

namespace TopCat

variable {k : Type v} [CommRing k] (R N : ModuleCat.{v} k) [Module.Projective k R]
  {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {U : Type v} [TopologicalSpace U]

/-- **Cohomology with compact supports of a star-convex open set vanishes outside the
dimension.** For an open embedding `j : U → F` into a finite-dimensional real normed space whose
image is star-convex, `Hⁿ_c(U; R, N) = 0` for `n ≠ finrank ℝ F`, for projective coefficients `R`
and any coefficient module `N`. -/
theorem isZero_compactSupportCohomology_of_starConvex {j : U → F} (hj : IsOpenEmbedding j)
    {y : F} (hU : StarConvex ℝ y (range j)) {n : ℕ} (h : n ≠ finrank ℝ F) :
    IsZero ((of U).compactSupportCohomology R k N n) := by
  rcases isEmpty_or_nonempty U with hU₀ | ⟨⟨u₀⟩⟩
  · -- the carrier of `of U` is `U`
    have : IsEmpty (of U) := hU₀
    exact isZero_compactSupportCohomology_of_isEmpty R k N (of U) n
  have hy : y ∈ range j := hU.mem ⟨j u₀, u₀, rfl⟩
  let f : of U ⟶ of F := ofHom ⟨j, hj.continuous⟩
  -- the underlying function of `f` is `j`
  have hf : IsOpenEmbedding f := hj
  refine ModuleCat.isZero_iff_subsingleton.2 ⟨fun a b ↦ ?_⟩
  suffices ∀ x : (of U).compactSupportCohomology R k N n, x = 0 by rw [this a, this b]
  intro x
  obtain ⟨K₀, -, w, rfl⟩ := exists_compactSupportCohomologyι_eq x ⊥
  -- The star hull about `y` of the image of `K₀` lies in the image of `j`.
  let S := Compacts.starHull (E := F) ℝ y (K₀.map f f.hom.continuous)
  have hS : (S : Set F) ⊆ range j := Compacts.starHull_subset hU hy (by
    rintro _ ⟨u, -, rfl⟩
    exact ⟨u, rfl⟩)
  let K : Compacts (of U) := ⟨j ⁻¹' S, hj.isInducing.isCompact_preimage' S.isCompact hS⟩
  have hKS : ((K.map f f.hom.continuous : Compacts (of F)) : Set F) = S :=
    image_preimage_eq_of_subset hS
  have hK₀K : K₀ ≤ K := fun u hu ↦ Compacts.le_starHull (E := F) ℝ y _ ⟨u, hu, rfl⟩
  -- `Hⁿ(U, U ∖ K)` is, by excision and star-convexity, the local cohomology of `F` at `y`.
  have hZ : IsZero ((TopPair.ofSubset (K : Set (of U))ᶜ).singularCohomology R k N n) := by
    have hSy : StarConvex ℝ y ((K.map f f.hom.continuous : Compacts (of F)) : Set F) :=
      hKS ▸ Compacts.starConvex_starHull (E := F) ℝ y _
    have hyS : y ∈ ((K.map f f.hom.continuous : Compacts (of F)) : Set F) :=
      hKS ▸ Compacts.mem_starHull_self (E := F) ℝ y _
    have := TauCeti.isIso_singularCohomologyMap_compl_of_starConvex R k N hSy hyS
      (K.map f f.hom.continuous).isCompact.isBounded n
    exact ((TauCeti.isZero_singularCohomology_complSingleton_of_ne R N
      (OpenPartialHomeomorph.refl F) (x := y) (mem_univ _) rfl h).of_iso
      (@asIso _ _ _ _ _ this).symm).of_iso
      (singularCohomologyComplCompactsMapIso R k N hf K n).symm
  have := ModuleCat.subsingleton_of_isZero hZ
  rw [← singularCohomologyMap_comp_compactSupportCohomologyι n hK₀K, ConcreteCategory.comp_apply,
    Subsingleton.elim (TopPair.singularCohomologyMap _ n w) 0, map_zero]

/-- **Cohomology with compact supports of a convex open set vanishes outside the dimension.** For
an open embedding `j : U → F` into a finite-dimensional real normed space with convex image,
`Hⁿ_c(U; R, N) = 0` for `n ≠ finrank ℝ F`. -/
theorem isZero_compactSupportCohomology_of_convex {j : U → F} (hj : IsOpenEmbedding j)
    (hU : Convex ℝ (range j)) {n : ℕ} (h : n ≠ finrank ℝ F) :
    IsZero ((of U).compactSupportCohomology R k N n) := by
  rcases (range j).eq_empty_or_nonempty with hU₀ | ⟨y, hy⟩
  · exact isZero_compactSupportCohomology_of_starConvex R N hj (y := 0)
      (hU₀ ▸ starConvex_empty 0) h
  · exact isZero_compactSupportCohomology_of_starConvex R N hj (hU.starConvex hy) h

/-- **Cohomology with compact supports of an open subset of `F` vanishes above the dimension.**
For an open embedding `j : U → F` into a finite-dimensional real normed space,
`Hⁿ_c(U; R, N) = 0` for `n > finrank ℝ F`, for projective coefficients `R`. -/
theorem isZero_compactSupportCohomology_of_isOpenEmbedding {j : U → F} (hj : IsOpenEmbedding j)
    {n : ℕ} (hn : finrank ℝ F < n) :
    IsZero ((of U).compactSupportCohomology R k N n) := by
  have := hj.isEmbedding.t2Space
  refine isZero_compactSupportCohomology_of_infClosed R k N
    (Opens.infClosed_setOf_convex_image hj.injective) hj.sSup_setOf_convex_image_eq_top
    (fun W _ m hm ↦ ?_) hn
  refine isZero_compactSupportCohomology_of_convex R N (hj.comp W.isOpenEmbedding') ?_ (by omega)
  rwa [range_comp, Subtype.range_coe]

end TopCat

end
