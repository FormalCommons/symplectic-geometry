/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Orientation.OpenEmbedding
public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.DualClass.Basic
public import TauCeti.AlgebraicTopology.Cohomology.Cap.Relative
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass
public import SymplecticGeometry.Topology.VectorBundle.TotalSpaceHomotopy
public import TauCeti.CategoryTheory.Monoidal.Preadditive

/-!
# The cap product of a dual class with the fundamental class

Let `f : Z → X` be a smooth embedding with closed range into a compact manifold `X`, with normal
bundle `π : ν → Z`, and let `oX` be a homological orientation of `X` in its dimension `n`, with
fundamental class `[X] ∈ Hₙ(X; ℤ)`. This file moves the cap product `dualClassOf f u ⌢ [X]` of
the class of `X` given by a class `u ∈ Hᵖ(ν, ν ∖ 0)` into the normal bundle: for the normalized
tube `Φ : ν ≅ W ⊆ X` through which `TauCeti.SmoothEmbedding.relDualClassOf` is defined (the
statement only asserts that some normalized tube has this property),

`dualClassOf f u ⌢ [X] = (f ∘ π)_* (u ⌢ μ_Φ)`,

where `μ_Φ ∈ Hₙ(ν, ν ∖ 0)` is the fundamental class of `W` along `f(Z)`, for the orientation of
`W` restricted from `oX` (Tau Ceti's `HomologicalOrientation.comap` and
`HomologicalOrientation.fundamentalClassOn`), carried to the normal bundle by the pair isomorphism
`TauCeti.SmoothEmbedding.tubePairIso` of `Φ`.

The proof has three steps.

* The cap product with `[X]` of the image of a relative class `α ∈ Hᵖ(X, X ∖ f(Z))` is the
  relative cap product of `α` with the image of `[X]` in `Hₙ(X, X ∖ f(Z))`
  (Tau Ceti's `TopPair.singularCap_singularCohomologyπ`), and that image is the fundamental class
  of `X` along the compact set `f(Z)` (`HomologicalOrientation.singularHomologyπ_fundamentalClass`).
* The fundamental class of `X` along `f(Z)` is the image of that of `W`, as both restrict to the
  local orientations of `oX` (`HomologicalOrientation.eq_fundamentalClassOn` and
  `HomologicalOrientation.localHomologyRestriction_localHomologyMap_fundamentalClassOn_comap`), so
  naturality of the relative cap product (`TopPair.singularCap_naturality`) along excision and
  along the tube carries the cap product to the normal bundle.
* The tube followed by the inclusion of `W` is homotopic to `f ∘ π`, since `Φ` is `f` on the zero
  section and the zero section after `π` is homotopic to the identity of `ν`
  (Tau Ceti's `VectorBundle.totalSpaceHomotopyEquiv`, through
  `TauCeti.VectorBundle.homotopic_comp_zeroSection_proj`), so both maps act alike on homology.

Tau Ceti's `TauCeti.IsFramedTube.singularCap_pontryaginThomCollapse` runs through the same three
steps for a framed tube and its collapse map.

The statement holds for every class `u`, every degree and every coefficient group `L`, so that it
covers the canonical Thom class of a normal orientation and the case of codimension zero.

## Main results

* `TauCeti.SmoothEmbedding.exists_isNormalizedTube_singularCap_dualClassOf_fundamentalClass`: the
  cap product of `dualClassOf f hn hdim hf u` with the fundamental class of `X` is the push-forward
  along `f ∘ π` of the cap product of `u` with `μ_Φ`.

## References

* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §6 (the Poincaré
  dual of a closed submanifold through the Thom class of its normal bundle).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3 (naturality of the cap product, fundamental classes along compact sets).
-/

public section

noncomputable section

open Bundle CategoryTheory MonoidalCategory Module Set AlgebraicTopology
open scoped Manifold ContDiff

attribute [local instance] MonoidalPreadditive.monoidalLinearInt

namespace TauCeti.SmoothEmbedding

variable {E H G : Type*} {F : Type} {V P Z X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace G] {I : ModelWithCorners ℝ E H}
  {J : ModelWithCorners ℝ V G} [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace Z] [ChartedSpace H Z] [IsManifold I ∞ Z]
  [TopologicalSpace X] [ChartedSpace G X] [IsManifold J ∞ X] [T2Space X]
  [SecondCountableTopology X] [CompactSpace X] [ChartedSpace F X] {n : ℕ}

/-- **The cap product of a dual class with the fundamental class, in the normal bundle.** Let
`f : Z → X` be a smooth embedding with closed range into a compact manifold `X`, with normal
bundle `π : ν → Z`, and let `oX` be a homological orientation of `X` of dimension `n`. There is a
normalized tube `Φ` of `f` onto an open set `W ⊆ X` such that, for every class
`u ∈ Hᵖ(ν, ν ∖ 0; L)` and `p + q = n`,

`dualClassOf f hn hdim hf u ⌢ [X] = (f ∘ π)_* (u ⌢ μ_Φ)` in `H_q(X; L)`,

where `μ_Φ ∈ Hₙ(ν, ν ∖ 0; ℤ)` is the fundamental class of `W` along `f(Z)`, for the orientation
`oX` restricted to `W`, carried to the normal bundle by the pair isomorphism `tubePairIso` of
`Φ` (after the identity of `W`, which writes `W ∖ f(Z)` as the preimage of `X ∖ f(Z)`). -/
theorem exists_isNormalizedTube_singularCap_dualClassOf_fundamentalClass
    (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) (hf : IsClosed (range f))
    (oX : HomologicalOrientation X F n) (hnX : finrank ℝ F = n) (L : ModuleCat.{0} ℤ) :
    letI := f.normalSpaceFiberBundle hn hdim
    ∃ (W : TopologicalSpace.Opens X)
      (Φ : TotalSpace P (fun x ↦ f.isImmersion.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W)
      (hΦ : f.IsNormalizedTube hn hdim Φ)
      (hK : IsCompact (Subtype.val ⁻¹' range f : Set W)), ∀ {p q : ℕ} (h : p + q = n)
        (u : (thomPair P (fun x ↦ f.isImmersion.NormalSpace x hn)).singularCohomology
          (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p),
        ((TopCat.of X).singularCap ℤ (ρ_ _).inv (ρ_ L).hom p q n h
            (f.dualClassOf hn hdim hf u)).hom (oX.fundamentalClass hnX) =
          (((singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).map
            (TopCat.ofHom ⟨fun v : TotalSpace P (fun x ↦ f.isImmersion.NormalSpace x hn) ↦ f v.proj,
              f.isEmbedding.continuous.comp (FiberBundle.continuous_proj P _)⟩)).hom
            (((thomPair P (fun x ↦ f.isImmersion.NormalSpace x hn)).singularCap ℤ (ρ_ _).inv
                (ρ_ L).hom
              p q n h u).hom
              ((TopPair.singularHomologyMap
                (TopPair.ofSubsetMap (X := TopCat.of W) (Y := TopCat.of W)
                  (B := (Subtype.val ⁻¹' range f)ᶜ) (B' := Subtype.val ⁻¹' (range f)ᶜ) (𝟙 _)
                  (fun _ hx ↦ hx) ≫ (f.tubePairIso hn hdim Φ hΦ.apply_zeroSection).inv)
                (ModuleCat.of ℤ (ULift.{0} ℤ)) n).hom
                ((oX.comap W.isOpenEmbedding').fundamentalClassOn hnX hK))) := by
  let := f.normalSpaceFiberBundle hn hdim
  obtain ⟨W, Φ, hΦ, hrel⟩ :=
    f.exists_isNormalizedTube_singularCohomologyMap_excisionMap_relDualClassOf
      (R := ModuleCat.of ℤ (ULift.{0} ℤ)) (k := ℤ) (M := L) hn hdim hf
  have hfW := range_subset_of_apply_zeroSection f hn hdim Φ hΦ.apply_zeroSection
  have hK : IsCompact (Subtype.val ⁻¹' range f : Set W) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hf.isCompact (by simpa using hfW)
  refine ⟨W, Φ, hΦ, hK, fun {p q} h u ↦ ?_⟩
  -- The identity of `W`, followed by the excision map, is the inclusion of `W` as a map of pairs.
  have hιex : TopPair.ofSubsetMap (X := TopCat.of W) (Y := TopCat.of W)
      (B := (Subtype.val ⁻¹' range f)ᶜ) (B' := Subtype.val ⁻¹' (range f)ᶜ) (𝟙 _)
      (fun _ hx ↦ hx) ≫ TopPair.excisionMap (X := TopCat.of X) (W : Set X) (range f)ᶜ =
      TopPair.ofSubsetMap (TopCat.ofHom ⟨Subtype.val, continuous_subtypeVal⟩)
        (B := (Subtype.val ⁻¹' range f : Set W)ᶜ) (B' := (range f)ᶜ)
        ((mapsTo_preimage _ _).mono_left (compl_subset_compl.2 subset_rfl)) :=
    TopPair.hom_ext_of_fst _ (by
      refine TopCat.ext fun x ↦ ?_
      rw [TopPair.Hom.fst_comp, TopCat.comp_app, TopPair.excisionMap_fst_apply]
      erw [TopPair.ofSubsetMap_fst_apply, TopPair.ofSubsetMap_fst_apply]
      rfl)
  -- The inclusion of `W` carries the fundamental class of `W` along `f(Z)` to that of `X`.
  have h1 : (TopPair.singularHomologyMap (TopPair.ofSubsetMap (X := TopCat.of W)
      (Y := TopCat.of W) (B := (Subtype.val ⁻¹' range f)ᶜ) (B' := Subtype.val ⁻¹' (range f)ᶜ)
      (𝟙 _) (fun _ hx ↦ hx) ≫ TopPair.excisionMap (X := TopCat.of X) (W : Set X) (range f)ᶜ)
        (ModuleCat.of ℤ (ULift.{0} ℤ)) n).hom
        ((oX.comap W.isOpenEmbedding').fundamentalClassOn hnX hK) =
      oX.fundamentalClassOn hnX hf.isCompact := by
    rw [hιex, ← localHomologyMap_def]
    exact oX.localHomologyMap_fundamentalClassOn_comap_preimage hnX W.isOpenEmbedding'
      (j := ⟨Subtype.val, continuous_subtypeVal⟩) hf.isCompact (by simpa using hfW) hK
  -- The class `μ_Φ` is carried back to the class of `W` by the tube.
  have hμ : (TopPair.singularHomologyMap (TopPair.ofSubsetMap (X := TopCat.of W)
      (Y := TopCat.of W) (B := (Subtype.val ⁻¹' range f)ᶜ) (B' := Subtype.val ⁻¹' (range f)ᶜ)
      (𝟙 _) (fun _ hx ↦ hx)) (ModuleCat.of ℤ (ULift.{0} ℤ)) n).hom
        ((oX.comap W.isOpenEmbedding').fundamentalClassOn hnX hK) =
      (TopPair.singularHomologyMap (f.tubePairIso hn hdim Φ hΦ.apply_zeroSection).hom
        (ModuleCat.of ℤ (ULift.{0} ℤ)) n).hom
        ((TopPair.singularHomologyMap
          (TopPair.ofSubsetMap (X := TopCat.of W) (Y := TopCat.of W)
            (B := (Subtype.val ⁻¹' range f)ᶜ) (B' := Subtype.val ⁻¹' (range f)ᶜ) (𝟙 _)
            (fun _ hx ↦ hx) ≫ (f.tubePairIso hn hdim Φ hΦ.apply_zeroSection).inv)
          (ModuleCat.of ℤ (ULift.{0} ℤ)) n).hom
          ((oX.comap W.isOpenEmbedding').fundamentalClassOn hnX hK)) := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← TopPair.singularHomologyMap_comp,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  -- The tube, followed by the inclusion of `W`, is homotopic to `f ∘ π`, as `Φ` is `f` on the
  -- zero section and the zero section after `π` is homotopic to the identity.
  let := f.normalSpaceVectorBundle hn hdim
  let g : C(TotalSpace P (fun x ↦ f.isImmersion.NormalSpace x hn), X) :=
    ⟨fun v ↦ (Φ v : X), continuous_subtypeVal.comp Φ.continuous⟩
  have hgf : g.Homotopic ⟨fun v ↦ f v.proj,
      f.isEmbedding.continuous.comp (FiberBundle.continuous_proj P _)⟩ :=
    VectorBundle.homotopic_comp_zeroSection_proj g (f := ⟨f, f.isEmbedding.continuous⟩)
      hΦ.apply_zeroSection
  have hg : TopPair.Hom.fst (f.tubePairIso hn hdim Φ hΦ.apply_zeroSection).hom ≫
      TopPair.Hom.fst (TopPair.excisionMap (X := TopCat.of X) (W : Set X) (range f)ᶜ) =
      TopCat.ofHom g :=
    tubePairIso_hom_fst_comp_excisionMap_fst f hn hdim Φ hΦ.apply_zeroSection
  -- Naturality of the relative cap product along excision and along the tube.
  have hnat₁ := TopPair.singularCap_naturality
    (TopPair.excisionMap (X := TopCat.of X) (W : Set X) (range f)ᶜ) ℤ (ρ_ _).inv (ρ_ L).hom
    p q n h (f.relDualClassOf hn hdim hf u)
  rw [hrel] at hnat₁
  have hnat₂ := TopPair.singularCap_naturality (f.tubePairIso hn hdim Φ hΦ.apply_zeroSection).hom
    ℤ (ρ_ _).inv (ρ_ L).hom p q n h (TopPair.singularCohomologyMap
      (f.tubePairIso hn hdim Φ hΦ.apply_zeroSection).inv p u)
  rw [← ConcreteCategory.comp_apply, ← TopPair.singularCohomologyMap_comp, Iso.hom_inv_id,
    TopPair.singularCohomologyMap_id, ModuleCat.id_apply] at hnat₂
  -- The cap product with `[X]` is the relative cap product with the image of `[X]` in
  -- `Hₙ(X, X ∖ f(Z))`.
  rw [dualClassOf_def]
  refine (ConcreteCategory.congr_hom (TopPair.singularCap_singularCohomologyπ
    (TopPair.ofSubset (X := TopCat.of X) (range f)ᶜ) ℤ (ρ_ _).inv (ρ_ L).hom p q n h
      (f.relDualClassOf hn hdim hf u)) _).trans ?_
  refine (ConcreteCategory.comp_apply _ _ _).trans ?_
  -- `erw`: the lemmas apply linear maps through `ModuleCat.Hom.hom`, the goal through
  -- `ConcreteCategory.hom`.
  erw [oX.singularHomologyπ_fundamentalClass hnX hf.isCompact, ← h1,
    TopPair.singularHomologyMap_comp, ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← hnat₁, hμ, ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply _
      (((TopPair.interPair (X := TopCat.of X) (W : Set X) (range f)ᶜ).singularCap ℤ (ρ_ _).inv
        (ρ_ L).hom p q n h) _), ← hnat₂, ← ConcreteCategory.comp_apply, Category.assoc,
    ← Functor.map_comp, hg, ContinuousMap.singularHomologyFunctor_map_eq_of_homotopic L q hgf]
  exact ConcreteCategory.comp_apply _ _ _

end TauCeti.SmoothEmbedding

end
