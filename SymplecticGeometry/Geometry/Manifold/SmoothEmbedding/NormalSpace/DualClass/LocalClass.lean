/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.DualClass.Basic
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass
public import SymplecticGeometry.Geometry.Manifold.TubularNeighborhood.PointFiber
public import SymplecticGeometry.Geometry.Manifold.TubularNeighborhood.ZeroDim

/-!
# The local classes of the fundamental class of a tube

Let `f : Z → X` be a smooth embedding with normal bundle `π : ν → Z`, `Φ : ν ≅ W ⊆ X` a tube of
`f` (a diffeomorphism onto an open set, equal to `f` on the zero section) and `oX` a homological
orientation of `X` of dimension `n`. The class `tubeFundamentalClass f hn hdim Φ hΦ oX hnX hK` in
`Hₙ(ν, ν ∖ 0; ℤ)` is the fundamental class of `W` along `f(Z)`, for `oX` restricted to `W`,
carried to the normal bundle by the inverse of the pair isomorphism `tubePairIso` of `Φ`. It is
the class `μ_Φ` of
`TauCeti.SmoothEmbedding.exists_isNormalizedTube_singularCap_dualClassOf_fundamentalClass`, which
`tubeFundamentalClass_def` unfolds to that form.

This file computes its local classes at the points `0_z` of the zero section, its images in
`Hₙ(ν, ν ∖ 0_z; ℤ)`, for every tube.

* The tube carries the local class at `0_z` to the local orientation `oX (f z)`
  (`localHomologyMap_tubeFundamentalClass`). The composite of the pair maps involved is the
  inclusion of `W` followed by the restriction to `f z`, so this is Tau Ceti's
  `HomologicalOrientation.localHomologyRestriction_localHomologyMap_fundamentalClassOn_comap`.
* The tube is an open embedding, so it induces an isomorphism of local homology at `0_z`
  (Tau Ceti's `isIso_localHomologyMap`). Hence a class of `P × E` at the origin that the chart
  `Bundle.Trivialization.localChartLocalHomologyIso` and the tube carry to the local orientation
  of `X` at `f z` is the local class read in that chart
  (`localChartLocalHomologyIso_inv_tubeFundamentalClass_of_localHomologyMap`).
* For the homological orientation of a smooth orientation of `X`, the library's
  `localHomologyMap_localChartLocalHomologyIso_hom_cross` and its variants in the files
  `LocalOrientation`, `PointFiber` and `ZeroDim` of `Geometry/Manifold/TubularNeighborhood/` give
  such a class in each case of dimension: the cross product of a local class of the normal fibre
  with one of `E`, normal factor first. The local class is therefore that cross product, written
  as `SymplecticGeometry.localHomologyCross` applied to a tensor product, the form that the local
  cap computations of `Topology/VectorBundle/Thom/LocalCap.lean` take. When the normal fibre is
  a point, the sign of the normal orientation is moved to the second factor.

## Main definitions

* `TauCeti.SmoothEmbedding.tubeFundamentalClass`: the class `μ_Φ ∈ Hₙ(ν, ν ∖ 0; ℤ)` of a tube.

## Main results

* `TauCeti.SmoothEmbedding.localHomologyMap_tubeFundamentalClass`: the tube carries the local
  class at `0_z` to the local orientation of `X` at `f z`.
* `TauCeti.SmoothEmbedding.localChartLocalHomologyIso_inv_tubeFundamentalClass_of_localHomologyMap`:
  the local class at `0_z`, read in a chart of the total space, is any class that the chart and
  the tube carry to the local orientation of `X` at `f z`.
* `TauCeti.SmoothEmbedding.localChartLocalHomologyIso_inv_tubeFundamentalClass`,
  `…_of_finrank_eq_zero`, `…_of_finrank_fiber_eq_zero` and
  `…_of_finrank_eq_zero_of_finrank_fiber_eq_zero`: the local class
  at `0_z` read in the chart, for a normalized tube and the orientation of a smooth orientation
  of `X`, when `Z` and the normal fibre have positive dimension, when `Z` has dimension zero,
  when the normal fibre is a point, and when both are.

## References

* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §6 (the Poincaré
  dual of a closed submanifold through the Thom class of its normal bundle).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3 (local orientations and fundamental classes along compact sets).
-/

public section

noncomputable section

open Bundle CategoryTheory Module Set
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {H G : Type*} {E F V P Z X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace G] {I : ModelWithCorners ℝ E H}
  {J : ModelWithCorners ℝ V G}
  [TopologicalSpace Z] [ChartedSpace H Z] [IsManifold I ∞ Z]
  [TopologicalSpace X] [ChartedSpace G X] [IsManifold J ∞ X] [T2Space X] {n : ℕ}

/-- **The fundamental class of a tube.** For a tube `Φ` of `f`, a diffeomorphism of the total
space of the normal bundle `ν` onto an open set `W` of `X` that is `f` on the zero section, and a
homological orientation `oX` of `X` of dimension `n`, the class `μ_Φ ∈ Hₙ(ν, ν ∖ 0; ℤ)` that `Φ`
carries to the fundamental class of `W` along `f(Z)`, for the orientation `oX` restricted to `W`.
This is the class of `exists_isNormalizedTube_singularCap_dualClassOf_fundamentalClass`. -/
def tubeFundamentalClass (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) {W : TopologicalSpace.Opens X}
    (Φ : letI := f.normalSpaceFiberBundle hn hdim
      TotalSpace P (fun x ↦ f.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W)
    (hΦ : letI := f.normalSpaceFiberBundle hn hdim
      ∀ x, (Φ (zeroSection P _ x) : X) = f x)
    [ChartedSpace F X] (oX : HomologicalOrientation X F n) (hnX : finrank ℝ F = n)
    (hK : IsCompact (Subtype.val ⁻¹' range f : Set W)) :
    letI := f.normalSpaceFiberBundle hn hdim
    (thomPair P (fun x ↦ f.NormalSpace x hn)).singularHomology (C := ModuleCat.{0} ℤ)
      (ModuleCat.of ℤ (ULift.{0} ℤ)) n :=
  letI := f.normalSpaceFiberBundle hn hdim
  (TopPair.singularHomologyMap
    (TopPair.ofSubsetMap (X := TopCat.of W) (Y := TopCat.of W)
      (B := (Subtype.val ⁻¹' range f)ᶜ) (B' := Subtype.val ⁻¹' (range f)ᶜ) (𝟙 _)
      (fun _ hx ↦ hx) ≫ (f.tubePairIso hn hdim Φ hΦ).inv)
    (ModuleCat.of ℤ (ULift.{0} ℤ)) n).hom
    ((oX.comap W.isOpenEmbedding').fundamentalClassOn hnX hK)

/-- The class `tubeFundamentalClass` is the image of the fundamental class of `W` along `f(Z)`
under the identity of `W` followed by the inverse of the pair isomorphism of the tube. -/
theorem tubeFundamentalClass_def (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) {W : TopologicalSpace.Opens X}
    (Φ : letI := f.normalSpaceFiberBundle hn hdim
      TotalSpace P (fun x ↦ f.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W)
    (hΦ : letI := f.normalSpaceFiberBundle hn hdim
      ∀ x, (Φ (zeroSection P _ x) : X) = f x)
    [ChartedSpace F X] (oX : HomologicalOrientation X F n) (hnX : finrank ℝ F = n)
    (hK : IsCompact (Subtype.val ⁻¹' range f : Set W)) :
    letI := f.normalSpaceFiberBundle hn hdim
    f.tubeFundamentalClass hn hdim Φ hΦ oX hnX hK =
      (TopPair.singularHomologyMap
        (TopPair.ofSubsetMap (X := TopCat.of W) (Y := TopCat.of W)
          (B := (Subtype.val ⁻¹' range f)ᶜ) (B' := Subtype.val ⁻¹' (range f)ᶜ) (𝟙 _)
          (fun _ hx ↦ hx) ≫ (f.tubePairIso hn hdim Φ hΦ).inv)
        (ModuleCat.of ℤ (ULift.{0} ℤ)) n).hom
        ((oX.comap W.isOpenEmbedding').fundamentalClassOn hnX hK) :=
  (rfl)

/-- **The tube carries the local class of its fundamental class to the local orientation.** For
`z : Z`, the image of `tubeFundamentalClass f hn hdim Φ hΦ oX hnX hK` in `Hₙ(ν, ν ∖ 0_z; ℤ)`,
pushed forward along `v ↦ Φ v` to `Hₙ(X, X ∖ f z; ℤ)`, is the local orientation `oX (f z)`. -/
theorem localHomologyMap_tubeFundamentalClass (f : SmoothEmbedding I J ∞ Z X)
    (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) {W : TopologicalSpace.Opens X}
    (Φ : letI := f.normalSpaceFiberBundle hn hdim
      TotalSpace P (fun x ↦ f.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W)
    (hΦ : letI := f.normalSpaceFiberBundle hn hdim
      ∀ x, (Φ (zeroSection P _ x) : X) = f x)
    [ChartedSpace F X] (oX : HomologicalOrientation X F n) (hnX : finrank ℝ F = n)
    (hK : IsCompact (Subtype.val ⁻¹' range f : Set W)) (z : Z) :
    letI := f.normalSpaceFiberBundle hn hdim
    localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        (⟨fun p ↦ (Φ p : X), continuous_subtypeVal.comp Φ.continuous⟩ :
          C(TotalSpace P (fun x ↦ f.NormalSpace x hn), X))
        (S := {zeroSection P _ z}) (T := {f z})
        (by
          rintro p hp
          exact Φ.injective (Subtype.ext (hp.trans (hΦ z).symm)))
        n
        ((TopPair.singularHomologyMap
          (TopPair.ofSubsetMap (X := TopCat.of (TotalSpace P (fun x ↦ f.NormalSpace x hn)))
            (B := zeroSectionCompl P (fun x ↦ f.NormalSpace x hn))
            (B' := ({zeroSection P _ z}ᶜ : Set (TotalSpace P (fun x ↦ f.NormalSpace x hn))))
            (𝟙 _) fun v hv h ↦ mem_zeroSectionCompl.1 hv
              (by rw [show v = zeroSection P _ z from h]; exact zeroSection_snd ..))
          (ModuleCat.of ℤ (ULift.{0} ℤ)) n).hom
          (f.tubeFundamentalClass hn hdim Φ hΦ oX hnX hK)) = (oX (f z)).val := by
  let := f.normalSpaceFiberBundle hn hdim
  have hfz : f z ∈ (W : Set X) := by rw [← hΦ z]; exact (Φ _).property
  have h := oX.localHomologyRestriction_localHomologyMap_fundamentalClassOn_comap hnX
    W.isOpenEmbedding' (j := ⟨Subtype.val, continuous_subtypeVal⟩) hK subset_rfl
    (x := ⟨f z, hfz⟩) (mem_range_self z)
  refine Eq.trans ?_ h
  rw [tubeFundamentalClass_def, localHomologyRestriction_def, localHomologyMap_def,
    localHomologyMap_def, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply, ← TopPair.singularHomologyMap_comp,
    ← TopPair.singularHomologyMap_comp, ← TopPair.singularHomologyMap_comp]
  refine congrArg (fun g ↦ TopPair.singularHomologyMap g (ModuleCat.of ℤ (ULift.{0} ℤ)) n _)
    (TopPair.hom_ext_of_fst _ (ConcreteCategory.hom_ext _ _ fun w ↦ ?_))
  simp only [TopPair.Hom.fst_comp, ConcreteCategory.comp_apply]
  erw [TopPair.ofSubsetMap_fst_apply, TopPair.ofSubsetMap_fst_apply, TopPair.ofSubsetMap_fst_apply,
    TopPair.ofSubsetMap_fst_apply, TopPair.ofSubsetMap_fst_apply, tubePairIso_inv_fst_apply]
  simp only [TopCat.hom_ofHom, TopCat.hom_id, ContinuousMap.coe_mk, Diffeomorph.apply_symm_apply]
  exact congrArg Subtype.val (ContinuousMap.id_apply (α := W) w)

/-- **A local class of the tube's fundamental class, read in a chart of the total space.** Let `c`
be the chart of `Z` at `z` read in `E` and translated so that `z` goes to `0`, and `S` an open
set of its target containing `0` that `c⁻¹` carries into the base set of the preferred
trivialization `e` of the normal bundle at `z`. If the tube `Φ` carries the image of a class `a`
of `P × E` at the origin under `Bundle.Trivialization.localChartLocalHomologyIso` of `e` and `c`
to the local orientation of `oX` at `f z`, then that isomorphism reads the class of
`tubeFundamentalClass` at `0_z` as `a`. -/
theorem localChartLocalHomologyIso_inv_tubeFundamentalClass_of_localHomologyMap
    [I.Boundaryless] (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) {W : TopologicalSpace.Opens X}
    (Φ : letI := f.normalSpaceFiberBundle hn hdim
      TotalSpace P (fun x ↦ f.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W)
    (hΦ : letI := f.normalSpaceFiberBundle hn hdim
      ∀ x, (Φ (zeroSection P _ x) : X) = f x)
    [ChartedSpace F X] (oX : HomologicalOrientation X F n) (hnX : finrank ℝ F = n)
    (hK : IsCompact (Subtype.val ⁻¹' range f : Set W)) (z : Z) {S : Set E} (hS : IsOpen S)
    (hSc : S ⊆ ((chartAt H z).extendTrans I (Homeomorph.subRight (extChartAt I z z))).target)
    (hSe : letI := f.normalSpaceFiberBundle hn hdim
      MapsTo ((chartAt H z).extendTrans I (Homeomorph.subRight (extChartAt I z z))).symm S
        (trivializationAt P (fun x ↦ f.NormalSpace x hn) z).baseSet)
    (h0 : (0 : E) ∈ S)
    (a : localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ))
      ({0} : Set (P × E)) n)
    (ha : letI := f.normalSpaceFiberBundle hn hdim
      letI := f.normalSpaceVectorBundle hn hdim
      haveI : T1Space (TotalSpace P fun x ↦ f.NormalSpace x hn) :=
        Φ.toHomeomorph.isEmbedding.t1Space
      localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        (⟨fun p ↦ (Φ p : X), continuous_subtypeVal.comp Φ.continuous⟩ :
          C(TotalSpace P (fun x ↦ f.NormalSpace x hn), X))
        (S := {zeroSection P _ z}) (T := {f z})
        (by
          rintro p hp
          exact Φ.injective (Subtype.ext (hp.trans (hΦ z).symm)))
        n
        ((Trivialization.localChartLocalHomologyIso (ModuleCat.of ℤ (ULift.{0} ℤ)) hS hSc hSe
          (by simp) (by simp) h0 n).hom a) = (oX (f z)).val) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    haveI : T1Space (TotalSpace P fun x ↦ f.NormalSpace x hn) :=
      Φ.toHomeomorph.isEmbedding.t1Space
    (Trivialization.localChartLocalHomologyIso (ModuleCat.of ℤ (ULift.{0} ℤ)) hS hSc hSe
        (by simp) (by simp) h0 n).inv
      ((TopPair.singularHomologyMap
        (TopPair.ofSubsetMap (X := TopCat.of (TotalSpace P (fun x ↦ f.NormalSpace x hn)))
          (B := zeroSectionCompl P (fun x ↦ f.NormalSpace x hn))
          (B' := ({zeroSection P _ z}ᶜ : Set (TotalSpace P (fun x ↦ f.NormalSpace x hn))))
          (𝟙 _) fun v hv h ↦ mem_zeroSectionCompl.1 hv
            (by rw [show v = zeroSection P _ z from h]; exact zeroSection_snd ..))
        (ModuleCat.of ℤ (ULift.{0} ℤ)) n).hom
        (f.tubeFundamentalClass hn hdim Φ hΦ oX hnX hK)) = a := by
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  have : T1Space (TotalSpace P fun x ↦ f.NormalSpace x hn) := Φ.toHomeomorph.isEmbedding.t1Space
  let g : C(TotalSpace P (fun x ↦ f.NormalSpace x hn), X) :=
    ⟨fun p ↦ (Φ p : X), continuous_subtypeVal.comp Φ.continuous⟩
  -- The tube is an open embedding, so it induces an isomorphism of local homology at `0_z`.
  have hg : Topology.IsOpenEmbedding g :=
    W.isOpenEmbedding'.comp Φ.toHomeomorph.isOpenEmbedding
  have hpre : g ⁻¹' {f z} = {zeroSection P _ z} := by
    ext p
    refine ⟨fun hp ↦ Φ.injective (Subtype.ext (hp.trans (hΦ z).symm)), fun hp ↦ ?_⟩
    rw [mem_singleton_iff.1 hp]
    exact hΦ z
  have : IsIso (localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) g hpre.subset n) :=
    isIso_localHomologyMap _ g hg hpre isClosed_singleton
      (singleton_subset_iff.2 ⟨_, hΦ z⟩) n
  have hinj : Function.Injective
      (localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) g hpre.subset n) :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  rw [← hinj (ha.trans (f.localHomologyMap_tubeFundamentalClass hn hdim Φ hΦ oX hnX hK z).symm)]
  exact Iso.hom_inv_id_apply _ _

section Cases

/-! ### The local class in each case of dimension

Here `oX` is a smooth orientation of `X`, and the homological orientation of the tube's
fundamental class is the one it induces. -/

variable [I.Boundaryless] [J.Boundaryless] [ChartedSpace V X] {f : SmoothEmbedding I J ∞ Z X}
  {hn : (∞ : ℕ∞ω) ≠ 0} {hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E}
  {W : TopologicalSpace.Opens X}
  (Φ : letI := f.normalSpaceFiberBundle hn hdim
    TotalSpace P (fun x ↦ f.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W)
  (hK : IsCompact (Subtype.val ⁻¹' range f : Set W)) (z : Z) {S : Set E}

/-- **The local class of the tube's fundamental class, in positive dimension and codimension.**
Let `Z` have dimension `m + 1` and the normal fibre `P` dimension `r + 1`, with orientations `oZ`
of `Z` and `oX` of `X`, and let `Φ` be a normalized tube of `f`. In the chart of the total space
at `0_z` given by the preferred trivialization `e` of the normal bundle at `z` and the chart of
`Z` at `z` translated to `0`, the local class at `0_z` of the fundamental class of `Φ`, for the
homological orientation of `oX`, is the cross product, normal factor first, of the local
orientation of `P` selected by the normal orientation at `z` read in `e` with the local
orientation of `E` selected by `oZ` at `z`. -/
theorem localChartLocalHomologyIso_inv_tubeFundamentalClass
    (hΦ : f.IsNormalizedTube hn hdim Φ) {m r d : ℕ} (hE : finrank ℝ E = m + 1)
    (hP : finrank ℝ P = r + 1) (hV : finrank ℝ V = d + 1)
    (oX : Manifold.Orientation J X (Fin (m + 1 + finrank ℝ P)))
    (oZ : Manifold.Orientation I Z (Fin (m + 1))) (hS : IsOpen S)
    (hSc : S ⊆ ((chartAt H z).extendTrans I (Homeomorph.subRight (extChartAt I z z))).target)
    (hSe : letI := f.normalSpaceFiberBundle hn hdim
      MapsTo ((chartAt H z).extendTrans I (Homeomorph.subRight (extChartAt I z z))).symm S
        (trivializationAt P (fun x ↦ f.NormalSpace x hn) z).baseSet)
    (h0 : (0 : E) ∈ S) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    haveI : T1Space (TotalSpace P fun x ↦ f.NormalSpace x hn) :=
      Φ.toHomeomorph.isEmbedding.t1Space
    (Trivialization.localChartLocalHomologyIso (ModuleCat.of ℤ (ULift.{0} ℤ)) hS hSc hSe
        (by simp) (by simp) h0 (d + 1)).inv
      ((TopPair.singularHomologyMap
        (TopPair.ofSubsetMap (X := TopCat.of (TotalSpace P (fun x ↦ f.NormalSpace x hn)))
          (B := zeroSectionCompl P (fun x ↦ f.NormalSpace x hn))
          (B' := ({zeroSection P _ z}ᶜ : Set (TotalSpace P (fun x ↦ f.NormalSpace x hn))))
          (𝟙 _) fun v hv h ↦ mem_zeroSectionCompl.1 hv
            (by rw [show v = zeroSection P _ z from h]; exact zeroSection_snd ..))
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (d + 1)).hom
        (f.tubeFundamentalClass hn hdim Φ hΦ.apply_zeroSection
          ((oX.reindex (finCongr (by omega))).toHomologicalOrientation hV) hV hK)) =
      (SymplecticGeometry.localHomologyCross (0 : P) (0 : E) (r + 1) (m + 1) (d + 1)
          (by omega)).hom
        (((Orientation.reindex ℝ P (finCongr hP)
          ((trivializationAt P (fun x ↦ f.NormalSpace x hn) z).mapOrientation
            (Fin (finrank ℝ P)) (mem_baseSet_trivializationAt P _ z)
            (normalOrientation f hn hdim oX oZ z))).localOrientation hP).val ⊗ₜ
          (Orientation.localOrientation (F := E) (oZ.orientationAt z) hE).val) := by
  rw [← LocalOrientation.coe_cross hP hE]
  exact localChartLocalHomologyIso_inv_tubeFundamentalClass_of_localHomologyMap f hn hdim Φ
    hΦ.apply_zeroSection _ hV hK z hS hSc hSe h0 _
    (localHomologyMap_localChartLocalHomologyIso_hom_cross Φ z hΦ hE hP hV oX oZ hS hSc hSe h0)

open Classical in
/-- **The local class of the tube's fundamental class, for a zero-dimensional submanifold.** Let
`Z` have dimension zero and the normal fibre `P` dimension `r + 1`. In the setting of
`localChartLocalHomologyIso_inv_tubeFundamentalClass`, the local class at `0_z` of the
fundamental class of `Φ`, read in the chart of the total space, is the cross product, normal
factor first, of the local orientation of `P` selected by the normal orientation at `z` read in
`e` with the class of the origin of `E`, counted positively if the orientation of `Z` at `z` is
the positive orientation and negatively otherwise. -/
theorem localChartLocalHomologyIso_inv_tubeFundamentalClass_of_finrank_eq_zero
    (hΦ : f.IsNormalizedTube hn hdim Φ) {r : ℕ} (hE : finrank ℝ E = 0)
    (hP : finrank ℝ P = r + 1) (hV : finrank ℝ V = r + 1)
    (oX : Manifold.Orientation J X (Fin (0 + finrank ℝ P)))
    (oZ : Manifold.Orientation I Z (Fin 0)) (hS : IsOpen S)
    (hSc : S ⊆ ((chartAt H z).extendTrans I (Homeomorph.subRight (extChartAt I z z))).target)
    (hSe : letI := f.normalSpaceFiberBundle hn hdim
      MapsTo ((chartAt H z).extendTrans I (Homeomorph.subRight (extChartAt I z z))).symm S
        (trivializationAt P (fun x ↦ f.NormalSpace x hn) z).baseSet)
    (h0 : (0 : E) ∈ S) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    haveI : T1Space (TotalSpace P fun x ↦ f.NormalSpace x hn) :=
      Φ.toHomeomorph.isEmbedding.t1Space
    (Trivialization.localChartLocalHomologyIso (ModuleCat.of ℤ (ULift.{0} ℤ)) hS hSc hSe
        (by simp) (by simp) h0 (r + 1)).inv
      ((TopPair.singularHomologyMap
        (TopPair.ofSubsetMap (X := TopCat.of (TotalSpace P (fun x ↦ f.NormalSpace x hn)))
          (B := zeroSectionCompl P (fun x ↦ f.NormalSpace x hn))
          (B' := ({zeroSection P _ z}ᶜ : Set (TotalSpace P (fun x ↦ f.NormalSpace x hn))))
          (𝟙 _) fun v hv h ↦ mem_zeroSectionCompl.1 hv
            (by rw [show v = zeroSection P _ z from h]; exact zeroSection_snd ..))
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (r + 1)).hom
        (f.tubeFundamentalClass hn hdim Φ hΦ.apply_zeroSection
          ((oX.reindex (finCongr (by omega))).toHomologicalOrientation hV) hV hK)) =
      (SymplecticGeometry.localHomologyCross (0 : P) (0 : E) (r + 1) 0 (r + 1)
          (add_zero _)).hom
        (((Orientation.reindex ℝ P (finCongr hP)
          ((trivializationAt P (fun x ↦ f.NormalSpace x hn) z).mapOrientation
            (Fin (finrank ℝ P)) (mem_baseSet_trivializationAt P _ z)
            (normalOrientation f hn hdim oX oZ z))).localOrientation hP).val ⊗ₜ
          (if oZ.orientationAt z = positiveOrientation then
            (localOrientationOfZeroDimChart (OpenPartialHomeomorph.refl E)
              (OpenPartialHomeomorph.mem_refl_source _) hE).val
          else
            -(localOrientationOfZeroDimChart (OpenPartialHomeomorph.refl E)
              (OpenPartialHomeomorph.mem_refl_source _) hE).val)) :=
  localChartLocalHomologyIso_inv_tubeFundamentalClass_of_localHomologyMap f hn hdim Φ
    hΦ.apply_zeroSection _ hV hK z hS hSc hSe h0 _
    (localHomologyMap_localChartLocalHomologyIso_hom_localHomologyCross_of_finrank_eq_zero Φ z hΦ
      hE hP hV oX oZ hS hSc hSe h0)

open Classical in
/-- **The local class of the tube's fundamental class, in codimension zero.** Let the normal
fibre `P` have dimension zero and `Z` dimension `m + 1`. In the setting of
`localChartLocalHomologyIso_inv_tubeFundamentalClass`, the local class at `0_z` of the
fundamental class of `Φ`, read in the chart of the total space, is the cross product of the class
of the origin of `P` with the local orientation of `E` selected by the orientation of `Z` at `z`,
if the normal orientation at `z` read in `e` is the positive orientation of `P`, and with its
negative otherwise. -/
theorem localChartLocalHomologyIso_inv_tubeFundamentalClass_of_finrank_fiber_eq_zero
    (hΦ : f.IsNormalizedTube hn hdim Φ) {m : ℕ} (hE : finrank ℝ E = m + 1)
    (hP : finrank ℝ P = 0) (hV : finrank ℝ V = m + 1)
    (oX : Manifold.Orientation J X (Fin (m + 1 + finrank ℝ P)))
    (oZ : Manifold.Orientation I Z (Fin (m + 1))) (hS : IsOpen S)
    (hSc : S ⊆ ((chartAt H z).extendTrans I (Homeomorph.subRight (extChartAt I z z))).target)
    (hSe : letI := f.normalSpaceFiberBundle hn hdim
      MapsTo ((chartAt H z).extendTrans I (Homeomorph.subRight (extChartAt I z z))).symm S
        (trivializationAt P (fun x ↦ f.NormalSpace x hn) z).baseSet)
    (h0 : (0 : E) ∈ S) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    haveI : T1Space (TotalSpace P fun x ↦ f.NormalSpace x hn) :=
      Φ.toHomeomorph.isEmbedding.t1Space
    (Trivialization.localChartLocalHomologyIso (ModuleCat.of ℤ (ULift.{0} ℤ)) hS hSc hSe
        (by simp) (by simp) h0 (m + 1)).inv
      ((TopPair.singularHomologyMap
        (TopPair.ofSubsetMap (X := TopCat.of (TotalSpace P (fun x ↦ f.NormalSpace x hn)))
          (B := zeroSectionCompl P (fun x ↦ f.NormalSpace x hn))
          (B' := ({zeroSection P _ z}ᶜ : Set (TotalSpace P (fun x ↦ f.NormalSpace x hn))))
          (𝟙 _) fun v hv h ↦ mem_zeroSectionCompl.1 hv
            (by rw [show v = zeroSection P _ z from h]; exact zeroSection_snd ..))
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 1)).hom
        (f.tubeFundamentalClass hn hdim Φ hΦ.apply_zeroSection
          ((oX.reindex (finCongr (by omega))).toHomologicalOrientation hV) hV hK)) =
      (SymplecticGeometry.localHomologyCross (0 : P) (0 : E) 0 (m + 1) (m + 1)
          (zero_add _)).hom
        ((localOrientationOfZeroDimChart (OpenPartialHomeomorph.refl P)
            (OpenPartialHomeomorph.mem_refl_source _) hP).val ⊗ₜ
          (if Orientation.reindex ℝ P (finCongr hP)
              ((trivializationAt P (fun x ↦ f.NormalSpace x hn) z).mapOrientation
                (Fin (finrank ℝ P)) (mem_baseSet_trivializationAt P _ z)
                (normalOrientation f hn hdim oX oZ z)) = positiveOrientation then
            (Orientation.localOrientation (F := E) (oZ.orientationAt z) hE).val
          else
            -(Orientation.localOrientation (F := E) (oZ.orientationAt z) hE).val)) := by
  have h :=
    localHomologyMap_localChartLocalHomologyIso_hom_localHomologyCross_of_finrank_fiber_eq_zero
      Φ z hΦ hE hP hV oX oZ hS hSc hSe h0
  refine localChartLocalHomologyIso_inv_tubeFundamentalClass_of_localHomologyMap f hn hdim Φ
    hΦ.apply_zeroSection _ hV hK z hS hSc hSe h0 _ ?_
  split_ifs with hc
  · rwa [ite_eq_left hc] at h
  · rw [ite_eq_right hc] at h
    rw [TensorProduct.tmul_neg, map_neg, map_neg, map_neg, h, neg_neg]

omit [J.Boundaryless] in
open Classical in
/-- **The local class of the tube's fundamental class, in dimension zero.** Let `Z` and the normal
fibre `P` both have dimension zero, so that `X` has dimension zero too. In the setting of
`localChartLocalHomologyIso_inv_tubeFundamentalClass`, with the zero-dimensional homological
orientation `toHomologicalOrientationOfZeroDim` of `oX`, the local class at `0_z` of the
fundamental class of `Φ`, read in the chart of the total space, is the cross product of the class
of the origin of `P` with the class of the origin of `E`, counted positively if the orientation of
`Z` at `z` and the normal orientation at `z` read in `e` are both positive or both negative, and
negatively otherwise. -/
theorem
    localChartLocalHomologyIso_inv_tubeFundamentalClass_of_finrank_eq_zero_of_finrank_fiber_eq_zero
    (hΦ : f.IsNormalizedTube hn hdim Φ) (hE : finrank ℝ E = 0) (hP : finrank ℝ P = 0)
    (oX : Manifold.Orientation J X (Fin (0 + finrank ℝ P)))
    (oZ : Manifold.Orientation I Z (Fin 0)) (hS : IsOpen S)
    (hSc : S ⊆ ((chartAt H z).extendTrans I (Homeomorph.subRight (extChartAt I z z))).target)
    (hSe : letI := f.normalSpaceFiberBundle hn hdim
      MapsTo ((chartAt H z).extendTrans I (Homeomorph.subRight (extChartAt I z z))).symm S
        (trivializationAt P (fun x ↦ f.NormalSpace x hn) z).baseSet)
    (h0 : (0 : E) ∈ S) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    haveI : T1Space (TotalSpace P fun x ↦ f.NormalSpace x hn) :=
      Φ.toHomeomorph.isEmbedding.t1Space
    (Trivialization.localChartLocalHomologyIso (ModuleCat.of ℤ (ULift.{0} ℤ)) hS hSc hSe
        (by simp) (by simp) h0 0).inv
      ((TopPair.singularHomologyMap
        (TopPair.ofSubsetMap (X := TopCat.of (TotalSpace P (fun x ↦ f.NormalSpace x hn)))
          (B := zeroSectionCompl P (fun x ↦ f.NormalSpace x hn))
          (B' := ({zeroSection P _ z}ᶜ : Set (TotalSpace P (fun x ↦ f.NormalSpace x hn))))
          (𝟙 _) fun v hv h ↦ mem_zeroSectionCompl.1 hv
            (by rw [show v = zeroSection P _ z from h]; exact zeroSection_snd ..))
        (ModuleCat.of ℤ (ULift.{0} ℤ)) 0).hom
        (f.tubeFundamentalClass hn hdim Φ hΦ.apply_zeroSection
          ((oX.reindex (finCongr ((zero_add _).trans hP))).toHomologicalOrientationOfZeroDim)
          (by omega) hK)) =
      (SymplecticGeometry.localHomologyCross (0 : P) (0 : E) 0 0 0 rfl).hom
        ((localOrientationOfZeroDimChart (OpenPartialHomeomorph.refl P)
            (OpenPartialHomeomorph.mem_refl_source _) hP).val ⊗ₜ
          (if Orientation.reindex ℝ P (finCongr hP)
              ((trivializationAt P (fun x ↦ f.NormalSpace x hn) z).mapOrientation
                (Fin (finrank ℝ P)) (mem_baseSet_trivializationAt P _ z)
                (normalOrientation f hn hdim oX oZ z)) = positiveOrientation then
            (if oZ.orientationAt z = positiveOrientation then
              (localOrientationOfZeroDimChart (OpenPartialHomeomorph.refl E)
                (OpenPartialHomeomorph.mem_refl_source _) hE).val
            else -(localOrientationOfZeroDimChart (OpenPartialHomeomorph.refl E)
                (OpenPartialHomeomorph.mem_refl_source _) hE).val)
          else
            -(if oZ.orientationAt z = positiveOrientation then
              (localOrientationOfZeroDimChart (OpenPartialHomeomorph.refl E)
                (OpenPartialHomeomorph.mem_refl_source _) hE).val
            else -(localOrientationOfZeroDimChart (OpenPartialHomeomorph.refl E)
                (OpenPartialHomeomorph.mem_refl_source _) hE).val))) := by
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  have h := localHomologyMap_localChartLocalHomologyIso_hom_cross_of_finrank_eq_zero
    Φ z hΦ hE hP oX oZ hS hSc hSe h0
  refine localChartLocalHomologyIso_inv_tubeFundamentalClass_of_localHomologyMap f hn hdim Φ
    hΦ.apply_zeroSection _ (by omega) hK z hS hSc hSe h0 _ ?_
  by_cases hc : Orientation.reindex ℝ P (finCongr hP)
      ((trivializationAt P (fun x ↦ f.NormalSpace x hn) z).mapOrientation
        (Fin (finrank ℝ P)) (mem_baseSet_trivializationAt P _ z)
        (normalOrientation f hn hdim oX oZ z)) = positiveOrientation
  · rw [ite_eq_left hc] at h ⊢
    exact h
  · rw [ite_eq_right hc] at h ⊢
    rwa [TensorProduct.tmul_neg, ← TensorProduct.neg_tmul]

end Cases

end TauCeti.SmoothEmbedding

end
