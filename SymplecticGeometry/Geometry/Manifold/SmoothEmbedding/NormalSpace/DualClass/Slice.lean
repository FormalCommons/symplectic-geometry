/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.DualClass.Basic
public import SymplecticGeometry.AlgebraicTopology.Cohomology.Local.Derivative
public import SymplecticGeometry.Topology.VectorBundle.Thom.FiberCoordinate
public import TauCeti.Geometry.Manifold.LocallyContractible
public import TauCeti.Topology.VectorBundle.MayerVietoris.DirectedUnion

/-!
# The dual class is determined by its normal slices

Let `f : Z → X` be a smooth embedding with closed range and normal bundle `ν` of rank
`r = finrank ℝ P`, and let `Φ` be a tube of `f` onto an open set `W ⊆ X`, equal to `f` on the zero
section. For `x : Z`, the *normal slice* of `Φ` at `x` is the map of pairs
`(ν_x, ν_x ∖ 0) ⟶ (X, X ∖ f(Z))`, `v ↦ Φ(x, v)`
(`TauCeti.SmoothEmbedding.normalSlice`): the inclusion of the fibre into the Thom pair of `ν`,
then the pair isomorphism `tubePairIso` of `Φ`, then the excision inclusion
`(W, W ∖ f(Z)) ⟶ (X, X ∖ f(Z))`.

In degree `r`, a class of the Thom pair of `ν` is determined by its restrictions to the fibres
(Tau Ceti's `TauCeti.singularCohomology_thomPair_ext`). Since `tubePairIso` is an isomorphism and
excision onto `W` is one in cohomology, a class `c ∈ Hʳ(X, X ∖ f(Z))` restricts on `(W, W ∖ f(Z))`
to the image of `u ∈ Hʳ(ν, ν ∖ 0)` under the tube exactly when, at every point `x`, its pull-back
along the normal slice at `x` is the restriction of `u` to the fibre over `x`
(`singularCohomologyMap_excisionMap_eq_iff_forall_normalSlice`). For the normalized tube through
which `relDualClassOf` is defined, this says that `c = relDualClassOf f hn hdim hf u` exactly when
the slices of `c` are the fibre restrictions of `u` (`eq_relDualClassOf_iff_forall_slice`). No
condition on `u`, such as being a Thom class, is needed; the degree must be the rank `r`, the
degree in which Tau Ceti's uniqueness by fibre restrictions holds.

## Main definitions

* `TauCeti.SmoothEmbedding.normalSlice`: the normal slice of a tube at a point, as a map of pairs.

## Main results

* `TauCeti.SmoothEmbedding.singularCohomologyMap_excisionMap_eq_iff_forall_normalSlice`: for any
  tube, a class of degree `r` restricts to the image of `u` exactly when its slices are the fibre
  restrictions of `u`.
* `TauCeti.SmoothEmbedding.eq_relDualClassOf_iff_forall_slice`: the same characterization of
  `relDualClassOf f hn hdim hf u`, through the normalized tube that defines it.

## References

* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §6
  (Proposition 6.24, the Poincaré dual of a closed submanifold as the Thom class of its normal
  bundle carried to the manifold by a tubular neighbourhood).
-/

public section

noncomputable section

open Bundle CategoryTheory Module Set Topology
open scoped Manifold ContDiff

universe w

namespace TauCeti.SmoothEmbedding

variable {E H G : Type*} {V P Z X : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [TopologicalSpace H] [TopologicalSpace G] {I : ModelWithCorners ℝ E H}
  {J : ModelWithCorners ℝ V G} [TopologicalSpace Z] [ChartedSpace H Z] [IsManifold I ∞ Z]
  [TopologicalSpace X] [ChartedSpace G X] [IsManifold J ∞ X]

section NormalSlice

/-- **The normal slice of a tube.** For a tube `Φ` of `f` onto an open set `W ⊆ X`, equal to `f`
on the zero section, and a point `x : Z`, the map of pairs `(ν_x, ν_x ∖ 0) ⟶ (X, X ∖ f(Z))`,
`v ↦ Φ(x, v)`: the fibre inclusion into the Thom pair of the normal bundle, followed by the pair
isomorphism of the tube and the inclusion `(W, W ∖ f(Z)) ⟶ (X, X ∖ f(Z))`. -/
def normalSlice (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) {W : TopologicalSpace.Opens X}
    (Φ : letI := f.normalSpaceFiberBundle hn hdim
      TotalSpace P (fun x ↦ f.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W)
    (hΦ : letI := f.normalSpaceFiberBundle hn hdim
      ∀ x, (Φ (zeroSection P _ x) : X) = f x) (x : Z) :
    TopPair.ofSubset (X := TopCat.of (f.NormalSpace x hn)) ({0}ᶜ : Set (f.NormalSpace x hn)) ⟶
      TopPair.ofSubset (X := TopCat.of X) (range f)ᶜ :=
  letI := f.normalSpaceFiberBundle hn hdim
  fiberThomPairMap P (fun x ↦ f.NormalSpace x hn) x ≫ (f.tubePairIso hn hdim Φ hΦ).hom ≫
    TopPair.excisionMap (X := TopCat.of X) (W : Set X) (range f)ᶜ

/-- The normal slice of a tube factors through the fibre inclusion, the pair isomorphism of the
tube and excision. -/
theorem normalSlice_def (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) {W : TopologicalSpace.Opens X}
    (Φ : letI := f.normalSpaceFiberBundle hn hdim
      TotalSpace P (fun x ↦ f.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W)
    (hΦ : letI := f.normalSpaceFiberBundle hn hdim
      ∀ x, (Φ (zeroSection P _ x) : X) = f x) (x : Z) :
    letI := f.normalSpaceFiberBundle hn hdim
    f.normalSlice hn hdim Φ hΦ x =
      fiberThomPairMap P (fun x ↦ f.NormalSpace x hn) x ≫ (f.tubePairIso hn hdim Φ hΦ).hom ≫
        TopPair.excisionMap (X := TopCat.of X) (W : Set X) (range f)ᶜ :=
  (rfl)

/-- On ambient spaces, the normal slice of a tube at `x` sends `v` to `Φ(x, v)`. -/
@[simp]
theorem normalSlice_fst_apply (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) {W : TopologicalSpace.Opens X}
    (Φ : letI := f.normalSpaceFiberBundle hn hdim
      TotalSpace P (fun x ↦ f.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W)
    (hΦ : letI := f.normalSpaceFiberBundle hn hdim
      ∀ x, (Φ (zeroSection P _ x) : X) = f x) (x : Z) (v : f.NormalSpace x hn) :
    TopPair.Hom.fst (f.normalSlice hn hdim Φ hΦ x) v =
      (Φ (TotalSpace.mk' P x v) : X) := by
  let := f.normalSpaceFiberBundle hn hdim
  rw [normalSlice_def, TopPair.Hom.fst_comp, TopPair.Hom.fst_comp]
  refine (ConcreteCategory.comp_apply (X := TopCat.of (f.NormalSpace x hn)) _ _ v).trans ?_
  rw [ConcreteCategory.comp_apply, TopPair.excisionMap_fst_apply]
  exact congrArg Subtype.val ((tubePairIso_hom_fst_apply f hn hdim Φ hΦ _).trans
    (congrArg Φ (fiberThomPairMap_fst_apply P (fun x ↦ f.NormalSpace x hn) x v)))

end NormalSlice

section Slice

variable {k : Type*} [CommRing k] {R M : ModuleCat.{w} k} [Module.Projective k R]

/-- **A class is determined by its normal slices.** For a tube `Φ` of `f` onto an open set `W`,
equal to `f` on the zero section, and a class `u` of the Thom pair of the normal bundle in the
degree `r = finrank ℝ P` of its rank, a class `c ∈ Hʳ(X, X ∖ f(Z))` restricts on
`(W, W ∖ f(Z))` to the image of `u` under the pair isomorphism of `Φ` exactly when, at every
`x : Z`, its pull-back along the normal slice of `Φ` at `x` is the restriction of `u` to the fibre
over `x`. -/
theorem singularCohomologyMap_excisionMap_eq_iff_forall_normalSlice
    (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) {W : TopologicalSpace.Opens X}
    (Φ : letI := f.normalSpaceFiberBundle hn hdim
      TotalSpace P (fun x ↦ f.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W)
    (hΦ : letI := f.normalSpaceFiberBundle hn hdim
      ∀ x, (Φ (zeroSection P _ x) : X) = f x)
    (u : letI := f.normalSpaceFiberBundle hn hdim
      (thomPair P (fun x ↦ f.NormalSpace x hn)).singularCohomology R k M (finrank ℝ P))
    (c : (TopPair.ofSubset (X := TopCat.of X) (range f)ᶜ).singularCohomology R k M
      (finrank ℝ P)) :
    letI := f.normalSpaceFiberBundle hn hdim
    TopPair.singularCohomologyMap (TopPair.excisionMap (X := TopCat.of X) (W : Set X) (range f)ᶜ)
        _ c = TopPair.singularCohomologyMap (f.tubePairIso hn hdim Φ hΦ).inv _ u ↔
      ∀ x, TopPair.singularCohomologyMap (f.normalSlice hn hdim Φ hΦ x) _ c =
        TopPair.singularCohomologyMap (fiberThomPairMap P (fun x ↦ f.NormalSpace x hn) x) _ u := by
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  set t := f.tubePairIso hn hdim Φ hΦ
  set e := TopPair.excisionMap (X := TopCat.of X) (W : Set X) (range f)ᶜ
  have hslice (x : Z) : TopPair.singularCohomologyMap (f.normalSlice hn hdim Φ hΦ x) _ c =
      TopPair.singularCohomologyMap (fiberThomPairMap P (fun x ↦ f.NormalSpace x hn) x) _
        (TopPair.singularCohomologyMap t.hom _ (TopPair.singularCohomologyMap e _ c)) := by
    rw [normalSlice_def, TopPair.singularCohomologyMap_comp_apply,
      TopPair.singularCohomologyMap_comp_apply]
  simp only [hslice]
  have hu := (TopPair.singularCohomologyMapIso R k M t (finrank ℝ P)).inv_hom_id_apply u
  have hc := (TopPair.singularCohomologyMapIso R k M t (finrank ℝ P)).hom_inv_id_apply
  rw [TopPair.singularCohomologyMapIso_hom, TopPair.singularCohomologyMapIso_inv] at hu hc
  refine ⟨fun h x ↦ by rw [h, hu], fun h ↦ ?_⟩
  rw [← singularCohomology_thomPair_ext h, hc]

variable [I.Boundaryless] [J.Boundaryless] [T2Space X] [SecondCountableTopology X]

/-- **The relative class of a submanifold is determined by its normal slices.** There is a
normalized tube `Φ`, the one through which `relDualClassOf` is defined, such that for every class
`u` of the Thom pair of the normal bundle in the degree `r = finrank ℝ P` of its rank, a class
`c ∈ Hʳ(X, X ∖ f(Z))` is `relDualClassOf f hn hdim hf u` exactly when, at every `x : Z`, its
pull-back along the normal slice of `Φ` at `x` is the restriction of `u` to the fibre over `x`. -/
theorem eq_relDualClassOf_iff_forall_slice (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) (hf : IsClosed (range f)) :
    letI := f.normalSpaceFiberBundle hn hdim
    ∃ (W : TopologicalSpace.Opens X)
      (Φ : TotalSpace P (fun x ↦ f.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W)
      (hΦ : f.IsNormalizedTube hn hdim Φ), ∀
        (u : (thomPair P (fun x ↦ f.NormalSpace x hn)).singularCohomology R k M (finrank ℝ P))
        (c : (TopPair.ofSubset (X := TopCat.of X) (range f)ᶜ).singularCohomology R k M
          (finrank ℝ P)),
        c = f.relDualClassOf hn hdim hf u ↔
          ∀ x, TopPair.singularCohomologyMap (f.normalSlice hn hdim Φ hΦ.apply_zeroSection x) _ c =
            TopPair.singularCohomologyMap (fiberThomPairMap P (fun x ↦ f.NormalSpace x hn) x) _
              u := by
  let := f.normalSpaceFiberBundle hn hdim
  obtain ⟨W, Φ, hΦ, h⟩ :=
    exists_isNormalizedTube_singularCohomologyMap_excisionMap_relDualClassOf (R := R) (k := k)
      (M := M) f hn hdim hf
  refine ⟨W, Φ, hΦ, fun u c ↦ ?_⟩
  have := TopPair.isIso_singularCohomologyMap_excisionMap_of_isClosed_subset R k M
    (X := TopCat.of X) W.isOpen hf
    (range_subset_of_apply_zeroSection f hn hdim Φ hΦ.apply_zeroSection) (finrank ℝ P)
  rw [← singularCohomologyMap_excisionMap_eq_iff_forall_normalSlice, ← h,
    (ConcreteCategory.injective_of_mono_of_preservesPullback _).eq_iff]

end Slice

section LocalDegree

variable {C : Type*} [Category C] [Limits.HasCoproducts.{w} C] [Abelian C] {R : C}
  {k : Type*} [Ring k] [Linear k C] {M : C}

/-- **The local-degree lemma.** Let `Φ` be a normalized tube of `f`, `x : Z`, and `e` the preferred
trivialization of the normal bundle at `x`. Let `B ⊆ P` be a neighbourhood of `0` and `g : P → X`
a map continuous on `B`, with `g 0 = f x`, sending no other point of `B` into `f(Z)`, and
differentiable at `0` with a derivative `A` such that the normal class of each `A w` is the vector
of the fibre over `x` with coordinate `w` in `e`. Then `g`, as a map of pairs
`(B, B ∖ {0}) ⟶ (X, X ∖ f(Z))`, pulls every class back as the normal slice of `Φ` at `x` does,
after `w ↦ e.symm x w`, the map of pairs `(B, B ∖ {0}) ⟶ (ν_x, ν_x ∖ {0})`. -/
theorem singularCohomologyMap_slice_eq_of_hasFDerivAt {f : SmoothEmbedding I J ∞ Z X}
    {hn : (∞ : ℕ∞ω) ≠ 0} {hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E}
    {W : TopologicalSpace.Opens X}
    {Φ : letI := f.normalSpaceFiberBundle hn hdim
      TotalSpace P (fun x ↦ f.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W}
    (hΦ : f.IsNormalizedTube hn hdim Φ) (x : Z) {B : Set P} (hB : B ∈ 𝓝 0) {g : P → X}
    (hgB : ContinuousOn g B) (hg0 : g 0 = f x) (hgf : ∀ w ∈ B, g w ∈ range f → w = 0)
    {A : P →L[ℝ] V} (hg : HasMFDerivAt 𝓘(ℝ, P) J g 0 A)
    (hA : letI := f.normalSpaceFiberBundle hn hdim
      haveI := f.normalSpaceVectorBundle hn hdim
      ∀ w : P, f.normalClassL x hn (A w) =
        (trivializationAt P (fun x ↦ f.NormalSpace x hn) x).symmL ℝ x w)
    {n : ℕ} (c : (TopPair.ofSubset (X := TopCat.of X) (range f)ᶜ).singularCohomology R k M n) :
    letI := f.normalSpaceFiberBundle hn hdim
    haveI := f.normalSpaceVectorBundle hn hdim
    TopPair.singularCohomologyMap
        (TopPair.ofSubsetMap (X := TopCat.of B) (Y := TopCat.of X)
          (TopCat.ofHom ⟨B.domRestrict g, hgB.domRestrict⟩)
          (B := {⟨0, mem_of_mem_nhds hB⟩}ᶜ) (B' := (range f)ᶜ)
          fun w hw h ↦ hw (Subtype.ext (hgf w w.property h))) n c =
      TopPair.singularCohomologyMap
        (TopPair.ofSubsetMap (X := TopCat.of B) (Y := TopCat.of (f.NormalSpace x hn))
          (TopCat.ofHom ⟨fun w ↦ (trivializationAt P (fun x ↦ f.NormalSpace x hn) x).symmL ℝ x w,
            (ContinuousLinearMap.continuous _).comp continuous_subtypeVal⟩)
          (B := {⟨0, mem_of_mem_nhds hB⟩}ᶜ) (B' := {0}ᶜ)
          fun _ hw h ↦ hw (Subtype.ext (by_contra fun h' ↦
            ((trivializationAt P (fun x ↦ f.NormalSpace x hn) x).symm_apply_ne_zero_iff ℝ
              (mem_baseSet_trivializationAt P _ x)).2 h'
              ((Trivialization.symmL_apply (R := ℝ) _ (mem_baseSet_trivializationAt P _ x)
                _).symm.trans (Set.mem_singleton_iff.1 h))))) n
        (TopPair.singularCohomologyMap (f.normalSlice hn hdim Φ hΦ.apply_zeroSection x) n c) := by
  let := f.normalSpaceFiberBundle hn hdim
  have := f.normalSpaceVectorBundle hn hdim
  classical
  set e := trivializationAt P (fun x ↦ f.NormalSpace x hn) x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt P _ x
  have hfxW : f x ∈ W := hΦ.apply_zeroSection x ▸ (Φ (zeroSection P _ x)).property
  -- The inverse of the tube, extended by the zero vector over `x` off `W`.
  let Ψ : X → TotalSpace P (fun x ↦ f.NormalSpace x hn) := fun y ↦
    if hy : y ∈ W then Φ.symm ⟨y, hy⟩ else zeroSection P _ x
  have hΨ {y : X} (hy : y ∈ W) : Ψ y = Φ.symm ⟨y, hy⟩ := by simp [Ψ, hy]
  have hΨc : ContinuousOn Ψ W := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact Φ.symm.continuous.congr fun y ↦ (hΨ y.property).symm
  have hgW : g 0 ∈ W := hg0 ▸ hfxW
  have hΨ0 : Ψ (g 0) = zeroSection P _ x := by
    rw [hΨ hgW]
    exact Φ.symm_apply_eq.2 (Subtype.ext (hg0.trans (hΦ.apply_zeroSection x).symm))
  have hΨg : ContinuousAt (fun w ↦ Ψ (g w)) 0 :=
    (hΨc.continuousAt (W.isOpen.mem_nhds hgW)).comp (hgB.continuousAt hB)
  have hΦΨ {y : X} (hy : y ∈ W) : (Φ (Ψ y) : X) = y := by
    rw [hΨ hy, Φ.apply_symm_apply]
  -- A contractible neighbourhood `U` of `x` inside the base set of `e`.
  have := I.stronglyLocallyContractibleSpace
  have := ChartedSpace.stronglyLocallyContractibleSpace H Z
  obtain ⟨U, ⟨hU, hUc⟩, hUe⟩ := (contractible_basis x).mem_iff.1 (e.open_baseSet.mem_nhds hx)
  -- A small open neighbourhood `O` of `0` on which `g` lands in `W`, over `U`.
  have hT : B ∩ g ⁻¹' W ∩ (fun w ↦ (Ψ (g w)).proj) ⁻¹' U ∈ 𝓝 0 := by
    refine Filter.inter_mem (Filter.inter_mem hB ?_) ?_
    · exact (hgB.continuousAt hB).preimage_mem_nhds (W.isOpen.mem_nhds hgW)
    · refine ((FiberBundle.continuous_proj P _).continuousAt.comp hΨg).preimage_mem_nhds ?_
      simpa [hΨ0] using hU
  set O := interior (B ∩ g ⁻¹' W ∩ (fun w ↦ (Ψ (g w)).proj) ⁻¹' U)
  have hO : IsOpen O := isOpen_interior
  have hO0 : (0 : P) ∈ O := mem_interior_iff_mem_nhds.2 hT
  have hOB : O ⊆ B := fun w hw ↦ (interior_subset hw).1.1
  have hOW : ∀ w ∈ O, g w ∈ W := fun w hw ↦ (interior_subset hw).1.2
  have hOU : ∀ w ∈ O, (Ψ (g w)).proj ∈ U := fun w hw ↦ (interior_subset hw).2
  have hψ0 : ∀ w ∈ O, w ≠ 0 → (Ψ (g w)).snd ≠ 0 := by
    intro w hw hw0 hs
    have hr : Ψ (g w) ∈ range (zeroSection P (fun x ↦ f.NormalSpace x hn)) := by
      by_contra h
      rw [← mem_compl_iff, ← zeroSectionCompl_eq_compl_range, mem_zeroSectionCompl] at h
      exact h hs
    obtain ⟨z, hz⟩ := hr
    refine hw0 (hgf w (hOB hw) ⟨z, ?_⟩)
    rw [← hΦΨ (hOW w hw), ← hz, hΦ.apply_zeroSection]
  -- Restriction from `B` to `O` is injective on cohomology: excision onto `O`, followed by the
  -- identification of `O`, as a subspace of `B`, with `O` itself.
  set S : Set (TopCat.of B) := {⟨0, mem_of_mem_nhds hB⟩}
  set A' : Set (TopCat.of B) := Subtype.val ⁻¹' O
  refine TopPair.injective_singularCohomologyMap_excisionMap_of_isClosed_subset (R := R) (k := k)
    (M := M) (U := A') (K := S) (hO.preimage continuous_subtypeVal)
    (by exact isClosed_singleton (X := B)) (singleton_subset_iff.2 hO0) n ?_
  rw [← TopPair.singularCohomologyMap_comp_apply, ← TopPair.singularCohomologyMap_comp_apply]
  let σ : O ≃ₜ A' :=
    { toFun w := ⟨⟨w, hOB w.property⟩, w.property⟩
      invFun a := ⟨a.val, a.property⟩
      left_inv _ := rfl
      right_inv _ := rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let τ := TopPair.ofSubsetIso (X := TopCat.of O) (Y := TopCat.of A') (B := {⟨0, hO0⟩}ᶜ)
    (B' := Subtype.val ⁻¹' Sᶜ) σ fun w ↦ by simp [σ, S, Subtype.ext_iff]
  have : IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) τ.hom n) :=
    TopPair.singularCohomologyMapIso_hom (R := R) (k := k) (M := M) τ n ▸
      (TopPair.singularCohomologyMapIso R k M τ n).isIso_hom
  refine ConcreteCategory.injective_of_mono_of_preservesPullback
    (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) τ.hom n) ?_
  rw [← TopPair.singularCohomologyMap_comp_apply, ← TopPair.singularCohomologyMap_comp_apply]
  -- On `O`, the map `g` factors through the inverse of the tube.
  let LO := TopPair.ofSubsetMap (X := TopCat.of O) (Y := TopCat.of X)
    (TopCat.ofHom ⟨fun w ↦ g w, (hgB.mono hOB).domRestrict⟩) (B := {⟨0, hO0⟩}ᶜ)
    (B' := (range f)ᶜ) fun w hw h ↦ hw (Subtype.ext (hgf w (hOB w.property) h))
  let RO := TopPair.ofSubsetMap (X := TopCat.of O) (Y := TopCat.of (f.NormalSpace x hn))
    (TopCat.ofHom ⟨fun w ↦ e.symmL ℝ x w,
      (ContinuousLinearMap.continuous _).comp continuous_subtypeVal⟩) (B := {⟨0, hO0⟩}ᶜ)
    (B' := {0}ᶜ) fun _ hw h ↦ hw (Subtype.ext (by_contra fun h' ↦
      (e.symm_apply_ne_zero_iff ℝ hx).2 h'
        ((Trivialization.symmL_apply (R := ℝ) _ hx _).symm.trans (Set.mem_singleton_iff.1 h))))
  have hLO : τ.hom ≫ TopPair.excisionMap A' Sᶜ ≫ TopPair.ofSubsetMap (X := TopCat.of B)
      (Y := TopCat.of X) (TopCat.ofHom ⟨B.domRestrict g, hgB.domRestrict⟩) (B := Sᶜ)
      (B' := (range f)ᶜ) (fun w hw h ↦ hw (Subtype.ext (hgf w w.property h))) = LO :=
    TopPair.hom_ext_of_fst _ (ConcreteCategory.hom_ext _ _ fun w ↦ by
      rw [TopPair.Hom.fst_comp, TopPair.Hom.fst_comp, ConcreteCategory.comp_apply,
        ConcreteCategory.comp_apply, TopPair.ofSubsetIso_hom]
      erw [TopPair.ofSubsetMap_fst_apply, TopPair.excisionMap_fst_apply,
        TopPair.ofSubsetMap_fst_apply, TopPair.ofSubsetMap_fst_apply]
      rfl)
  have hRO : τ.hom ≫ TopPair.excisionMap A' Sᶜ ≫ TopPair.ofSubsetMap (X := TopCat.of B)
      (Y := TopCat.of (f.NormalSpace x hn))
      (TopCat.ofHom ⟨fun w ↦ e.symmL ℝ x w,
        (ContinuousLinearMap.continuous _).comp continuous_subtypeVal⟩) (B := Sᶜ) (B' := {0}ᶜ)
      (fun _ hw h ↦ hw (Subtype.ext (by_contra fun h' ↦ (e.symm_apply_ne_zero_iff ℝ hx).2 h'
        ((Trivialization.symmL_apply (R := ℝ) _ hx _).symm.trans
          (Set.mem_singleton_iff.1 h))))) = RO :=
    TopPair.hom_ext_of_fst _ (ConcreteCategory.hom_ext _ _ fun w ↦ by
      rw [TopPair.Hom.fst_comp, TopPair.Hom.fst_comp, ConcreteCategory.comp_apply,
        ConcreteCategory.comp_apply, TopPair.ofSubsetIso_hom]
      erw [TopPair.ofSubsetMap_fst_apply, TopPair.excisionMap_fst_apply,
        TopPair.ofSubsetMap_fst_apply, TopPair.ofSubsetMap_fst_apply]
      rfl)
  rw [hLO, hRO]
  let ψ : TopPair.ofSubset (X := TopCat.of O) ({⟨0, hO0⟩}ᶜ) ⟶
      thomPair P (fun x ↦ f.NormalSpace x hn) :=
    TopPair.ofSubsetMap (X := TopCat.of O)
      (Y := TopCat.of (TotalSpace P (fun x ↦ f.NormalSpace x hn)))
      (TopCat.ofHom ⟨O.domRestrict (Ψ ∘ g), (hΨc.comp (hgB.mono hOB) hOW).domRestrict⟩)
      (B := {⟨0, hO0⟩}ᶜ) (B' := zeroSectionCompl P _)
      fun w hw ↦ mem_zeroSectionCompl.2 (hψ0 w w.property fun h ↦ hw (Subtype.ext h))
  have hψU : ∀ w : O, (TopPair.Hom.fst ψ w).proj ∈ U := fun w ↦ by
    erw [TopPair.ofSubsetMap_fst_apply]
    exact hOU w w.property
  have hLψ : LO = ψ ≫ (f.tubePairIso hn hdim Φ hΦ.apply_zeroSection).hom ≫
      TopPair.excisionMap (X := TopCat.of X) (W : Set X) (range f)ᶜ := by
    refine TopPair.hom_ext_of_fst _ (ConcreteCategory.hom_ext _ _ fun w ↦ ?_)
    rw [TopPair.Hom.fst_comp, TopPair.Hom.fst_comp, ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply]
    erw [TopPair.excisionMap_fst_apply, TopPair.ofSubsetMap_fst_apply,
      TopPair.ofSubsetMap_fst_apply]
    exact (hΦΨ (hOW _ (show O from w).property)).symm.trans
      (congrArg Subtype.val (tubePairIso_hom_fst_apply f hn hdim Φ _ _).symm)
  rw [hLψ, TopPair.singularCohomologyMap_comp_apply, TopPair.singularCohomologyMap_comp_apply,
    singularCohomologyMap_eq_singularCohomologyMap_fiberCoordPairMap e (U := U) hUe
      (mem_of_mem_nhds hU) ψ
      hψU, normalSlice_def, TopPair.singularCohomologyMap_comp_apply,
    TopPair.singularCohomologyMap_comp_apply]
  generalize TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
    (fiberThomPairMap P (fun x ↦ f.NormalSpace x hn) x) n _ = d
  -- Read in `e`, the fibre over `x` is `P`.
  set ℓ := e.continuousLinearEquivAt ℝ x hx
  let τ₂ := TopPair.ofSubsetIso (X := TopCat.of (f.NormalSpace x hn)) (Y := TopCat.of P)
    (B := {0}ᶜ) (B' := {0}ᶜ) ℓ.toHomeomorph fun v ↦ by simp
  rw [← (TopPair.singularCohomologyMapIso R k M τ₂ n).inv_hom_id_apply d,
    TopPair.singularCohomologyMapIso_hom, ← TopPair.singularCohomologyMap_comp_apply,
    ← TopPair.singularCohomologyMap_comp_apply]
  -- The fibre coordinate of `g` has derivative the identity at `0`.
  set F : P → P := fun w ↦ (e (Ψ (g w))).2
  have hFc : ContinuousOn F O := (e.continuousOn.comp (hΨc.comp (hgB.mono hOB) hOW)
    fun w hw ↦ e.mem_source.2 (hUe (hOU w hw))).snd
  have hF0 : F 0 = 0 := by simp [F, hΨ0, e.zeroSection ℝ hx]
  have hF : HasFDerivAt F (ContinuousLinearMap.id ℝ P) 0 :=
    hΦ.hasFDerivAt_trivializationAt_snd hg hA hΨg hΨ0
      (by filter_upwards [hO.mem_nhds hO0] with w hw using hΦΨ (hOW w hw))
  have hFx : ∀ w ∈ O, F w = F 0 → w = 0 := fun w hw h ↦ by_contra fun hw0 ↦
    (e.snd_apply_ne_zero_iff ℝ (hUe (hOU w hw))).2 (hψ0 w hw hw0) (h.trans hF0)
  have hid : AntilipschitzWith 1 (ContinuousLinearMap.id ℝ P) := by
    simpa using AntilipschitzWith.id (α := P)
  have key := TopPair.singularCohomologyMap_ofSubsetMap_eq_affine_of_hasFDerivAt R k M
    (hO.mem_nhds hO0) hFc hF hid hFx n
  let j := TopPair.ofSubsetMap (X := TopCat.of P) (𝟙 _) (B := {F 0}ᶜ) (B' := {0}ᶜ)
    (by rw [hF0]; exact mapsTo_id _)
  have hfc : e.fiberCoordPairMap (hUe (mem_of_mem_nhds hU)) ψ (fun q ↦ hUe (hψU q)) ≫ τ₂.hom =
      TopPair.ofSubsetMap (X := TopCat.of O) (Y := TopCat.of P)
        (TopCat.ofHom ⟨O.domRestrict F, hFc.domRestrict⟩) (B := {⟨0, hO0⟩}ᶜ) (B' := {F 0}ᶜ)
        (fun y hy h ↦ hy (Subtype.ext (hFx y y.property h))) ≫ j := by
    refine TopPair.hom_ext_of_fst _ (ConcreteCategory.hom_ext _ _ fun w ↦ ?_)
    rw [TopPair.Hom.fst_comp, TopPair.Hom.fst_comp, ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply, Trivialization.fiberCoordPairMap_fst_apply,
      TopPair.ofSubsetIso_hom]
    erw [TopPair.ofSubsetMap_fst_apply, TopPair.ofSubsetMap_fst_apply,
      TopPair.ofSubsetMap_fst_apply, TopPair.ofSubsetMap_fst_apply]
    exact ℓ.apply_symm_apply _
  have hRj : RO ≫ τ₂.hom =
      TopPair.ofSubsetMap (X := TopCat.of O) (Y := TopCat.of P)
        (TopCat.ofHom ⟨fun y : O ↦ F 0 + (ContinuousLinearMap.id ℝ P) (y - 0), by fun_prop⟩)
        (B := {⟨0, hO0⟩}ᶜ) (B' := {F 0}ᶜ)
        (fun y hy h ↦ hy (Subtype.ext <| sub_eq_zero.1 <| hid.injective <|
          (add_eq_left.1 h).trans (map_zero _).symm)) ≫ j := by
    refine TopPair.hom_ext_of_fst _ (ConcreteCategory.hom_ext _ _ fun w ↦ ?_)
    rw [TopPair.Hom.fst_comp, TopPair.Hom.fst_comp, ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply, TopPair.ofSubsetIso_hom]
    erw [TopPair.ofSubsetMap_fst_apply, TopPair.ofSubsetMap_fst_apply,
      TopPair.ofSubsetMap_fst_apply, TopPair.ofSubsetMap_fst_apply]
    simp only [hF0, ℓ, Trivialization.symmL_apply (R := ℝ) e hx, ConcreteCategory.hom_ofHom,
      ContinuousMap.coe_mk, ContinuousLinearEquiv.coe_toHomeomorph,
      Trivialization.continuousLinearEquivAt_apply, sub_zero, ContinuousLinearMap.id_apply,
      zero_add]
    exact congrArg Prod.snd (e.apply_mk_symm hx _)
  rw [hfc, hRj, TopPair.singularCohomologyMap_comp_apply, TopPair.singularCohomologyMap_comp_apply]
  exact ConcreteCategory.congr_hom key _

end LocalDegree

end TauCeti.SmoothEmbedding

end
