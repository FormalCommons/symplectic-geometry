/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.DualClass.Basic
public import SymplecticGeometry.AlgebraicTopology.Cohomology.Local.Restrict
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

The local-degree lemma (`singularCohomologyMap_slice_eq_of_hasFDerivAt`) compares the normal
slice of a normalized tube `Φ` at `x` with any map `g` from a neighbourhood `B` of `0` in `P`
into `X` which sends only `0` into `f(Z)`, sends it to `f x`, and whose derivative at `0`,
followed by the quotient onto the normal space, is the inverse of the preferred trivialization `e`
at `x`. Both pull classes of `(X, X ∖ f(Z))` back in the same way, in every degree, once the
slice is read on `B` through `e`. On a small enough open `O ⊆ B` (restriction to which is
injective by excision), `g` lifts through `Φ` to a map into the Thom pair whose base points stay
in a contractible neighbourhood of `x`; this lift pulls classes back through its fibre coordinate
in `e` (`TauCeti.singularCohomologyMap_eq_singularCohomologyMap_fiberCoordPairMap`). Since `Φ`
is normalized, that fibre coordinate has derivative the identity at `0`
(`TauCeti.SmoothEmbedding.IsNormalizedTube.hasFDerivAt_trivializationAt_snd`), so it agrees on
relative cohomology with the inclusion of `O`
(`TopPair.singularCohomologyMap_ofSubsetMap_eq_inclusion_of_hasFDerivAt_id`). This follows the
linearization argument of Tau Ceti's
`TauCeti.VectorBundleOrientation.sectionIndex_eq_sign_det_of_hasFDerivAt`, which
compares a map with its derivative on a small ball around a zero.

## Main definitions

* `TauCeti.SmoothEmbedding.normalSlice`: the normal slice of a tube at a point, as a map of pairs.

## Main results

* `TauCeti.SmoothEmbedding.singularCohomologyMap_excisionMap_eq_iff_forall_normalSlice`: for any
  tube, a class of degree `r` restricts to the image of `u` exactly when its slices are the fibre
  restrictions of `u`.
* `TauCeti.SmoothEmbedding.eq_relDualClassOf_iff_forall_slice`: the same characterization of
  `relDualClassOf f hn hdim hf u`, through the normalized tube that defines it.
* `TauCeti.SmoothEmbedding.singularCohomologyMap_slice_eq_of_hasFDerivAt`: the local-degree
  lemma: a map with the derivative of a normal slice at `0` pulls classes back as the slice does.

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

/-- The local-degree lemma on a small open neighbourhood `O` of `0`, on which `g` lands in the image
`W` of the tube, over a contractible subset `U` of the base set of the preferred trivialization
at `x`. Here `Ψ` is an inverse of the tube on `W`. -/
private theorem singularCohomologyMap_slice_eq_of_isOpen {f : SmoothEmbedding I J ∞ Z X}
    {hn : (∞ : ℕ∞ω) ≠ 0} {hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E}
    {W : TopologicalSpace.Opens X}
    {Φ : letI := f.normalSpaceFiberBundle hn hdim
      TotalSpace P (fun x ↦ f.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W}
    (hΦ : f.IsNormalizedTube hn hdim Φ) (x : Z) {O : Set P} (hO : IsOpen O) (hO0 : (0 : P) ∈ O)
    {g : P → X} (hgO : ContinuousOn g O) (hgf : ∀ w ∈ O, g w ∈ range f → w = 0)
    {A : P →L[ℝ] V} (hg : HasMFDerivAt 𝓘(ℝ, P) J g 0 A)
    (hA : letI := f.normalSpaceFiberBundle hn hdim
      haveI := f.normalSpaceVectorBundle hn hdim
      ∀ w : P, f.normalClassL x hn (A w) =
        (trivializationAt P (fun x ↦ f.NormalSpace x hn) x).symmL ℝ x w)
    {Ψ : X → TotalSpace P (fun x ↦ f.NormalSpace x hn)} (hΨc : ContinuousOn Ψ W)
    (hΦΨ : ∀ {y : X}, y ∈ W → (Φ (Ψ y) : X) = y)
    (hΨ0 : Ψ (g 0) = zeroSection P (fun x ↦ f.NormalSpace x hn) x) {U : Set Z}
    [ContractibleSpace U] (hUe : letI := f.normalSpaceFiberBundle hn hdim
      U ⊆ (trivializationAt P (fun x ↦ f.NormalSpace x hn) x).baseSet)
    (hOW : ∀ w ∈ O, g w ∈ W) (hOU : ∀ w ∈ O, (Ψ (g w)).proj ∈ U)
    {n : ℕ} (c : (TopPair.ofSubset (X := TopCat.of X) (range f)ᶜ).singularCohomology R k M n) :
    letI := f.normalSpaceFiberBundle hn hdim
    haveI := f.normalSpaceVectorBundle hn hdim
    TopPair.singularCohomologyMap
        (TopPair.ofSubsetMap (X := TopCat.of O) (Y := TopCat.of X)
          (TopCat.ofHom ⟨O.domRestrict g, hgO.domRestrict⟩)
          (B := {⟨0, hO0⟩}ᶜ) (B' := (range f)ᶜ)
          fun w hw h ↦ hw (Subtype.ext (hgf w w.property h))) n c =
      TopPair.singularCohomologyMap
        (TopPair.ofSubsetMap (X := TopCat.of O) (Y := TopCat.of P)
          (TopCat.ofHom (ContinuousMap.subtypeVal O)) (B := {⟨0, hO0⟩}ᶜ) (B' := {0}ᶜ)
          (fun _ hw h ↦ hw (Subtype.ext (Set.mem_singleton_iff.1 h))) ≫
          ((trivializationAt P (fun x ↦ f.NormalSpace x hn) x).continuousLinearEquivAt ℝ x
            (mem_baseSet_trivializationAt P _ x)).symm.complZeroPairIso.hom) n
        (TopPair.singularCohomologyMap (f.normalSlice hn hdim Φ hΦ.apply_zeroSection x) n c) := by
  let := f.normalSpaceFiberBundle hn hdim
  have := f.normalSpaceVectorBundle hn hdim
  set e := trivializationAt P (fun x ↦ f.NormalSpace x hn) x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt P _ x
  have hxU : x ∈ U := by simpa [hΨ0] using hOU 0 hO0
  have hΨg : ContinuousAt (fun w ↦ Ψ (g w)) 0 :=
    (hΨc.comp hgO hOW).continuousAt (hO.mem_nhds hO0)
  set LO := TopPair.ofSubsetMap (X := TopCat.of O) (Y := TopCat.of X)
    (TopCat.ofHom ⟨O.domRestrict g, hgO.domRestrict⟩) (B := {⟨0, hO0⟩}ᶜ)
    (B' := (range f)ᶜ) fun w hw h ↦ hw (Subtype.ext (hgf w w.property h))
  -- Off `0`, the inverse of the tube does not meet the zero section along `g`.
  have hψ0 : ∀ w ∈ O, w ≠ 0 → (Ψ (g w)).snd ≠ 0 := by
    intro w hw hw0 hs
    have hr : Ψ (g w) ∈ range (zeroSection P (fun x ↦ f.NormalSpace x hn)) := by
      by_contra h
      rw [← mem_compl_iff, ← zeroSectionCompl_eq_compl_range, mem_zeroSectionCompl] at h
      exact h hs
    obtain ⟨z, hz⟩ := hr
    refine hw0 (hgf w hw ⟨z, ?_⟩)
    rw [← hΦΨ (hOW w hw), ← hz, hΦ.apply_zeroSection]
  -- On `O`, the map `g` factors through the inverse of the tube.
  let ψ : TopPair.ofSubset (X := TopCat.of O) ({⟨0, hO0⟩}ᶜ) ⟶
      thomPair P (fun x ↦ f.NormalSpace x hn) :=
    TopPair.ofSubsetMap (X := TopCat.of O)
      (Y := TopCat.of (TotalSpace P (fun x ↦ f.NormalSpace x hn)))
      (TopCat.ofHom ⟨O.domRestrict (Ψ ∘ g), (hΨc.comp hgO hOW).domRestrict⟩)
      (B := {⟨0, hO0⟩}ᶜ) (B' := zeroSectionCompl P _)
      fun w hw ↦ mem_zeroSectionCompl.2 (hψ0 w w.property fun h ↦ hw (Subtype.ext h))
  have hψ (w : O) : TopPair.Hom.fst ψ w = Ψ (g w) :=
    TopPair.ofSubsetMap_fst_apply (X := TopCat.of O) (B := {⟨0, hO0⟩}ᶜ) _ _ w
  have hψU (w : O) : (TopPair.Hom.fst ψ w).proj ∈ U := hψ w ▸ hOU w w.property
  have hLψ : LO = ψ ≫ (f.tubePairIso hn hdim Φ hΦ.apply_zeroSection).hom ≫
      TopPair.excisionMap (X := TopCat.of X) (W : Set X) (range f)ᶜ := by
    refine TopPair.hom_ext_of_fst _ (ConcreteCategory.hom_ext _ _ fun w ↦ ?_)
    rw [TopPair.Hom.fst_comp, TopPair.Hom.fst_comp, ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply]
    erw [TopPair.excisionMap_fst_apply, TopPair.ofSubsetMap_fst_apply,
      TopPair.ofSubsetMap_fst_apply]
    exact (hΦΨ (hOW _ (show O from w).property)).symm.trans
      (congrArg Subtype.val (tubePairIso_hom_fst_apply f hn hdim Φ _ _).symm)
  rw [hLψ, TopPair.singularCohomologyMap_comp_apply,
    singularCohomologyMap_eq_singularCohomologyMap_fiberCoordPairMap e (U := U) hUe hxU ψ hψU,
    normalSlice_def]
  simp only [TopPair.singularCohomologyMap_comp_apply]
  generalize TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
    (fiberThomPairMap P (fun x ↦ f.NormalSpace x hn) x) n _ = d
  -- Read in `e`, the fibre over `x` is `P`.
  set ℓ := e.continuousLinearEquivAt ℝ x hx
  obtain ⟨d, rfl⟩ : ∃ d', d = TopPair.singularCohomologyMap ℓ.complZeroPairIso.hom n d' :=
    ⟨_, by rw [← TopPair.singularCohomologyMap_comp_apply, Iso.hom_inv_id,
      TopPair.singularCohomologyMap_id, ConcreteCategory.id_apply]⟩
  rw [ContinuousLinearEquiv.complZeroPairIso_symm, Iso.symm_hom,
    ← TopPair.singularCohomologyMap_comp_apply ℓ.complZeroPairIso.inv, Iso.inv_hom_id,
    TopPair.singularCohomologyMap_id, ConcreteCategory.id_apply,
    ← TopPair.singularCohomologyMap_comp_apply, e.fiberCoordPairMap_comp_complZeroPairIso_hom]
  -- The fibre coordinate of `g` has derivative the identity at `0`.
  set F : P → P := fun w ↦ (e (Ψ (g w))).2
  have hFc : ContinuousOn F O := (e.continuousOn.comp (hΨc.comp hgO hOW)
    fun w hw ↦ e.mem_source.2 (hUe (hOU w hw))).snd
  have hF0 : F 0 = 0 := by simp [F, hΨ0, e.zeroSection ℝ hx]
  have hF : HasFDerivAt F (ContinuousLinearMap.id ℝ P) 0 :=
    hΦ.hasFDerivAt_trivializationAt_snd hg hA hΨg hΨ0
      (by filter_upwards [hO.mem_nhds hO0] with w hw using hΦΨ (hOW w hw))
  have hFx : ∀ w ∈ O, F w = 0 → w = 0 := fun w hw h ↦ by_contra fun hw0 ↦
    (e.snd_apply_ne_zero_iff ℝ (hUe (hOU w hw))).2 (hψ0 w hw hw0) h
  have hfc : (TopPair.isoOfSubsetRange _).hom ≫ TopPair.ofSubsetMap
      (TopCat.ofHom ⟨fun q ↦ (e (TopPair.Hom.fst ψ q)).2,
        (e.continuousOn.comp_continuous (TopPair.Hom.fst ψ).hom.continuous
          fun q ↦ e.mem_source.2 (hUe (hψU q))).snd⟩)
      (fun q hq ↦ (e.snd_apply_ne_zero_iff ℝ (hUe (hψU q))).2 <|
        mem_zeroSectionCompl.1 (TopPair.mapsTo_range_map_of_hom ψ hq)) =
      TopPair.ofSubsetMap (X := TopCat.of O) (Y := TopCat.of P)
        (TopCat.ofHom ⟨O.domRestrict F, hFc.domRestrict⟩) (B := {⟨0, hO0⟩}ᶜ) (B' := {0}ᶜ)
        (fun y hy h ↦ hy (Subtype.ext (hFx y y.property h))) := by
    refine TopPair.hom_ext_of_fst _ (ConcreteCategory.hom_ext _ _ fun w ↦ ?_)
    rw [TopPair.Hom.fst_comp, ConcreteCategory.comp_apply,
      TopPair.isoOfSubsetRange_hom_fst_apply]
    -- The points of the pairs are those of `O` and `P` only up to unfolding `ofSubset`.
    erw [TopPair.ofSubsetMap_fst_apply, TopPair.ofSubsetMap_fst_apply]
    exact congrArg (fun p ↦ (e p).2) (hψ w)
  rw [hfc, TopPair.singularCohomologyMap_ofSubsetMap_eq_inclusion_of_hasFDerivAt_id R k M
    (hO.mem_nhds hO0) hFc hF0 hF hFx n]

/-- **The local-degree lemma.** Let `Φ` be a normalized tube of `f`, `x : Z`, and `e` the preferred
trivialization of the normal bundle at `x`. Let `B ⊆ P` be a neighbourhood of `0` and `g : P → X`
a map continuous on `B`, with `g 0 = f x`, sending no other point of `B` into `f(Z)`, and
differentiable at `0` with a derivative `A` such that the normal class of each `A w` is the vector
of the fibre over `x` with coordinate `w` in `e`. Then `g`, as a map of pairs
`(B, B ∖ {0}) ⟶ (X, X ∖ f(Z))`, pulls every class back as the normal slice of `Φ` at `x` does,
after `w ↦ e.symm x w`: the inclusion `(B, B ∖ {0}) ⟶ (P, P ∖ {0})` followed by the pair
isomorphism `(P, P ∖ {0}) ≅ (ν_x, ν_x ∖ {0})` of the inverse of `e` on the fibre over `x`. -/
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
        (TopPair.ofSubsetMap (X := TopCat.of B) (Y := TopCat.of P)
          (TopCat.ofHom (ContinuousMap.subtypeVal B)) (B := {⟨0, mem_of_mem_nhds hB⟩}ᶜ)
          (B' := {0}ᶜ) (fun _ hw h ↦ hw (Subtype.ext (Set.mem_singleton_iff.1 h))) ≫
          ((trivializationAt P (fun x ↦ f.NormalSpace x hn) x).continuousLinearEquivAt ℝ x
            (mem_baseSet_trivializationAt P _ x)).symm.complZeroPairIso.hom) n
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
  obtain ⟨U, ⟨hU, hUc⟩, hUe : U ⊆ e.baseSet⟩ :=
    (contractible_basis x).mem_iff.1 (e.open_baseSet.mem_nhds hx)
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
  -- Restriction from `B` to `O` is injective on cohomology.
  have := TopPair.isIso_singularCohomologyMap_ofSubsetMap_inclusion R k M hO hOB hO0 n
  refine (ConcreteCategory.injective_of_mono_of_preservesPullback _ :
    Function.Injective (ConcreteCategory.hom (TopPair.singularCohomologyMap (R := R) (k := k)
      (M := M) (TopPair.ofSubsetMap (X := TopCat.of O) (Y := TopCat.of B)
        (TopCat.ofHom ⟨Set.inclusion hOB, continuous_inclusion hOB⟩)
        (B := {⟨0, hO0⟩}ᶜ) (B' := {⟨0, hOB hO0⟩}ᶜ)
        fun _ hw h ↦ hw (Set.inclusion_injective hOB h)) n))) ?_
  rw [← TopPair.singularCohomologyMap_comp_apply, ← TopPair.singularCohomologyMap_comp_apply,
    ← Category.assoc]
  convert singularCohomologyMap_slice_eq_of_isOpen hΦ x hO hO0 (hgB.mono hOB)
    (fun w hw ↦ hgf w (hOB hw)) hg hA hΨc hΦΨ hΨ0 hUe hOW hOU c using 4
  · exact TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ _ rfl
  · congr 1
    exact TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ _ rfl

end LocalDegree

end TauCeti.SmoothEmbedding

end
