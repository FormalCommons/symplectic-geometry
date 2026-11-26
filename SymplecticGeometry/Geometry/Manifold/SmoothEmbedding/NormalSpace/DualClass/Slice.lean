/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.DualClass.Basic
public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.ThomPairMap
public import SymplecticGeometry.AlgebraicTopology.Cohomology.Local.Restrict
public import SymplecticGeometry.AlgebraicTopology.Cohomology.Local.Derivative
public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.Diffeomorph
public import SymplecticGeometry.Topology.VectorBundle.Thom.FiberCoordinate
public import TauCeti.Geometry.Manifold.LocallyContractible
public import TauCeti.Topology.VectorBundle.MayerVietoris.DirectedUnion
public import TauCeti.Topology.VectorBundle.Thom.FiberwiseEquiv
import SymplecticGeometry.Geometry.Manifold.IsManifold.Basic

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
(`singularCohomologyMap_excisionMap_eq_iff_forall_normalSlice`). No condition on `u`, such as
being a Thom class, is needed; the degree must be the rank `r`, the degree in which Tau
Ceti's uniqueness by fibre restrictions holds.

The local-degree lemma (`singularCohomologyMap_slice_eq_of_hasFDerivAt`) compares the normal
slice of a normalized tube `Φ` at `x` with any map `g` from a neighbourhood `B` of `0` in `P`
into `X` which sends only `0` into `f(Z)`, sends it to `f x`, and whose derivative at `0`,
followed by the quotient onto the normal space, is the inverse of the preferred trivialization `e`
at `x`. Both pull classes of `(X, X ∖ f(Z))` back in the same way, in every degree, once the
slice is read on `B` through `e`. On a small enough open `O ⊆ B` (restriction to which is
injective by excision), `g` lifts through `Φ` to a map into the Thom pair whose base points stay
in a contractible neighbourhood of `x`; this lift pulls classes back, through
`(e.continuousLinearEquivAt ℝ x hx).complZeroPairIso.inv`, along its coordinate in the model
fibre (`Bundle.Trivialization.coordPairMap`,
`TauCeti.singularCohomologyMap_eq_singularCohomologyMap_complZeroPairIso_inv`). Since `Φ` is
normalized, that coordinate has derivative the identity at `0`
(`TauCeti.SmoothEmbedding.IsNormalizedTube.hasFDerivAt_trivializationAt_snd`), so it agrees on
relative cohomology with the inclusion of `O`
(`TopPair.singularCohomologyMap_ofSubsetMap_eq_inclusion_of_hasFDerivAt_id`). This follows the
linearization argument of Tau Ceti's
`TauCeti.VectorBundleOrientation.sectionIndex_eq_sign_det_of_hasFDerivAt`, which
compares a map with its derivative on a small ball around a zero.

For `u` in the degree `r` of the rank, with coefficients `R, M : ModuleCat k` and `R` projective
over `k`, the class does not depend on the normalized tube. For two normalized tubes `Φ`
and `Φ'` and a point `x`, the map `w ↦ Φ'(x, e⁻¹ w)` on `P` has, by normalization of `Φ'`, the
derivative that the local-degree lemma asks for (`IsNormalizedTube.exists_hasMFDerivAt_apply_mk`,
which reads a normal slice of a normalized tube through any linear isomorphism `P ≃ ν_x`), so the
lemma applied to `Φ` and to `Φ'` shows that their normal slices at `x` pull classes back alike
(`singularCohomologyMap_normalSlice_eq_of_isNormalizedTube`). By the slice criterion, every
normalized tube then carries `relDualClassOf f hn hdim hf u` for `u` of degree `r`
(`singularCohomologyMap_excisionMap_relDualClassOf`, `relDualClassOf_eq_of_isNormalizedTube`), so
that `c = relDualClassOf f hn hdim hf u` exactly when the slices of `c` along any normalized tube
are the fibre restrictions of `u` (`eq_relDualClassOf_iff_forall_slice`).

For a diffeomorphism `φ : X' ≃ X` and the embedding `f' = φ⁻¹ ∘ f`
(`f.transDiffeomorph φ.symm`), the triangle `φ ∘ f' = f` (`comp_transDiffeomorph_symm`) has an
ambient map with invertible derivative, so `NormalSpace/ThomPairMap.lean` gives the isomorphism
of the normal spaces of `f'` with those of `f` by the derivative of `φ`
(`transDiffeomorphNormalSpaceEquiv`, from `normalSpaceEquivOfComp`) and the map of Thom pairs
`(ν_{f'}, ν_{f'} ∖ 0) ⟶ (ν_f, ν_f ∖ 0)` that it induces (`transDiffeomorphThomPairMap`, from
`thomPairMapOfComp`), which on the fibre over `x` is the isomorphism of fibre pairs of the
equivalence at `x` (`fiberThomPairMap_comp_transDiffeomorphThomPairMap`).

The dual classes are natural under `φ`. Write `u'` for the pull-back of a class `u` of degree `r`
along `transDiffeomorphThomPairMap`, and `ℓ` for the isomorphism `ν_{f'} x ≃ ν_f x` at `x`. For
normalized tubes `Φ` of `f` and `Φ'` of `f'`, the map `w ↦ φ (Φ'(x, ℓ⁻¹ (e⁻¹ w)))` on `P`, with
`e` the preferred trivialization of `ν_f` at `x`, has by the chain rule, normalization of `Φ'`
and `transDiffeomorphNormalSpaceEquiv_normalClass` the derivative at `0` that the local-degree
lemma asks for. So the normal slice of `Φ'` followed by `φ` pulls classes back as `ℓ` followed
by the normal slice of `Φ` (`singularCohomologyMap_normalSlice_transDiffeomorph`). With the
fibre restrictions of `transDiffeomorphThomPairMap`, the slice criterion then gives that the
relative class of `f'` and `u'` is the pull-back of that of `f` and `u` along
`φ : (X', X' ∖ f'(Z)) ⟶ (X, X ∖ f(Z))` (`relDualClassOf_transDiffeomorph`), and the same for the
absolute classes (`dualClassOf_transDiffeomorph`).

For a normal orientation `o` of `f`, the map of Thom pairs `transDiffeomorphThomPairMap` pulls the
canonical Thom class of `o` back to that of the orientation `o.comap` transported along the
derivative of `φ` (`singularCohomologyMap_thomPairMapOfFiberwise_canonicalThomClass_comap`). So
the oriented dual classes are natural too: the dual class of `f'` with the transported orientation
is the pull-back along `φ` of the dual class of `f` with `o` (`relDualClass_transDiffeomorph`,
`dualClass_transDiffeomorph`).

## Main definitions

* `TauCeti.SmoothEmbedding.normalSlice`: the normal slice of a tube at a point, as a map of pairs.
* `TauCeti.SmoothEmbedding.transDiffeomorphNormalSpaceEquiv`,
  `TauCeti.SmoothEmbedding.transDiffeomorphThomPairMap`: for a diffeomorphism `φ : X' ≃ X`,
  the identification of the normal spaces of `φ⁻¹ ∘ f` with those of `f` by the derivative of
  `φ`, and the map of Thom pairs of normal bundles that it induces.

## Main results

* `TauCeti.SmoothEmbedding.singularCohomologyMap_excisionMap_eq_iff_forall_normalSlice`: for any
  tube, a class of degree `r` restricts to the image of `u` exactly when its slices are the fibre
  restrictions of `u`.
* `TauCeti.SmoothEmbedding.singularCohomologyMap_slice_eq_of_hasFDerivAt`: the local-degree
  lemma: a map with the derivative of a normal slice at `0` pulls classes back as the slice does.
* `TauCeti.SmoothEmbedding.singularCohomologyMap_normalSlice_eq_of_isNormalizedTube`: the normal
  slices of two normalized tubes at a point pull classes back alike.
* `TauCeti.SmoothEmbedding.relDualClassOf_eq_of_isNormalizedTube`,
  `TauCeti.SmoothEmbedding.singularCohomologyMap_excisionMap_relDualClassOf`: independence of the
  tube: for `u` of degree `r`, with coefficients `R, M : ModuleCat k` and `R` projective over `k`,
  every normalized tube carries `relDualClassOf f hn hdim hf u`.
* `TauCeti.SmoothEmbedding.eq_relDualClassOf_iff_forall_slice`: for `u` of degree `r`, a class
  is `relDualClassOf f hn hdim hf u` exactly when its slices along a normalized tube are the
  fibre restrictions of `u`.
* `TauCeti.SmoothEmbedding.fiberThomPairMap_comp_transDiffeomorphThomPairMap`: on the fibre over
  `x`, the map of Thom pairs under a diffeomorphism is the fibre-pair isomorphism of the
  derivative.
* `TauCeti.SmoothEmbedding.singularCohomologyMap_normalSlice_transDiffeomorph`: under a
  diffeomorphism `φ`, the normal slice of a normalized tube of `φ⁻¹ ∘ f` followed by `φ` pulls
  classes back as the derivative of `φ` followed by the normal slice of a normalized tube of `f`.
* `TauCeti.SmoothEmbedding.relDualClassOf_transDiffeomorph`,
  `TauCeti.SmoothEmbedding.dualClassOf_transDiffeomorph`: naturality of the relative and
  absolute classes under a diffeomorphism, for `u` of degree `r`.
* `TauCeti.SmoothEmbedding.relDualClass_transDiffeomorph`,
  `TauCeti.SmoothEmbedding.dualClass_transDiffeomorph`: naturality of the relative and absolute
  dual classes of a normally oriented embedding under a diffeomorphism, with the normal
  orientation transported by the derivative.

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
      TotalSpace P (fun x ↦ f.isImmersion.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W)
    (hΦ : letI := f.normalSpaceFiberBundle hn hdim
      ∀ x, (Φ (zeroSection P _ x) : X) = f x) (x : Z) :
    TopPair.ofSubset (X := TopCat.of (f.isImmersion.NormalSpace x hn))
        ({0}ᶜ : Set (f.isImmersion.NormalSpace x hn)) ⟶
      TopPair.ofSubset (X := TopCat.of X) (range f)ᶜ :=
  letI := f.normalSpaceFiberBundle hn hdim
  fiberThomPairMap P (fun x ↦ f.isImmersion.NormalSpace x hn) x ≫ (f.tubePairIso hn hdim Φ hΦ).hom ≫
    TopPair.excisionMap (X := TopCat.of X) (W : Set X) (range f)ᶜ

/-- The normal slice of a tube factors through the fibre inclusion, the pair isomorphism of the
tube and excision. -/
theorem normalSlice_def (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) {W : TopologicalSpace.Opens X}
    (Φ : letI := f.normalSpaceFiberBundle hn hdim
      TotalSpace P (fun x ↦ f.isImmersion.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W)
    (hΦ : letI := f.normalSpaceFiberBundle hn hdim
      ∀ x, (Φ (zeroSection P _ x) : X) = f x) (x : Z) :
    letI := f.normalSpaceFiberBundle hn hdim
    f.normalSlice hn hdim Φ hΦ x =
      fiberThomPairMap P (fun x ↦ f.isImmersion.NormalSpace x hn) x ≫
          (f.tubePairIso hn hdim Φ hΦ).hom ≫
        TopPair.excisionMap (X := TopCat.of X) (W : Set X) (range f)ᶜ :=
  (rfl)

/-- On ambient spaces, the normal slice of a tube at `x` sends `v` to `Φ(x, v)`. -/
@[simp]
theorem normalSlice_fst_apply (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) {W : TopologicalSpace.Opens X}
    (Φ : letI := f.normalSpaceFiberBundle hn hdim
      TotalSpace P (fun x ↦ f.isImmersion.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W)
    (hΦ : letI := f.normalSpaceFiberBundle hn hdim
      ∀ x, (Φ (zeroSection P _ x) : X) = f x) (x : Z) (v : f.isImmersion.NormalSpace x hn) :
    TopPair.Hom.fst (f.normalSlice hn hdim Φ hΦ x) v =
      (Φ (TotalSpace.mk' P x v) : X) := by
  let := f.normalSpaceFiberBundle hn hdim
  rw [normalSlice_def, TopPair.Hom.fst_comp, TopPair.Hom.fst_comp]
  refine (ConcreteCategory.comp_apply (X := TopCat.of (f.isImmersion.NormalSpace x hn)) _ _ v).trans
      ?_
  rw [ConcreteCategory.comp_apply]
  exact (tubePairIso_hom_fst_comp_excisionMap_fst_apply f hn hdim Φ hΦ _).trans
    (congrArg (fun v ↦ (Φ v : X)) (fiberThomPairMap_fst_apply P
        (fun x ↦ f.isImmersion.NormalSpace x hn) x v))

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
      TotalSpace P (fun x ↦ f.isImmersion.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W)
    (hΦ : letI := f.normalSpaceFiberBundle hn hdim
      ∀ x, (Φ (zeroSection P _ x) : X) = f x)
    (u : letI := f.normalSpaceFiberBundle hn hdim
      (thomPair P (fun x ↦ f.isImmersion.NormalSpace x hn)).singularCohomology R k M (finrank ℝ P))
    (c : (TopPair.ofSubset (X := TopCat.of X) (range f)ᶜ).singularCohomology R k M
      (finrank ℝ P)) :
    letI := f.normalSpaceFiberBundle hn hdim
    TopPair.singularCohomologyMap (TopPair.excisionMap (X := TopCat.of X) (W : Set X) (range f)ᶜ)
        _ c = TopPair.singularCohomologyMap (f.tubePairIso hn hdim Φ hΦ).inv _ u ↔
      ∀ x, TopPair.singularCohomologyMap (f.normalSlice hn hdim Φ hΦ x) _ c =
        TopPair.singularCohomologyMap (fiberThomPairMap P (fun x ↦ f.isImmersion.NormalSpace x hn)
            x) _ u := by
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  set t := f.tubePairIso hn hdim Φ hΦ
  set e := TopPair.excisionMap (X := TopCat.of X) (W : Set X) (range f)ᶜ
  have hslice (x : Z) : TopPair.singularCohomologyMap (f.normalSlice hn hdim Φ hΦ x) _ c =
      TopPair.singularCohomologyMap (fiberThomPairMap P (fun x ↦ f.isImmersion.NormalSpace x hn) x)
          _
        (TopPair.singularCohomologyMap t.hom _ (TopPair.singularCohomologyMap e _ c)) := by
    rw [normalSlice_def, TopPair.singularCohomologyMap_comp_apply,
      TopPair.singularCohomologyMap_comp_apply]
  simp only [hslice]
  have hu := (TopPair.singularCohomologyMapIso R k M t (finrank ℝ P)).inv_hom_id_apply u
  have hc := (TopPair.singularCohomologyMapIso R k M t (finrank ℝ P)).hom_inv_id_apply
  rw [TopPair.singularCohomologyMapIso_hom, TopPair.singularCohomologyMapIso_inv] at hu hc
  refine ⟨fun h x ↦ by rw [h, hu], fun h ↦ ?_⟩
  rw [← singularCohomology_thomPair_ext h, hc]

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
      TotalSpace P (fun x ↦ f.isImmersion.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W}
    (hΦ : f.IsNormalizedTube hn hdim Φ) (x : Z) {O : Set P} (hO : IsOpen O) (hO0 : (0 : P) ∈ O)
    {g : P → X} (hgO : ContinuousOn g O) (hgf : ∀ w ∈ O, g w ∈ range f → w = 0)
    {A : P →L[ℝ] V} (hg : HasMFDerivAt 𝓘(ℝ, P) J g 0 A)
    (hA : letI := f.normalSpaceFiberBundle hn hdim
      haveI := f.normalSpaceVectorBundle hn hdim
      ∀ w : P, f.isImmersion.normalClassL x hn (A w) =
        (trivializationAt P (fun x ↦ f.isImmersion.NormalSpace x hn) x).symmL ℝ x w)
    {Ψ : X → TotalSpace P (fun x ↦ f.isImmersion.NormalSpace x hn)} (hΨc : ContinuousOn Ψ W)
    (hΦΨ : ∀ {y : X}, y ∈ W → (Φ (Ψ y) : X) = y)
    (hΨ0 : Ψ (g 0) = zeroSection P (fun x ↦ f.isImmersion.NormalSpace x hn) x) {U : Set Z}
    [ContractibleSpace U] (hUe : letI := f.normalSpaceFiberBundle hn hdim
      U ⊆ (trivializationAt P (fun x ↦ f.isImmersion.NormalSpace x hn) x).baseSet)
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
          ((trivializationAt P (fun x ↦ f.isImmersion.NormalSpace x hn) x).continuousLinearEquivAt ℝ
              x
            (mem_baseSet_trivializationAt P _ x)).symm.complZeroPairIso.hom) n
        (TopPair.singularCohomologyMap (f.normalSlice hn hdim Φ hΦ.apply_zeroSection x) n c) := by
  let := f.normalSpaceFiberBundle hn hdim
  have := f.normalSpaceVectorBundle hn hdim
  set e := trivializationAt P (fun x ↦ f.isImmersion.NormalSpace x hn) x
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
    have hr : Ψ (g w) ∈ range (zeroSection P (fun x ↦ f.isImmersion.NormalSpace x hn)) := by
      by_contra h
      rw [← mem_compl_iff, ← zeroSectionCompl_eq_compl_range, mem_zeroSectionCompl] at h
      exact h hs
    refine hw0 (hgf w hw ?_)
    rw [← hΦΨ (hOW w hw)]
    exact (apply_mem_range_iff_of_apply_zeroSection f hn hdim Φ hΦ.apply_zeroSection _).2 hr
  -- On `O`, the map `g` factors through the inverse of the tube.
  let ψ : TopPair.ofSubset (X := TopCat.of O) ({⟨0, hO0⟩}ᶜ) ⟶
      thomPair P (fun x ↦ f.isImmersion.NormalSpace x hn) :=
    TopPair.ofSubsetMap (X := TopCat.of O)
      (Y := TopCat.of (TotalSpace P (fun x ↦ f.isImmersion.NormalSpace x hn)))
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
    refine Eq.trans ?_ (tubePairIso_hom_fst_comp_excisionMap_fst_apply f hn hdim Φ _ _).symm
    erw [TopPair.ofSubsetMap_fst_apply, hψ]
    exact (hΦΨ (hOW _ (show O from w).property)).symm
  rw [hLψ, TopPair.singularCohomologyMap_comp_apply,
    singularCohomologyMap_eq_singularCohomologyMap_complZeroPairIso_inv e (U := U) hUe hxU ψ hψU,
    normalSlice_def, ContinuousLinearEquiv.complZeroPairIso_symm, Iso.symm_hom]
  simp only [TopPair.singularCohomologyMap_comp_apply]
  generalize TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
    (e.continuousLinearEquivAt ℝ x hx).complZeroPairIso.inv n _ = d
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
  have hfc : e.coordPairMap ψ (fun q ↦ hUe (hψU q)) =
      TopPair.ofSubsetMap (X := TopCat.of O) (Y := TopCat.of P)
        (TopCat.ofHom ⟨O.domRestrict F, hFc.domRestrict⟩) (B := {⟨0, hO0⟩}ᶜ) (B' := {0}ᶜ)
        (fun y hy h ↦ hy (Subtype.ext (hFx y y.property h))) := by
    refine TopPair.hom_ext_of_fst _ (ConcreteCategory.hom_ext _ _ fun w ↦ ?_)
    rw [Trivialization.coordPairMap_fst_apply]
    -- The points of the pair are those of `O` only up to unfolding `ofSubset`.
    erw [TopPair.ofSubsetMap_fst_apply (X := TopCat.of O) (Y := TopCat.of P)]
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
      TotalSpace P (fun x ↦ f.isImmersion.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W}
    (hΦ : f.IsNormalizedTube hn hdim Φ) (x : Z) {B : Set P} (hB : B ∈ 𝓝 0) {g : P → X}
    (hgB : ContinuousOn g B) (hg0 : g 0 = f x) (hgf : ∀ w ∈ B, g w ∈ range f → w = 0)
    {A : P →L[ℝ] V} (hg : HasMFDerivAt 𝓘(ℝ, P) J g 0 A)
    (hA : letI := f.normalSpaceFiberBundle hn hdim
      haveI := f.normalSpaceVectorBundle hn hdim
      ∀ w : P, f.isImmersion.normalClassL x hn (A w) =
        (trivializationAt P (fun x ↦ f.isImmersion.NormalSpace x hn) x).symmL ℝ x w)
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
          ((trivializationAt P (fun x ↦ f.isImmersion.NormalSpace x hn) x).continuousLinearEquivAt ℝ
              x
            (mem_baseSet_trivializationAt P _ x)).symm.complZeroPairIso.hom) n
        (TopPair.singularCohomologyMap (f.normalSlice hn hdim Φ hΦ.apply_zeroSection x) n c) := by
  let := f.normalSpaceFiberBundle hn hdim
  have := f.normalSpaceVectorBundle hn hdim
  classical
  set e := trivializationAt P (fun x ↦ f.isImmersion.NormalSpace x hn) x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt P _ x
  have hfxW : f x ∈ W :=
    range_subset_of_apply_zeroSection f hn hdim Φ hΦ.apply_zeroSection (mem_range_self x)
  -- The inverse of the tube, extended by the zero vector over `x` off `W`.
  let Ψ : X → TotalSpace P (fun x ↦ f.isImmersion.NormalSpace x hn) := fun y ↦
    if hy : y ∈ W then Φ.symm ⟨y, hy⟩ else zeroSection P _ x
  have hΨ {y : X} (hy : y ∈ W) : Ψ y = Φ.symm ⟨y, hy⟩ := by simp [Ψ, hy]
  have hΨc : ContinuousOn Ψ W := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact Φ.symm.continuous.congr fun y ↦ (hΨ y.property).symm
  have hgW : g 0 ∈ W := hg0 ▸ hfxW
  have hΨ0 : Ψ (g 0) = zeroSection P _ x := by
    rw [hg0, hΨ hfxW]
    exact symm_apply_eq_zeroSection_of_apply_zeroSection f hn hdim Φ hΦ.apply_zeroSection x hfxW
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

/-- **The normal slices of two normalized tubes agree in cohomology.** For normalized tubes `Φ`
and `Φ'` of `f` and a point `x : Z`, the normal slices of `Φ` and of `Φ'` at `x` pull every class
of `(X, X ∖ f(Z))` back to the same class of `(ν_x, ν_x ∖ 0)`, in every degree. -/
theorem singularCohomologyMap_normalSlice_eq_of_isNormalizedTube {f : SmoothEmbedding I J ∞ Z X}
    {hn : (∞ : ℕ∞ω) ≠ 0} {hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E}
    {W W' : TopologicalSpace.Opens X}
    {Φ : letI := f.normalSpaceFiberBundle hn hdim
      TotalSpace P (fun x ↦ f.isImmersion.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W}
    {Φ' : letI := f.normalSpaceFiberBundle hn hdim
      TotalSpace P (fun x ↦ f.isImmersion.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W'}
    (hΦ : f.IsNormalizedTube hn hdim Φ) (hΦ' : f.IsNormalizedTube hn hdim Φ') (x : Z) {n : ℕ}
    (c : (TopPair.ofSubset (X := TopCat.of X) (range f)ᶜ).singularCohomology R k M n) :
    TopPair.singularCohomologyMap (f.normalSlice hn hdim Φ' hΦ'.apply_zeroSection x) n c =
      TopPair.singularCohomologyMap (f.normalSlice hn hdim Φ hΦ.apply_zeroSection x) n c := by
  let := f.normalSpaceFiberBundle hn hdim
  have := f.normalSpaceVectorBundle hn hdim
  set e := trivializationAt P (fun x ↦ f.isImmersion.NormalSpace x hn) x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt P _ x
  set ℓ := e.continuousLinearEquivAt ℝ x hx
  -- The map `w ↦ Φ'(x, ℓ⁻¹ w)` has the derivative that the local-degree lemma asks for.
  obtain ⟨hgc, hg0, hgf, A, hg, hA⟩ := hΦ'.exists_hasMFDerivAt_apply_mk x ℓ.symm
  have hA' (w : P) : f.isImmersion.normalClassL x hn (A w) = e.symmL ℝ x w := by
    rw [hA, ← e.symm_continuousLinearEquivAt_eq' hx, ContinuousLinearEquiv.coe_coe]
  have h1 := singularCohomologyMap_slice_eq_of_hasFDerivAt hΦ x Filter.univ_mem hgc.continuousOn
    hg0 (fun w _ ↦ hgf w) hg hA' c
  have h2 := singularCohomologyMap_slice_eq_of_hasFDerivAt hΦ' x Filter.univ_mem hgc.continuousOn
    hg0 (fun w _ ↦ hgf w) hg hA' c
  -- Both sides are read through the same isomorphism `(univ, univ ∖ {0}) ≅ (ν_x, ν_x ∖ 0)`.
  exact TopPair.injective_singularCohomologyMap_ofSubsetMap_subtypeVal_univ_comp R k M (0 : P)
    ℓ.symm.complZeroPairIso n (h2.symm.trans h1)

end LocalDegree

section Independence

variable {k : Type*} [CommRing k] {R M : ModuleCat.{w} k} [Module.Projective k R]
  [I.Boundaryless] [J.Boundaryless] [T2Space X] [SecondCountableTopology X]

/-- **Every normalized tube carries the relative dual class.** For every normalized tube `Φ` of
`f` onto an open set `W` and every class `u` of the Thom pair of the normal bundle in the degree
`r = finrank ℝ P` of its rank, with coefficients `R, M : ModuleCat k` and `R` projective over
`k`, the restriction of `relDualClassOf f hn hdim hf u` to `(W, W ∖ f(Z))` by excision is the
image of `u` under the pair isomorphism of `Φ`. -/
theorem singularCohomologyMap_excisionMap_relDualClassOf (f : SmoothEmbedding I J ∞ Z X)
    (hn : (∞ : ℕ∞ω) ≠ 0) (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    (hf : IsClosed (range f)) {W : TopologicalSpace.Opens X}
    {Φ : letI := f.normalSpaceFiberBundle hn hdim
      TotalSpace P (fun x ↦ f.isImmersion.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W}
    (hΦ : f.IsNormalizedTube hn hdim Φ)
    (u : letI := f.normalSpaceFiberBundle hn hdim
      (thomPair P (fun x ↦ f.isImmersion.NormalSpace x hn)).singularCohomology R k M
          (finrank ℝ P)) :
    TopPair.singularCohomologyMap (TopPair.excisionMap (X := TopCat.of X) (W : Set X) (range f)ᶜ)
        _ (f.relDualClassOf hn hdim hf u) =
      TopPair.singularCohomologyMap (f.tubePairIso hn hdim Φ hΦ.apply_zeroSection).inv _ u := by
  obtain ⟨W₀, Φ₀, hΦ₀, h⟩ :=
    exists_isNormalizedTube_singularCohomologyMap_excisionMap_relDualClassOf (R := R) (k := k)
      (M := M) f hn hdim hf
  rw [singularCohomologyMap_excisionMap_eq_iff_forall_normalSlice]
  intro x
  rw [singularCohomologyMap_normalSlice_eq_of_isNormalizedTube hΦ₀ hΦ]
  exact (singularCohomologyMap_excisionMap_eq_iff_forall_normalSlice f hn hdim Φ₀ _ u _).1
    (h _ u) x

/-- **The dual class does not depend on the tube.** Let `Φ` be any normalized tube of `f` onto an
open set `W`, and `u` a class of the Thom pair of the normal bundle in the degree
`r = finrank ℝ P` of its rank, with coefficients `R, M : ModuleCat k` and `R` projective over
`k`. A class `c ∈ Hʳ(X, X ∖ f(Z))` whose restriction to `(W, W ∖ f(Z))`
by excision is the image of `u` under the pair isomorphism of `Φ` is
`relDualClassOf f hn hdim hf u`. -/
theorem relDualClassOf_eq_of_isNormalizedTube (f : SmoothEmbedding I J ∞ Z X)
    (hn : (∞ : ℕ∞ω) ≠ 0) (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    (hf : IsClosed (range f)) {W : TopologicalSpace.Opens X}
    {Φ : letI := f.normalSpaceFiberBundle hn hdim
      TotalSpace P (fun x ↦ f.isImmersion.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W}
    (hΦ : f.IsNormalizedTube hn hdim Φ)
    {u : letI := f.normalSpaceFiberBundle hn hdim
      (thomPair P (fun x ↦ f.isImmersion.NormalSpace x hn)).singularCohomology R k M (finrank ℝ P)}
    {c : (TopPair.ofSubset (X := TopCat.of X) (range f)ᶜ).singularCohomology R k M
      (finrank ℝ P)}
    (hc : TopPair.singularCohomologyMap
        (TopPair.excisionMap (X := TopCat.of X) (W : Set X) (range f)ᶜ) _ c =
      TopPair.singularCohomologyMap (f.tubePairIso hn hdim Φ hΦ.apply_zeroSection).inv _ u) :
    f.relDualClassOf hn hdim hf u = c := by
  have := TopPair.isIso_singularCohomologyMap_excisionMap_of_isClosed_subset R k M
    (X := TopCat.of X) W.isOpen hf
    (range_subset_of_apply_zeroSection f hn hdim Φ hΦ.apply_zeroSection) (finrank ℝ P)
  refine ConcreteCategory.injective_of_mono_of_preservesPullback (TopPair.singularCohomologyMap
    (TopPair.excisionMap (X := TopCat.of X) (W : Set X) (range f)ᶜ) _) ?_
  rw [singularCohomologyMap_excisionMap_relDualClassOf f hn hdim hf hΦ, hc]

/-- **The relative class of a submanifold is determined by its normal slices.** Let `Φ` be any
normalized tube of `f` onto an open set `W`, and `u` a class of the Thom pair of the normal bundle
in the degree `r = finrank ℝ P` of its rank, with coefficients `R, M : ModuleCat k` and `R`
projective over `k`. A class `c ∈ Hʳ(X, X ∖ f(Z))` is `relDualClassOf f hn hdim hf u` exactly
when, at every `x : Z`, its pull-back along the normal slice of `Φ` at `x` is the restriction of
`u` to the fibre over `x`. -/
theorem eq_relDualClassOf_iff_forall_slice (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) (hf : IsClosed (range f))
    {W : TopologicalSpace.Opens X}
    {Φ : letI := f.normalSpaceFiberBundle hn hdim
      TotalSpace P (fun x ↦ f.isImmersion.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W}
    (hΦ : f.IsNormalizedTube hn hdim Φ)
    (u : letI := f.normalSpaceFiberBundle hn hdim
      (thomPair P (fun x ↦ f.isImmersion.NormalSpace x hn)).singularCohomology R k M (finrank ℝ P))
    (c : (TopPair.ofSubset (X := TopCat.of X) (range f)ᶜ).singularCohomology R k M
      (finrank ℝ P)) :
    letI := f.normalSpaceFiberBundle hn hdim
    c = f.relDualClassOf hn hdim hf u ↔
      ∀ x, TopPair.singularCohomologyMap (f.normalSlice hn hdim Φ hΦ.apply_zeroSection x) _ c =
        TopPair.singularCohomologyMap (fiberThomPairMap P (fun x ↦ f.isImmersion.NormalSpace x hn)
            x) _ u := by
  rw [← singularCohomologyMap_excisionMap_eq_iff_forall_normalSlice]
  refine ⟨?_, fun h ↦ (relDualClassOf_eq_of_isNormalizedTube f hn hdim hf hΦ h).symm⟩
  rintro rfl
  exact singularCohomologyMap_excisionMap_relDualClassOf f hn hdim hf hΦ u

end Independence

section TransDiffeomorph

variable {X' : Type w} [TopologicalSpace X'] [ChartedSpace G X'] [IsManifold J ∞ X']

/-- **The normal spaces of an embedding moved by an ambient diffeomorphism.** For a
diffeomorphism `φ : X' ≃ X`, the derivative of `φ` identifies the normal space at `x` of the
embedding `φ⁻¹ ∘ f` with that of `f`: `normalSpaceEquivOfComp` for the triangle
`φ ∘ (φ⁻¹ ∘ f) = f`. -/
def transDiffeomorphNormalSpaceEquiv (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (φ : X' ≃ₘ^∞⟮J, J⟯ X) (x : Z) :
    (f.transDiffeomorph φ.symm).isImmersion.NormalSpace x hn ≃L[ℝ] f.isImmersion.NormalSpace x hn :=
  (f.transDiffeomorph φ.symm).normalSpaceEquivOfComp f hn hn
    (fun _ ↦ φ.isInvertible_mfderiv hn) (f.comp_transDiffeomorph_symm φ) x

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] [IsManifold I ∞ Z] [IsManifold J ∞ X] in
/-- `transDiffeomorphNormalSpaceEquiv` is `normalSpaceEquivOfComp` for the triangle
`φ ∘ (φ⁻¹ ∘ f) = f`. -/
theorem transDiffeomorphNormalSpaceEquiv_def (f : SmoothEmbedding I J ∞ Z X)
    (hn : (∞ : ℕ∞ω) ≠ 0) (φ : X' ≃ₘ^∞⟮J, J⟯ X) (x : Z) :
    f.transDiffeomorphNormalSpaceEquiv hn φ x =
      (f.transDiffeomorph φ.symm).normalSpaceEquivOfComp f hn hn
        (fun _ ↦ φ.isInvertible_mfderiv hn) (f.comp_transDiffeomorph_symm φ) x :=
  (rfl)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] [IsManifold I ∞ Z] [IsManifold J ∞ X] in
/-- On the normal class of a tangent vector `w` of `X'`, `transDiffeomorphNormalSpaceEquiv` is the
normal class of its image `dφ w`. -/
@[simp]
theorem transDiffeomorphNormalSpaceEquiv_normalClass (f : SmoothEmbedding I J ∞ Z X)
    (hn : (∞ : ℕ∞ω) ≠ 0) (φ : X' ≃ₘ^∞⟮J, J⟯ X) (x : Z)
    (w : TangentSpace J (f.transDiffeomorph φ.symm x)) :
    f.transDiffeomorphNormalSpaceEquiv hn φ x
        ((f.transDiffeomorph φ.symm).isImmersion.normalClass x hn w) =
      f.isImmersion.normalClass x hn (tangentSpaceCast J (φ (f.transDiffeomorph φ.symm x)) (f x)
        (mfderiv J J φ (f.transDiffeomorph φ.symm x) w)) := by
  rw [transDiffeomorphNormalSpaceEquiv_def, normalSpaceEquivOfComp_normalClass]

/-- **The map of Thom pairs of normal bundles under an ambient diffeomorphism.** For a
diffeomorphism `φ : X' ≃ X`, the map `(ν', ν' ∖ 0) ⟶ (ν, ν ∖ 0)` from the Thom pair of the normal
bundle of `φ⁻¹ ∘ f` to that of `f`, over the identity of `Z`, which is the derivative of `φ` on
each fibre: `thomPairMapOfComp` for the triangle `φ ∘ (φ⁻¹ ∘ f) = f`. -/
def transDiffeomorphThomPairMap (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (φ : X' ≃ₘ^∞⟮J, J⟯ X) :
    thomPair P (fun x ↦ (f.transDiffeomorph φ.symm).isImmersion.NormalSpace x hn) ⟶
      thomPair P (fun x ↦ f.isImmersion.NormalSpace x hn) :=
  (f.transDiffeomorph φ.symm).thomPairMapOfComp f hn hn
    (φ.contMDiff.of_le (ENat.one_le_iff_ne_zero_withTop.mpr hn))
    (fun _ ↦ φ.isInvertible_mfderiv hn) (f.comp_transDiffeomorph_symm φ)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [IsManifold I ∞ Z] in
/-- `transDiffeomorphThomPairMap` is `thomPairMapOfComp` for the triangle
`φ ∘ (φ⁻¹ ∘ f) = f`. -/
theorem transDiffeomorphThomPairMap_def (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (φ : X' ≃ₘ^∞⟮J, J⟯ X) :
    f.transDiffeomorphThomPairMap (P := P) hn φ =
      (f.transDiffeomorph φ.symm).thomPairMapOfComp f hn hn
        (φ.contMDiff.of_le (ENat.one_le_iff_ne_zero_withTop.mpr hn))
        (fun _ ↦ φ.isInvertible_mfderiv hn) (f.comp_transDiffeomorph_symm φ) :=
  (rfl)

/-- On the fibre over `x`, `transDiffeomorphThomPairMap` is the isomorphism of fibre pairs
induced by `transDiffeomorphNormalSpaceEquiv` at `x`. -/
theorem fiberThomPairMap_comp_transDiffeomorphThomPairMap (f : SmoothEmbedding I J ∞ Z X)
    (hn : (∞ : ℕ∞ω) ≠ 0) (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    (φ : X' ≃ₘ^∞⟮J, J⟯ X) (x : Z) :
    letI := (f.transDiffeomorph φ.symm).normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceFiberBundle hn hdim
    fiberThomPairMap P (fun x ↦ (f.transDiffeomorph φ.symm).isImmersion.NormalSpace x hn) x ≫
        f.transDiffeomorphThomPairMap hn φ =
      (f.transDiffeomorphNormalSpaceEquiv hn φ x).complZeroPairIso.hom ≫
        fiberThomPairMap P (fun x ↦ f.isImmersion.NormalSpace x hn) x :=
  letI := (f.transDiffeomorph φ.symm).normalSpaceFiberBundle hn hdim
  letI := f.normalSpaceFiberBundle hn hdim
  fiberThomPairMap_comp_thomPairMapOfComp _ _ hn hn _ _ _ x

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] [IsManifold I ∞ Z] [IsManifold J ∞ X] in
/-- A diffeomorphism `φ : X' ≃ X` sends the complement of the range of `φ⁻¹ ∘ f` into the
complement of the range of `f`. -/
theorem mapsTo_compl_range_transDiffeomorph (f : SmoothEmbedding I J ∞ Z X)
    (φ : X' ≃ₘ^∞⟮J, J⟯ X) :
    MapsTo φ (range (f.transDiffeomorph φ.symm))ᶜ (range f)ᶜ := by
  rintro y hy ⟨z, hz⟩
  exact hy ⟨z, by rw [transDiffeomorph_apply, hz, Diffeomorph.symm_apply_apply]⟩

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] [IsManifold I ∞ Z] [IsManifold J ∞ X] in
/-- Moving an embedding with closed range by a diffeomorphism `φ : X ≃ X'` gives an embedding
with closed range. -/
theorem isClosed_range_transDiffeomorph {f : SmoothEmbedding I J ∞ Z X} (hf : IsClosed (range f))
    (φ : X ≃ₘ^∞⟮J, J⟯ X') : IsClosed (range (f.transDiffeomorph φ)) := by
  rw [range_transDiffeomorph]
  exact φ.toHomeomorph.isClosedMap _ hf

section LocalDegree

variable {C : Type*} [Category C] [Limits.HasCoproducts.{w} C] [Abelian C] {R : C}
  {k : Type*} [Ring k] [Linear k C] {M : C}

/-- **Normal slices under an ambient diffeomorphism.** Let `φ : X' ≃ X` be a diffeomorphism,
`Φ` a normalized tube of `f` and `Φ'` one of `φ⁻¹ ∘ f`. At every `x : Z`, the normal slice of
`Φ'` followed by `φ`, as a map of pairs `(ν'_x, ν'_x ∖ 0) ⟶ (X, X ∖ f(Z))`, pulls every class
back as the normal slice of `Φ` does after the isomorphism `ν'_x ≃ ν_x` given by the derivative
of `φ` (`transDiffeomorphNormalSpaceEquiv`), in every degree. -/
theorem singularCohomologyMap_normalSlice_transDiffeomorph {f : SmoothEmbedding I J ∞ Z X}
    {hn : (∞ : ℕ∞ω) ≠ 0} {hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E}
    (φ : X' ≃ₘ^∞⟮J, J⟯ X) {W : TopologicalSpace.Opens X} {W' : TopologicalSpace.Opens X'}
    {Φ : letI := f.normalSpaceFiberBundle hn hdim
      TotalSpace P (fun x ↦ f.isImmersion.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W}
    {Φ' : letI := (f.transDiffeomorph φ.symm).normalSpaceFiberBundle hn hdim
      TotalSpace P (fun x ↦ (f.transDiffeomorph φ.symm).isImmersion.NormalSpace x hn) ≃ₘ^∞⟮I.prod
          𝓘(ℝ, P), J⟯
        W'}
    (hΦ : f.IsNormalizedTube hn hdim Φ)
    (hΦ' : (f.transDiffeomorph φ.symm).IsNormalizedTube hn hdim Φ') (x : Z) {n : ℕ}
    (c : (TopPair.ofSubset (X := TopCat.of X) (range f)ᶜ).singularCohomology R k M n) :
    TopPair.singularCohomologyMap
        ((f.transDiffeomorph φ.symm).normalSlice hn hdim Φ' hΦ'.apply_zeroSection x ≫
          TopPair.ofSubsetMap (X := TopCat.of X') (Y := TopCat.of X)
            (TopCat.ofHom ⟨φ, φ.continuous⟩) (f.mapsTo_compl_range_transDiffeomorph φ)) n c =
      TopPair.singularCohomologyMap
        ((f.transDiffeomorphNormalSpaceEquiv hn φ x).complZeroPairIso.hom ≫
          f.normalSlice hn hdim Φ hΦ.apply_zeroSection x) n c := by
  let := f.normalSpaceFiberBundle hn hdim
  have := f.normalSpaceVectorBundle hn hdim
  let := (f.transDiffeomorph φ.symm).normalSpaceFiberBundle hn hdim
  have := (f.transDiffeomorph φ.symm).normalSpaceVectorBundle hn hdim
  set e := trivializationAt P (fun x ↦ f.isImmersion.NormalSpace x hn) x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt P _ x
  set m := (e.continuousLinearEquivAt ℝ x hx).symm
  set ℓ := f.transDiffeomorphNormalSpaceEquiv hn φ x
  set ψ := m.trans ℓ.symm
  -- The map `g' : w ↦ Φ'(x, ℓ⁻¹ (m w))` into `X'`, and its image `g = φ ∘ g'` in `X`.
  obtain ⟨hgc', hg0', hgf', A', hg', hA'⟩ := hΦ'.exists_hasMFDerivAt_apply_mk x ψ
  set g' : P → X' := fun w ↦ (Φ' (TotalSpace.mk' P x (ψ w)) : X')
  set g : P → X := fun w ↦ φ (g' w)
  have hgc : ContinuousOn g univ := (φ.continuous.comp hgc').continuousOn
  have hg0 : g 0 = f x := by
    simp only [g, g', hg0', transDiffeomorph_apply, Diffeomorph.apply_symm_apply]
  have hgf : ∀ w ∈ univ, g w ∈ range f → w = 0 := by
    rintro w - ⟨z, hz⟩
    exact hgf' w ⟨z, (transDiffeomorph_apply _ _ _).trans (φ.symm_apply_eq.2 hz)⟩
  have hφ : HasMFDerivAt J J φ (g' 0) (mfderiv J J φ (g' 0)) :=
    (φ.contMDiff.mdifferentiableAt (by simp)).hasMFDerivAt
  -- On normal classes, `dφ` at the point `f' x` is `ℓ`.
  have hdφ : ∀ (y : X') (_ : y = f.transDiffeomorph φ.symm x) (D : TangentSpace J y),
      f.isImmersion.normalClassL x hn (mfderiv J J φ y D) =
        ℓ ((f.transDiffeomorph φ.symm).isImmersion.normalClassL x hn D) := by
    rintro _ rfl D
    have h := f.transDiffeomorphNormalSpaceEquiv_normalClass hn φ x D
    rw [tangentSpaceCast_apply] at h
    rw [Manifold.IsImmersion.normalClassL_apply (hf := (f.transDiffeomorph φ.symm).isImmersion)]
    exact (Manifold.IsImmersion.normalClassL_apply _ _ _ _).trans h.symm
  set A := (mfderiv J J φ (g' 0)).comp (A' : P →L[ℝ] TangentSpace J (g' 0))
  have hA (w : P) : f.isImmersion.normalClassL x hn (A w) = e.symmL ℝ x w := by
    refine (hdφ _ hg0' (A' w)).trans ?_
    rw [hA', ← e.symm_continuousLinearEquivAt_eq' hx, ContinuousLinearEquiv.coe_coe]
    simp [ψ, m]
  have h1 := singularCohomologyMap_slice_eq_of_hasFDerivAt hΦ x Filter.univ_mem hgc hg0 hgf
    (hφ.comp 0 hg') hA c
  -- Read on `(univ, univ ∖ {0})` through `m`, the map `g` is `ℓ⁻¹`, then the normal slice of
  -- `Φ'`, then `φ`.
  have hgi : TopPair.ofSubsetMap (X := TopCat.of (univ : Set P)) (Y := TopCat.of X)
      (TopCat.ofHom ⟨univ.domRestrict g, hgc.domRestrict⟩) (B := {⟨0, mem_univ 0⟩}ᶜ)
      (B' := (range f)ᶜ) (fun w hw h ↦ hw (Subtype.ext (hgf w w.property h))) =
      (TopPair.ofSubsetMap (X := TopCat.of (univ : Set P)) (Y := TopCat.of P)
        (TopCat.ofHom (ContinuousMap.subtypeVal univ)) (B := {⟨0, mem_univ 0⟩}ᶜ)
        (B' := {0}ᶜ) (fun _ hw h ↦ hw (Subtype.ext (Set.mem_singleton_iff.1 h))) ≫
        m.complZeroPairIso.hom) ≫ ℓ.complZeroPairIso.inv ≫
        (f.transDiffeomorph φ.symm).normalSlice hn hdim Φ' hΦ'.apply_zeroSection x ≫
          TopPair.ofSubsetMap (X := TopCat.of X') (Y := TopCat.of X)
            (TopCat.ofHom ⟨φ, φ.continuous⟩) (f.mapsTo_compl_range_transDiffeomorph φ) := by
    refine TopPair.hom_ext_of_fst _ (ConcreteCategory.hom_ext _ _ fun w ↦ ?_)
    simp only [TopPair.Hom.fst_comp, ConcreteCategory.comp_apply]
    -- The points of the pairs are those of `univ`, `P` and `X` only up to unfolding `ofSubset`.
    erw [TopPair.ofSubsetMap_fst_apply, TopPair.ofSubsetMap_fst_apply,
      TopPair.ofSubsetMap_fst_apply]
    rw [ContinuousLinearEquiv.complZeroPairIso_hom_fst_apply,
      ContinuousLinearEquiv.complZeroPairIso_inv_fst_apply, normalSlice_fst_apply]
    -- Both sides are `φ (Φ' (x, ℓ⁻¹ (m w)))`, with `w` a point of `univ` only up to unfolding
    -- `ofSubset`, so `Set.domRestrict_apply` does not apply syntactically.
    rfl
  have h3 : TopPair.singularCohomologyMap (ℓ.complZeroPairIso.inv ≫
      (f.transDiffeomorph φ.symm).normalSlice hn hdim Φ' hΦ'.apply_zeroSection x ≫
        TopPair.ofSubsetMap (X := TopCat.of X') (Y := TopCat.of X)
          (TopCat.ofHom ⟨φ, φ.continuous⟩) (f.mapsTo_compl_range_transDiffeomorph φ)) n c =
      TopPair.singularCohomologyMap (f.normalSlice hn hdim Φ hΦ.apply_zeroSection x) n c := by
    refine TopPair.injective_singularCohomologyMap_ofSubsetMap_subtypeVal_univ_comp R k M (0 : P)
      m.complZeroPairIso n ?_
    rw [← TopPair.singularCohomologyMap_comp_apply, ← hgi, h1]
  rw [TopPair.singularCohomologyMap_comp_apply ℓ.complZeroPairIso.hom, ← h3,
    ← TopPair.singularCohomologyMap_comp_apply, Iso.hom_inv_id_assoc]

end LocalDegree

section Naturality

variable {k : Type*} [CommRing k] {R M : ModuleCat.{w} k} [Module.Projective k R]
  [I.Boundaryless] [J.Boundaryless] [T2Space X] [SecondCountableTopology X] [T2Space X']
  [SecondCountableTopology X']

/-- **Naturality of the relative class under a diffeomorphism.** Let `φ : X' ≃ X` be a
diffeomorphism and `u` a class of the Thom pair of the normal bundle of `f` in the degree
`r = finrank ℝ P` of its rank, with coefficients `R, M : ModuleCat k` and `R` projective over `k`.
The relative class of `φ⁻¹ ∘ f` given by the pull-back of `u` along the map of Thom pairs
`transDiffeomorphThomPairMap` is the pull-back along `φ : (X', X' ∖ φ⁻¹(f(Z))) ⟶ (X, X ∖ f(Z))`
of `relDualClassOf f hn hdim hf u`. -/
theorem relDualClassOf_transDiffeomorph (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) (hf : IsClosed (range f))
    (φ : X' ≃ₘ^∞⟮J, J⟯ X)
    (u : letI := f.normalSpaceFiberBundle hn hdim
      (thomPair P (fun x ↦ f.isImmersion.NormalSpace x hn)).singularCohomology R k M
          (finrank ℝ P)) :
    (f.transDiffeomorph φ.symm).relDualClassOf hn hdim
        (f.isClosed_range_transDiffeomorph hf φ.symm)
        (TopPair.singularCohomologyMap (f.transDiffeomorphThomPairMap hn φ) _ u) =
      TopPair.singularCohomologyMap
        (TopPair.ofSubsetMap (X := TopCat.of X') (Y := TopCat.of X)
          (TopCat.ofHom ⟨φ, φ.continuous⟩) (f.mapsTo_compl_range_transDiffeomorph φ)) _
        (f.relDualClassOf hn hdim hf u) := by
  let := f.normalSpaceFiberBundle hn hdim
  let := (f.transDiffeomorph φ.symm).normalSpaceFiberBundle hn hdim
  obtain ⟨W, Φ, hΦ, -⟩ :=
    exists_isNormalizedTube_singularCohomologyMap_excisionMap_relDualClassOf (R := R) (k := k)
      (M := M) f hn hdim hf
  obtain ⟨W', Φ', hΦ', -⟩ :=
    exists_isNormalizedTube_singularCohomologyMap_excisionMap_relDualClassOf (R := R) (k := k)
      (M := M) (f.transDiffeomorph φ.symm) hn hdim (f.isClosed_range_transDiffeomorph hf φ.symm)
  refine relDualClassOf_eq_of_isNormalizedTube _ hn hdim _ hΦ' ?_
  rw [singularCohomologyMap_excisionMap_eq_iff_forall_normalSlice]
  intro x
  rw [← TopPair.singularCohomologyMap_comp_apply,
    singularCohomologyMap_normalSlice_transDiffeomorph φ hΦ hΦ' x,
    ← TopPair.singularCohomologyMap_comp_apply,
    fiberThomPairMap_comp_transDiffeomorphThomPairMap f hn hdim φ x,
    TopPair.singularCohomologyMap_comp_apply, TopPair.singularCohomologyMap_comp_apply,
    (singularCohomologyMap_excisionMap_eq_iff_forall_normalSlice f hn hdim Φ
      hΦ.apply_zeroSection u _).1 (singularCohomologyMap_excisionMap_relDualClassOf f hn hdim hf
        hΦ u) x]

/-- **Naturality of the absolute class under a diffeomorphism.** Let `φ : X' ≃ X` be a
diffeomorphism and `u` a class of the Thom pair of the normal bundle of `f` in the degree
`r = finrank ℝ P` of its rank, with coefficients `R, M : ModuleCat k` and `R` projective over `k`.
The absolute class of `φ⁻¹ ∘ f` given by the pull-back of `u` along the map of Thom pairs
`transDiffeomorphThomPairMap` is the pull-back along `φ` of `dualClassOf f hn hdim hf u`. -/
theorem dualClassOf_transDiffeomorph (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) (hf : IsClosed (range f))
    (φ : X' ≃ₘ^∞⟮J, J⟯ X)
    (u : letI := f.normalSpaceFiberBundle hn hdim
      (thomPair P (fun x ↦ f.isImmersion.NormalSpace x hn)).singularCohomology R k M
          (finrank ℝ P)) :
    (f.transDiffeomorph φ.symm).dualClassOf hn hdim
        (f.isClosed_range_transDiffeomorph hf φ.symm)
        (TopPair.singularCohomologyMap (f.transDiffeomorphThomPairMap hn φ) _ u) =
      TopCat.singularCohomologyMap (TopCat.ofHom ⟨φ, φ.continuous⟩) _
        (f.dualClassOf hn hdim hf u) := by
  rw [dualClassOf_def, dualClassOf_def, relDualClassOf_transDiffeomorph,
    TopPair.singularCohomologyπ_singularCohomologyMap_ofSubsetMap]

/-- **Naturality of the relative dual class under a diffeomorphism.** Let `φ : X' ≃ X` be a
diffeomorphism and `o` an orientation of the normal bundle of `f`, of rank `r`. The relative dual
class of `φ⁻¹ ∘ f`, normally oriented by the pull-back of `o` along the derivative of `φ`
(`normalSpaceEquivOfComp` for `φ ∘ (φ⁻¹ ∘ f) = f`), is the pull-back along
`φ : (X', X' ∖ φ⁻¹(f(Z))) ⟶ (X, X ∖ f(Z))` of `relDualClass f hn hdim hf o hr`. -/
theorem relDualClass_transDiffeomorph (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) (hf : IsClosed (range f))
    (φ : X' ≃ₘ^∞⟮J, J⟯ X) {r : ℕ}
    (o : letI := f.normalSpaceFiberBundle hn hdim
      letI := f.normalSpaceVectorBundle hn hdim
      VectorBundleOrientation P (fun x ↦ f.NormalSpace x hn) (Fin r)) (hr : finrank ℝ P = r) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    letI := (f.transDiffeomorph φ.symm).normalSpaceFiberBundle hn hdim
    letI := (f.transDiffeomorph φ.symm).normalSpaceVectorBundle hn hdim
    (f.transDiffeomorph φ.symm).relDualClass hn hdim (f.isClosed_range_transDiffeomorph hf φ.symm)
        (o.comap (g := ContinuousMap.id Z) ((Fintype.card_fin r).trans hr.symm)
          ((f.transDiffeomorph φ.symm).continuous_normalSpaceEquivOfComp f hn hn
            (φ.contMDiff.of_le (ENat.one_le_iff_ne_zero_withTop.mpr hn))
            (fun _ ↦ φ.isInvertible_mfderiv hn) (f.comp_transDiffeomorph_symm φ))) hr =
      TopPair.singularCohomologyMap
        (TopPair.ofSubsetMap (X := TopCat.of X') (Y := TopCat.of X)
          (TopCat.ofHom ⟨φ, φ.continuous⟩) (f.mapsTo_compl_range_transDiffeomorph φ)) _
        (f.relDualClass hn hdim hf o hr) := by
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  let := (f.transDiffeomorph φ.symm).normalSpaceFiberBundle hn hdim
  let := (f.transDiffeomorph φ.symm).normalSpaceVectorBundle hn hdim
  subst hr
  -- `relDualClass` takes integral cohomology with the structure `Linear.preadditiveIntLinear` of
  -- `ModuleCat ℤ`, `relDualClassOf_transDiffeomorph` the structure `ModuleCat.instLinear`; they
  -- are equal (`Linear.subsingletonInt`) but not by definition.
  have key (L : Linear ℤ (ModuleCat.{w} ℤ))
      (u : (thomPair P fun x ↦ f.NormalSpace x hn).singularCohomology
        (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ (ModuleCat.of ℤ (ULift.{w} ℤ)) (finrank ℝ P)) :
      (f.transDiffeomorph φ.symm).relDualClassOf hn hdim
          (f.isClosed_range_transDiffeomorph hf φ.symm)
          (TopPair.singularCohomologyMap (f.transDiffeomorphThomPairMap hn φ) _ u) =
        TopPair.singularCohomologyMap
          (TopPair.ofSubsetMap (X := TopCat.of X') (Y := TopCat.of X)
            (TopCat.ofHom ⟨φ, φ.continuous⟩) (f.mapsTo_compl_range_transDiffeomorph φ)) _
          (f.relDualClassOf hn hdim hf u) := by
    obtain rfl : L = ModuleCat.instLinear := Subsingleton.elim _ _
    exact relDualClassOf_transDiffeomorph f hn hdim hf φ u
  rw [relDualClass_def, relDualClass_def, ← key, transDiffeomorphThomPairMap_def,
    thomPairMapOfComp_def]
  -- The goal agrees with the naturality of the canonical Thom class only up to unfolding
  -- (`thomPairMapOfFiberwise` over `g = ContinuousMap.id Z`), which `rw` does not see.
  exact congrArg _ (o.singularCohomologyMap_thomPairMapOfFiberwise_canonicalThomClass_comap rfl rfl
      _).symm

/-- **Naturality of the dual class under a diffeomorphism.** Let `φ : X' ≃ X` be a diffeomorphism
and `o` an orientation of the normal bundle of `f`, of rank `r`. The dual class of `φ⁻¹ ∘ f`,
normally oriented by the pull-back of `o` along the derivative of `φ`
(`normalSpaceEquivOfComp` for `φ ∘ (φ⁻¹ ∘ f) = f`), is the pull-back along `φ` of
`dualClass f hn hdim hf o hr`. -/
theorem dualClass_transDiffeomorph (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) (hf : IsClosed (range f))
    (φ : X' ≃ₘ^∞⟮J, J⟯ X) {r : ℕ}
    (o : letI := f.normalSpaceFiberBundle hn hdim
      letI := f.normalSpaceVectorBundle hn hdim
      VectorBundleOrientation P (fun x ↦ f.NormalSpace x hn) (Fin r)) (hr : finrank ℝ P = r) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    letI := (f.transDiffeomorph φ.symm).normalSpaceFiberBundle hn hdim
    letI := (f.transDiffeomorph φ.symm).normalSpaceVectorBundle hn hdim
    (f.transDiffeomorph φ.symm).dualClass hn hdim (f.isClosed_range_transDiffeomorph hf φ.symm)
        (o.comap (g := ContinuousMap.id Z) ((Fintype.card_fin r).trans hr.symm)
          ((f.transDiffeomorph φ.symm).continuous_normalSpaceEquivOfComp f hn hn
            (φ.contMDiff.of_le (ENat.one_le_iff_ne_zero_withTop.mpr hn))
            (fun _ ↦ φ.isInvertible_mfderiv hn) (f.comp_transDiffeomorph_symm φ))) hr =
      TopCat.singularCohomologyMap (TopCat.ofHom ⟨φ, φ.continuous⟩) _
        (f.dualClass hn hdim hf o hr) := by
  rw [dualClass_eq_singularCohomologyπ_relDualClass,
    dualClass_eq_singularCohomologyπ_relDualClass, relDualClass_transDiffeomorph,
    TopPair.singularCohomologyπ_singularCohomologyMap_ofSubsetMap]

end Naturality

end TransDiffeomorph

end TauCeti.SmoothEmbedding

end
