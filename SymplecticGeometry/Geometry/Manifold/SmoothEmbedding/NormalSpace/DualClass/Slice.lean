/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.DualClass.Basic
public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.ThomPairMap
public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.Diffeomorph
public import SymplecticGeometry.Topology.VectorBundle.Thom.FiberCoordinate
public import TauCeti.Geometry.Manifold.LocallyContractible
public import TauCeti.Topology.VectorBundle.MayerVietoris.DirectedUnion
public import TauCeti.Topology.VectorBundle.Thom.FiberwiseEquiv
import SymplecticGeometry.AlgebraicTopology.Cohomology.Local.Restrict
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
slice of a normalized tube `Φ` at `x` with any map `g` from a neighbourhood `B` of `0` in a real
normed space `Q` into `X` which sends only `0` into `f(Z)`, sends it to `f x`, and whose
derivative at `0`, followed by the quotient onto the normal space, is a given linear isomorphism
`m : Q ≃ ν_x`. Both pull classes of `(X, X ∖ f(Z))` back in the same way, in every degree, once
the slice is read on `B` through `m`. Precomposing with a linear isomorphism reduces this to the
case `Q = P` with `m` the inverse of the preferred trivialization `e` at `x`. There, on a small
enough open `O ⊆ B` (restriction to which is
injective by excision, `TopPair.injective_singularCohomologyMap_ofSubsetMap_inclusion`), `g`
lifts through `Φ` to a map into the Thom pair whose base points stay in a contractible
neighbourhood of `x`. Since `Φ` is normalized, the coordinate of that lift in `e` has derivative
the identity at `0` (`TauCeti.SmoothEmbedding.IsNormalizedTube.hasFDerivAt_trivializationAt_snd`),
so by the local-degree lemma for maps into a Thom pair
(`TauCeti.singularCohomologyMap_ofSubsetMap_eq_complZeroPairIso_inv_of_hasFDerivAt_of_mapsTo`)
the lift pulls classes back as the restriction to the fibre over `x`, carried to `(P, P ∖ {0})`
along `e` and pulled back along the inclusion of `O`. This follows the
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

For a normal orientation `o`, the slices of `relDualClass f hn hdim hf o hr` are therefore the
fibre restrictions of the canonical Thom class: read through a linear isomorphism `m : Q ≃ ν_x`
that carries an orientation `ν` of `Q` to `o x`, the slice at `x` is the generator
`ν.modelThomGenerator hQ` (`singularCohomologyMap_normalSlice_relDualClass`), by the naturality
of the model generators under linear isomorphisms
(`Orientation.singularCohomologyMap_modelThomGenerator`), which moves it from the trivialization
at `x` to `m`.

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
  lemma: a map on a space `Q` whose derivative at `0`, followed by the quotient onto the normal
  space, is a linear isomorphism `m : Q ≃ ν_x` pulls classes back as the normal slice read
  through `m` does.
* `TauCeti.SmoothEmbedding.singularCohomologyMap_normalSlice_eq_of_isNormalizedTube`: the normal
  slices of two normalized tubes at a point pull classes back alike.
* `TauCeti.SmoothEmbedding.relDualClassOf_eq_of_isNormalizedTube`,
  `TauCeti.SmoothEmbedding.singularCohomologyMap_excisionMap_relDualClassOf`: independence of the
  tube: for `u` of degree `r`, with coefficients `R, M : ModuleCat k` and `R` projective over `k`,
  every normalized tube carries `relDualClassOf f hn hdim hf u`.
* `TauCeti.SmoothEmbedding.eq_relDualClassOf_iff_forall_slice`: for `u` of degree `r`, a class
  is `relDualClassOf f hn hdim hf u` exactly when its slices along a normalized tube are the
  fibre restrictions of `u`.
* `TauCeti.SmoothEmbedding.singularCohomologyMap_normalSlice_relDualClass`: read through a linear
  isomorphism `Q ≃ ν_x` that preserves orientation, the normal slice at `x` of the relative dual
  class is the model generator of `Q`.
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

/-- **The normal slice read through a linear isomorphism.** For a linear isomorphism
`m : P ≃ ν_x` and a map of pairs `h : (X, X ∖ f(Z)) ⟶ (Y, B')`, the inclusion
`(univ, univ ∖ {0}) ⟶ (P, P ∖ {0})`, followed by `m`, the normal slice of `Φ` at `x` and `h`, is
the map of pairs given by any `g : P → Y` with `g w = h(Φ(x, m w))` for all `w`. -/
theorem ofSubsetMap_subtypeVal_comp_complZeroPairIso_hom_comp_normalSlice_comp
    (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) {W : TopologicalSpace.Opens X}
    (Φ : letI := f.normalSpaceFiberBundle hn hdim
      TotalSpace P (fun x ↦ f.isImmersion.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W)
    (hΦ : letI := f.normalSpaceFiberBundle hn hdim
      ∀ x, (Φ (zeroSection P _ x) : X) = f x) (x : Z)
    (m : P ≃L[ℝ] f.isImmersion.NormalSpace x hn) {Y : TopCat.{w}} {B' : Set Y}
    (h : TopPair.ofSubset (X := TopCat.of X) (range f)ᶜ ⟶ TopPair.ofSubset B') {g : P → Y}
    (hgc : ContinuousOn g univ) (hgB : ∀ w, w ≠ 0 → g w ∈ B')
    (hg : ∀ w, TopPair.Hom.fst h (Φ (TotalSpace.mk' P x (m w)) : X) = g w) :
    (TopPair.ofSubsetMap (X := TopCat.of (univ : Set P)) (Y := TopCat.of P)
        (TopCat.ofHom (ContinuousMap.subtypeVal univ)) (B := {⟨0, mem_univ 0⟩}ᶜ)
        (B' := {0}ᶜ) (fun _ hw h ↦ hw (Subtype.ext (Set.mem_singleton_iff.1 h))) ≫
        m.complZeroPairIso.hom) ≫ f.normalSlice hn hdim Φ hΦ x ≫ h =
      TopPair.ofSubsetMap (X := TopCat.of (univ : Set P)) (Y := Y)
        (TopCat.ofHom ⟨univ.domRestrict g, hgc.domRestrict⟩) (B := {⟨0, mem_univ 0⟩}ᶜ)
        (B' := B') fun w hw ↦ hgB w fun h ↦ hw (Subtype.ext h) := by
  refine TopPair.hom_ext_of_fst _ (ConcreteCategory.hom_ext _ _ fun w ↦ ?_)
  simp only [TopPair.Hom.fst_comp, ConcreteCategory.comp_apply]
  -- The `MapsTo` proofs in the statement typecheck only after unfolding `ofSubset`, which keeps
  -- `rw` from matching; `generalize_proofs` replaces them by hypotheses.
  generalize_proofs
  rw [TopPair.ofSubsetMap_fst_apply, TopPair.ofSubsetMap_fst_apply,
    ContinuousLinearEquiv.complZeroPairIso_hom_fst_apply, normalSlice_fst_apply]
  exact hg _

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
  have hLψ : LO = ψ ≫ (f.tubePairIso hn hdim Φ hΦ.apply_zeroSection).hom ≫
      TopPair.excisionMap (X := TopCat.of X) (W : Set X) (range f)ᶜ := by
    refine TopPair.hom_ext_of_fst _ (ConcreteCategory.hom_ext _ _ fun w ↦ ?_)
    rw [TopPair.Hom.fst_comp, TopPair.Hom.fst_comp, ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply]
    refine Eq.trans ?_ (tubePairIso_hom_fst_comp_excisionMap_fst_apply f hn hdim Φ _ _).symm
    simp only [LO, ψ]
    -- The `MapsTo` proofs of `LO` and `ψ` typecheck only after unfolding `ofSubset`, which keeps
    -- `rw` from matching; `generalize_proofs` replaces them by hypotheses.
    generalize_proofs
    rw [TopPair.ofSubsetMap_fst_apply, TopPair.ofSubsetMap_fst_apply]
    exact (hΦΨ (hOW _ (show O from w).property)).symm
  rw [hLψ, TopPair.singularCohomologyMap_comp_apply, normalSlice_def,
    ContinuousLinearEquiv.complZeroPairIso_symm, Iso.symm_hom]
  -- Since `Φ` is normalized, the fibre coordinate of `g` has derivative the identity at `0`.
  have hF : HasFDerivAt (fun w ↦ (e (Ψ (g w))).2) (ContinuousLinearMap.id ℝ P) 0 :=
    hΦ.hasFDerivAt_trivializationAt_snd hg hA hΨg hΨ0
      (by filter_upwards [hO.mem_nhds hO0] with w hw using hΦΨ (hOW w hw))
  refine (singularCohomologyMap_ofSubsetMap_eq_complZeroPairIso_inv_of_hasFDerivAt_of_mapsTo e hUe
    hxU (hO.mem_nhds hO0) (hΨc.comp hgO hOW) hOU hΨ0 hψ0 hF (K := 1) AntilipschitzWith.id
    _).trans ?_
  simp only [TopPair.singularCohomologyMap_comp_apply]
  -- The derivative `ContinuousLinearMap.id ℝ P`, restricted to `O`, is the inclusion of `O`.
  rfl

/-- The local-degree lemma read through the preferred trivialization `e` of the normal bundle at
`x`, a step of `singularCohomologyMap_slice_eq_of_hasFDerivAt`: the map `g` is on `P`, and the
normal class of each `A w` is the vector of the fibre over `x` with coordinate `w` in `e`. -/
private theorem singularCohomologyMap_slice_eq_of_hasFDerivAt_trivializationAt
    {f : SmoothEmbedding I J ∞ Z X}
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
  refine TopPair.injective_singularCohomologyMap_ofSubsetMap_inclusion R k M hO hOB hO0 n ?_
  rw [← TopPair.singularCohomologyMap_comp_apply, ← TopPair.singularCohomologyMap_comp_apply,
    ← Category.assoc]
  convert singularCohomologyMap_slice_eq_of_isOpen hΦ x hO hO0 (hgB.mono hOB)
    (fun w hw ↦ hgf w (hOB hw)) hg hA hΨc hΦΨ hΨ0 hUe hOW hOU c using 4
  · exact TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ _ rfl
  · congr 1
    exact TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ _ rfl

/-- **The local-degree lemma.** Let `Φ` be a normalized tube of
`f`, `x : Z`, and `m : Q ≃ ν_x` a linear isomorphism from a real normed space `Q`. Let `B ⊆ Q` be
a neighbourhood of `0` and `g : Q → X` a map continuous on `B`, with `g 0 = f x`, sending no other
point of `B` into `f(Z)`, and differentiable at `0` with a derivative `A` such that the normal
class of each `A w` is `m w`. Then `g`, as a map of pairs `(B, B ∖ {0}) ⟶ (X, X ∖ f(Z))`, pulls
every class back as the normal slice of `Φ` at `x` does after `m`: the inclusion
`(B, B ∖ {0}) ⟶ (Q, Q ∖ {0})` followed by the pair isomorphism of `m`.

The proof reads `g` on `P` as `g ∘ m⁻¹ ∘ e⁻¹`, `e` the preferred trivialization at `x`. -/
theorem singularCohomologyMap_slice_eq_of_hasFDerivAt {f : SmoothEmbedding I J ∞ Z X}
    {hn : (∞ : ℕ∞ω) ≠ 0} {hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E}
    {W : TopologicalSpace.Opens X}
    {Φ : letI := f.normalSpaceFiberBundle hn hdim
      TotalSpace P (fun x ↦ f.isImmersion.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W}
    (hΦ : f.IsNormalizedTube hn hdim Φ) (x : Z) {Q : Type w} [NormedAddCommGroup Q]
    [NormedSpace ℝ Q] (m : Q ≃L[ℝ] f.isImmersion.NormalSpace x hn) {B : Set Q} (hB : B ∈ 𝓝 0)
    {g : Q → X} (hgB : ContinuousOn g B) (hg0 : g 0 = f x)
    (hgf : ∀ w ∈ B, g w ∈ range f → w = 0) {A : Q →L[ℝ] V} (hg : HasMFDerivAt 𝓘(ℝ, Q) J g 0 A)
    (hA : ∀ w : Q, f.isImmersion.normalClassL x hn (A w) = m w)
    {n : ℕ} (c : (TopPair.ofSubset (X := TopCat.of X) (range f)ᶜ).singularCohomology R k M n) :
    TopPair.singularCohomologyMap
        (TopPair.ofSubsetMap (X := TopCat.of B) (Y := TopCat.of X)
          (TopCat.ofHom ⟨B.domRestrict g, hgB.domRestrict⟩)
          (B := {⟨0, mem_of_mem_nhds hB⟩}ᶜ) (B' := (range f)ᶜ)
          fun w hw h ↦ hw (Subtype.ext (hgf w w.property h))) n c =
      TopPair.singularCohomologyMap
        (TopPair.ofSubsetMap (X := TopCat.of B) (Y := TopCat.of Q)
          (TopCat.ofHom (ContinuousMap.subtypeVal B)) (B := {⟨0, mem_of_mem_nhds hB⟩}ᶜ)
          (B' := {0}ᶜ) (fun _ hw h ↦ hw (Subtype.ext (Set.mem_singleton_iff.1 h))) ≫
          m.complZeroPairIso.hom) n
        (TopPair.singularCohomologyMap (f.normalSlice hn hdim Φ hΦ.apply_zeroSection x) n c) := by
  let := f.normalSpaceFiberBundle hn hdim
  have := f.normalSpaceVectorBundle hn hdim
  set e := trivializationAt P (fun x ↦ f.isImmersion.NormalSpace x hn) x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt P _ x
  set ℓ := e.continuousLinearEquivAt ℝ x hx
  -- Read `g` on `P` through `L = m⁻¹ ∘ ℓ⁻¹`, so that the preferred trivialization appears.
  set L : P ≃L[ℝ] Q := ℓ.symm.trans m.symm
  have hB' : L ⁻¹' B ∈ 𝓝 (0 : P) :=
    L.continuous.continuousAt.preimage_mem_nhds (by rwa [map_zero])
  have hgB' : ContinuousOn (g ∘ L) (L ⁻¹' B) :=
    hgB.comp L.continuous.continuousOn (mapsTo_preimage _ _)
  have hg0' : (g ∘ L) 0 = f x := by simp [hg0]
  have hgf' (w : P) (hw : w ∈ L ⁻¹' B) (h : (g ∘ L) w ∈ range f) : w = 0 :=
    L.map_eq_zero_iff.1 (hgf _ hw h)
  have hgL : HasMFDerivAt 𝓘(ℝ, Q) J g (L 0) A := by rwa [map_zero]
  have hg' : HasMFDerivAt 𝓘(ℝ, P) J (g ∘ L) 0 (A.comp (L : P →L[ℝ] Q)) :=
    hgL.comp 0 L.hasFDerivAt.hasMFDerivAt
  have hA' (w : P) : f.isImmersion.normalClassL x hn (A.comp (L : P →L[ℝ] Q) w) =
      e.symmL ℝ x w := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, hA]
    simp only [L, ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.apply_symm_apply]
    rw [← e.symm_continuousLinearEquivAt_eq' hx, ContinuousLinearEquiv.coe_coe]
  have h := singularCohomologyMap_slice_eq_of_hasFDerivAt_trivializationAt hΦ x hB' hgB' hg0' hgf'
    hg' hA' c
  -- The map of pairs `(B, B ∖ {0}) ⟶ (L⁻¹ B, L⁻¹ B ∖ {0})`, `w ↦ L⁻¹ w`.
  let φ := TopPair.ofSubsetMap (X := TopCat.of B) (Y := TopCat.of (L ⁻¹' B))
    (TopCat.ofHom ⟨fun w ↦ ⟨L.symm w, by simp [w.property]⟩, by fun_prop⟩)
    (B := {⟨0, mem_of_mem_nhds hB⟩}ᶜ) (B' := {⟨0, mem_of_mem_nhds hB'⟩}ᶜ)
    fun w hw h ↦ hw (Subtype.ext (by simpa using congrArg Subtype.val h))
  have h1 : φ ≫ TopPair.ofSubsetMap (X := TopCat.of (L ⁻¹' B)) (Y := TopCat.of X)
        (TopCat.ofHom ⟨(L ⁻¹' B).domRestrict (g ∘ L), hgB'.domRestrict⟩)
        (B := {⟨0, mem_of_mem_nhds hB'⟩}ᶜ) (B' := (range f)ᶜ)
        (fun w hw h ↦ hw (Subtype.ext (hgf' w w.property h))) =
      TopPair.ofSubsetMap (X := TopCat.of B) (Y := TopCat.of X)
          (TopCat.ofHom ⟨B.domRestrict g, hgB.domRestrict⟩)
          (B := {⟨0, mem_of_mem_nhds hB⟩}ᶜ) (B' := (range f)ᶜ)
          fun w hw h ↦ hw (Subtype.ext (hgf w w.property h)) := by
    refine TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ _ ?_
    ext w
    simp
  have h2 : φ ≫ TopPair.ofSubsetMap (X := TopCat.of (L ⁻¹' B)) (Y := TopCat.of P)
          (TopCat.ofHom (ContinuousMap.subtypeVal (L ⁻¹' B)))
          (B := {⟨0, mem_of_mem_nhds hB'⟩}ᶜ) (B' := {0}ᶜ)
          (fun _ hw h ↦ hw (Subtype.ext (Set.mem_singleton_iff.1 h))) ≫
          ℓ.symm.complZeroPairIso.hom =
      TopPair.ofSubsetMap (X := TopCat.of B) (Y := TopCat.of Q)
          (TopCat.ofHom (ContinuousMap.subtypeVal B)) (B := {⟨0, mem_of_mem_nhds hB⟩}ᶜ)
          (B' := {0}ᶜ) (fun _ hw h ↦ hw (Subtype.ext (Set.mem_singleton_iff.1 h))) ≫
          m.complZeroPairIso.hom := by
    rw [ContinuousLinearEquiv.complZeroPairIso_hom, ContinuousLinearEquiv.complZeroPairIso_hom]
    simp only [φ]
    -- The `MapsTo` proofs in the statement typecheck only after unfolding `ofSubset`, which keeps
    -- `rw` from matching; `generalize_proofs` replaces them by hypotheses.
    generalize_proofs
    rw [← Category.assoc, TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ ?_ rfl]
    · refine TopPair.ofSubsetMap_comp_ofSubsetMap_eq _ _ _ _ ?_
      ext w
      simp [L]
    · intro w hw h
      exact hw (Subtype.ext (by simpa [L] using h))
  rw [← h1, TopPair.singularCohomologyMap_comp_apply, h,
    ← TopPair.singularCohomologyMap_comp_apply, ← h2]

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
  have h1 := singularCohomologyMap_slice_eq_of_hasFDerivAt hΦ x ℓ.symm Filter.univ_mem
    hgc.continuousOn hg0 (fun w _ ↦ hgf w) hg hA c
  have h2 := singularCohomologyMap_slice_eq_of_hasFDerivAt hΦ' x ℓ.symm Filter.univ_mem
    hgc.continuousOn hg0 (fun w _ ↦ hgf w) hg hA c
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
  refine TopPair.injective_singularCohomologyMap_excisionMap_of_isClosed_subset (R := R)
    (k := k) (M := M) (X := TopCat.of X) W.isOpen hf
    (range_subset_of_apply_zeroSection f hn hdim Φ hΦ.apply_zeroSection) (finrank ℝ P) ?_
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

/-- **The normal slices of the relative dual class.** Let `Φ` be a normalized tube of `f`,
`x : Z`, and `m : Q ≃ ν_x` a linear isomorphism from a real normed space `Q` of dimension `r`
that carries an orientation `ν` of `Q` to the normal orientation `o x`. The pull-back of
`relDualClass f hn hdim hf o hr` along `m` followed by the normal slice of `Φ` at `x` is the
generator `ν.modelThomGenerator hQ` of `Hʳ(Q, Q ∖ {0}; ℤ)` selected by `ν`. -/
theorem singularCohomologyMap_normalSlice_relDualClass (f : SmoothEmbedding I J ∞ Z X)
    (hn : (∞ : ℕ∞ω) ≠ 0) (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    (hf : IsClosed (range f)) {r : ℕ}
    (o : letI := f.normalSpaceFiberBundle hn hdim
      letI := f.normalSpaceVectorBundle hn hdim
      VectorBundleOrientation P (fun x ↦ f.isImmersion.NormalSpace x hn) (Fin r))
    (hr : finrank ℝ P = r) {W : TopologicalSpace.Opens X}
    {Φ : letI := f.normalSpaceFiberBundle hn hdim
      TotalSpace P (fun x ↦ f.isImmersion.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W}
    (hΦ : f.IsNormalizedTube hn hdim Φ) (x : Z) {Q : Type w} [NormedAddCommGroup Q]
    [NormedSpace ℝ Q] [FiniteDimensional ℝ Q] (ν : Orientation ℝ Q (Fin r))
    (hQ : finrank ℝ Q = r) (m : Q ≃L[ℝ] f.isImmersion.NormalSpace x hn)
    (hm : ν.map (Fin r) m.toLinearEquiv = o x) :
    TopPair.singularCohomologyMap (m.complZeroPairIso.hom ≫
        f.normalSlice hn hdim Φ hΦ.apply_zeroSection x) r (f.relDualClass hn hdim hf o hr) =
      ν.modelThomGenerator hQ := by
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  subst hr
  set e := trivializationAt P (fun x ↦ f.isImmersion.NormalSpace x hn) x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  rw [TopPair.singularCohomologyMap_comp_apply,
    singularCohomologyMap_relDualClass_eq_of_relDualClassOf f hn hdim hf o rfl _ _ _
      ((eq_relDualClassOf_iff_forall_slice f hn hdim hf hΦ _ _).1 rfl x),
    o.singularCohomologyMap_fiberThomPairMap_canonicalThomClass rfl e hx]
  have h : ν.map _ (m.trans (e.continuousLinearEquivAt ℝ x hx)).toLinearEquiv =
      e.mapOrientation _ hx (o x) := by
    rw [Trivialization.mapOrientation_apply, ← hm, ← Orientation.map_trans]
    -- `(e.continuousLinearEquivAt ℝ x hx).toLinearEquiv` is `e.linearEquivAt ℝ x hx`.
    congr 1
  rw [← Orientation.singularCohomologyMap_modelThomGenerator _ ν hQ rfl, h,
    ContinuousLinearEquiv.complZeroPairIso_trans, Iso.trans_hom,
    TopPair.singularCohomologyMap_comp_apply]

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
  have hA (w : P) : f.isImmersion.normalClassL x hn (A w) = m w := by
    refine (hdφ _ hg0' (A' w)).trans ?_
    rw [hA']
    simp [ψ]
  have h1 := singularCohomologyMap_slice_eq_of_hasFDerivAt hΦ x m Filter.univ_mem hgc hg0 hgf
    (hφ.comp 0 hg') hA c
  -- Read on `(univ, univ ∖ {0})` through `ψ = ℓ⁻¹ ∘ m`, the normal slice of `Φ'` followed by `φ`
  -- is `g`.
  have hgi := ofSubsetMap_subtypeVal_comp_complZeroPairIso_hom_comp_normalSlice_comp _ hn hdim Φ'
    hΦ'.apply_zeroSection x ψ (TopPair.ofSubsetMap (X := TopCat.of X') (Y := TopCat.of X)
      (TopCat.ofHom ⟨φ, φ.continuous⟩) (f.mapsTo_compl_range_transDiffeomorph φ)) hgc
    (fun w hw h ↦ hw (hgf w (mem_univ w) h)) fun _ ↦ TopPair.ofSubsetMap_fst_apply _ _ _
  rw [ContinuousLinearEquiv.complZeroPairIso_trans, ContinuousLinearEquiv.complZeroPairIso_symm ℓ,
    Iso.trans_hom, Iso.symm_hom, Category.assoc, Category.assoc] at hgi
  have h3 : TopPair.singularCohomologyMap (ℓ.complZeroPairIso.inv ≫
      (f.transDiffeomorph φ.symm).normalSlice hn hdim Φ' hΦ'.apply_zeroSection x ≫
        TopPair.ofSubsetMap (X := TopCat.of X') (Y := TopCat.of X)
          (TopCat.ofHom ⟨φ, φ.continuous⟩) (f.mapsTo_compl_range_transDiffeomorph φ)) n c =
      TopPair.singularCohomologyMap (f.normalSlice hn hdim Φ hΦ.apply_zeroSection x) n c := by
    refine TopPair.injective_singularCohomologyMap_ofSubsetMap_subtypeVal_univ_comp R k M (0 : P)
      m.complZeroPairIso n ?_
    rw [← TopPair.singularCohomologyMap_comp_apply, Category.assoc, hgi, h1]
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
      VectorBundleOrientation P (fun x ↦ f.isImmersion.NormalSpace x hn) (Fin r))
          (hr : finrank ℝ P = r) :
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
  -- `relDualClassOf_transDiffeomorph` is stated for the `ℤ`-linear structure
  -- `ModuleCat.instLinear`; read both classes for that structure.
  rw [relDualClass_eq_singularCohomologyLinearCongr_relDualClassOf,
    relDualClass_eq_singularCohomologyLinearCongr_relDualClassOf,
    ← TopPair.singularCohomologyLinearCongr_naturality, ← relDualClassOf_transDiffeomorph,
    ← TopPair.singularCohomologyLinearCongr_naturality, transDiffeomorphThomPairMap_def,
    thomPairMapOfComp_def]
  -- The goal agrees with the naturality of the canonical Thom class only up to unfolding
  -- (`thomPairMapOfFiberwise` over `g = ContinuousMap.id Z`), which `rw` does not see.
  congr 3
  exact (o.singularCohomologyMap_thomPairMapOfFiberwise_canonicalThomClass_comap rfl rfl _).symm

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
      VectorBundleOrientation P (fun x ↦ f.isImmersion.NormalSpace x hn) (Fin r))
          (hr : finrank ℝ P = r) :
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
