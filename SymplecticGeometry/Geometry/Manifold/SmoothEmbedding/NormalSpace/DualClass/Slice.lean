/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.DualClass.Basic
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

open Bundle CategoryTheory Module Set
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

end TauCeti.SmoothEmbedding

end
