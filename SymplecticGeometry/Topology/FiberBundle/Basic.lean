/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.FiberBundle.Basic
public import Mathlib.Topology.Sets.OpenCover
public import TauCeti.Topology.FiberBundle.MapFiber
public import SymplecticGeometry.Topology.FiberBundle.Trivialization
import TauCeti.Topology.FiberBundle.Trivialization

/-!
# Fibre bundles read in their trivializations

Let `E` be a fibre bundle over `B` with model fibre `F`. A set `s` of points of the total space
is open as soon as, in the trivialization at each point `b` of the base, membership in `s` of a
point of the source is membership of its fibre coordinate in one fixed open set `t ⊆ F`. This
is how a fibrewise condition, such as nondegeneracy of the forms in a bundle of bilinear or
alternating maps, is shown to be open: the condition is invariant under the fibre equivalences
of the trivializations and open on the model fibre.

A trivialization `e` whose base set contains `b` also gives the inclusion `f ↦ e⁻¹ (b, f)` of
the model fibre onto the fibre over `b` (`Bundle.Trivialization.fiberInclusionMap`). Read through
two trivializations, these inclusions differ by the coordinate change.

## Main definitions

* `Bundle.Trivialization.fiberInclusionMap`: the inclusion of the model fibre onto the fibre over a
  point of the base set of a trivialization, as a continuous map. Tau Ceti's
  `Bundle.Trivialization.fiberInclusion` is the same inclusion as a morphism of `TopCat`.

## Main results

* `Bundle.Trivialization.leftInverse_snd_fiberInclusionMap` and
  `Bundle.Trivialization.fiberInclusionMap_snd_apply`: the fibre coordinate of a trivialization and
  its fibre inclusion are inverse to each other.
* `Bundle.Trivialization.fiberInclusionMap_coordChange`: the inclusions of a fibre through two
  trivializations differ by their coordinate change;
  `Bundle.Trivialization.coe_fiberInclusionMap_eq_comp_coordChange` says so as an equality of
  functions.
* `Bundle.Trivialization.coe_fiberInclusionMap_transFiberHomeomorph`: changing the fibre of a
  trivialization by a homeomorphism `h` composes its fibre inclusions with the inverse of `h`.
* `Bundle.Trivialization.fiberInclusionMap_transFiberwiseHomeomorph_apply`: following a
  trivialization by a homeomorphism `Φ` of `U × F` over `U` composes its fibre inclusion over
  `b ∈ U` with the fibre of `Φ⁻¹` over `b`.
* `Bundle.Trivialization.coe_fiberInclusionMap_transFiberwiseHomeomorph_symm`: for
  `Φ (p, v) = (p, χ p v)`, following a trivialization by `Φ⁻¹` composes its fibre inclusion over
  `b ∈ U` with `χ b`.
* `Bundle.Trivialization.coordChange_compHomeomorph`: precomposing two trivializations with a
  homeomorphism leaves their coordinate change unchanged.
* `Bundle.Trivialization.compTotalSpaceHomeomorph_refl`: a trivialization transported by Tau
  Ceti's `Bundle.Trivialization.compTotalSpaceHomeomorph` along the identity of the total space
  is itself.
* `TauCeti.MapFiber.Atlas.iUnion_baseSet_trivAt` and
  `TauCeti.MapFiber.Atlas.isOpenCover_baseSet_trivAt`: the base sets of the trivializations of an
  atlas cover the base, as sets and as an open cover.
* `TauCeti.MapFiber.Atlas.trivializationAt_fiberBundleOfHomeomorph_refl` and
  `TauCeti.MapFiber.Atlas.mem_trivializationAtlas_fiberBundleOfHomeomorph_refl_iff`: for an atlas
  of a bundle and the identity of its total space, the fibre bundle structure of Tau Ceti's
  `TauCeti.MapFiber.Atlas.fiberBundleOfHomeomorph` has the trivializations of the atlas as its
  preferred trivializations and as its atlas.
* `FiberBundle.iUnion_baseSet_trivializationAt`: the base sets of the preferred trivializations
  of a fibre bundle cover the base.
* `FiberBundle.isOpen_of_forall_mem_iff_snd_mem`: a set of the total space that every
  trivialization `trivializationAt F E b` reads, on its source, as the preimage of an open set of
  the model fibre under the fibre coordinate, is open.
* `FiberBundle.nonempty_fiber`: the fibres of a fibre bundle with a nonempty model fibre are
  nonempty.
* `ContinuousAt.eventually_mem_baseSet_trivializationAt`: a map into the base of a fibre bundle,
  continuous at `x₀`, takes the points near `x₀` into the base set of the preferred trivialization
  at its value at `x₀`; Tau Ceti's `Bundle.TotalSpace.eventually_proj_mem_baseSet_trivializationAt`
  is the case of the projection.

## Implementation notes

The proof is the trivialization argument of Tau Ceti's `TauCeti.isOpen_zeroSectionCompl`
(`TauCeti/Topology/VectorBundle/ZeroSection.lean`): the preimage of `Prod.snd ⁻¹' t` under a
trivialization is open in its source, by `OpenPartialHomeomorph.isOpen_inter_preimage`.

## References

* D. Husemoller, *Fibre Bundles*, 3rd ed., Graduate Texts in Mathematics 20, Springer, 1994,
  Chapter 4 (general fibre bundles).
-/

public section

open Bundle Topology

namespace Bundle.Trivialization

variable {B F Z : Type*} [TopologicalSpace B] [TopologicalSpace F] [TopologicalSpace Z]
  {proj : Z → B}

/-- The inclusion `f ↦ e⁻¹ (b, f)` of the model fibre `F` onto the fibre over `b` of the
total space, read through a trivialization `e` whose base set contains `b`: the inverse of
`Bundle.Trivialization.preimageSingletonHomeomorph`, followed by the inclusion of the fibre. -/
def fiberInclusionMap (e : Trivialization F proj) {b : B} (hb : b ∈ e.baseSet) : C(F, Z) :=
  (ContinuousMap.subtypeVal (proj ⁻¹' {b})).comp (e.preimageSingletonHomeomorph hb).symm

lemma fiberInclusionMap_apply (e : Trivialization F proj) {b : B} (hb : b ∈ e.baseSet) (f : F) :
    e.fiberInclusionMap hb f = e.toOpenPartialHomeomorph.symm (b, f) :=
  (rfl)

/-- The inclusion of the fibre over `b` lands in the fibre over `b`. -/
lemma proj_fiberInclusionMap (e : Trivialization F proj) {b : B} (hb : b ∈ e.baseSet) (f : F) :
    proj (e.fiberInclusionMap hb f) = b :=
  ((e.preimageSingletonHomeomorph hb).symm f).property

/-- The inclusion of the fibre over `b` is the inverse of `e` on `{b} × F`. -/
lemma coe_fiberInclusionMap (e : Trivialization F proj) {b : B} (hb : b ∈ e.baseSet) :
    ⇑(e.fiberInclusionMap hb) = fun f ↦ e.toOpenPartialHomeomorph.symm (b, f) :=
  funext (e.fiberInclusionMap_apply hb)

/-- The inclusion of the fibre over a point of the base set lands in the source of `e`. -/
lemma fiberInclusionMap_mem_source (e : Trivialization F proj) {b : B} (hb : b ∈ e.baseSet)
    (f : F) : e.fiberInclusionMap hb f ∈ e.source :=
  e.mem_source.2 ((e.proj_fiberInclusionMap hb f).symm ▸ hb)

/-- `e` sends the image of `f` under the fibre inclusion over `b` to `(b, f)`. -/
@[simp]
lemma apply_fiberInclusionMap (e : Trivialization F proj) {b : B} (hb : b ∈ e.baseSet) (f : F) :
    e (e.fiberInclusionMap hb f) = (b, f) := by
  rw [fiberInclusionMap_apply]
  exact e.apply_symm_apply' hb

/-- The fibre coordinate of `e` is a left inverse of the fibre inclusion over `b`. -/
lemma leftInverse_snd_fiberInclusionMap (e : Trivialization F proj) {b : B}
    (hb : b ∈ e.baseSet) : Function.LeftInverse (fun x ↦ (e x).2) (e.fiberInclusionMap hb) :=
  fun f ↦ congrArg Prod.snd (e.apply_fiberInclusionMap hb f)

/-- The fibre inclusion over `proj x` sends the fibre coordinate of `x` in `e` back to `x`. -/
@[simp]
lemma fiberInclusionMap_snd_apply (e : Trivialization F proj) {x : Z}
    (hx : proj x ∈ e.baseSet) : e.fiberInclusionMap hx (e x).2 = x := by
  rw [fiberInclusionMap_apply, e.symm_apply_mk_proj (e.mem_source.2 hx)]

/-- The inclusions of a fibre read through two trivializations differ by the coordinate
change. -/
lemma fiberInclusionMap_coordChange (e₁ e₂ : Trivialization F proj) {b : B} (h₁ : b ∈ e₁.baseSet)
    (h₂ : b ∈ e₂.baseSet) (f : F) :
    e₂.fiberInclusionMap h₂ (e₁.coordChange e₂ b f) = e₁.fiberInclusionMap h₁ f := by
  rw [fiberInclusionMap_apply, fiberInclusionMap_apply, e₁.mk_coordChange e₂ h₁ h₂]
  exact e₂.toOpenPartialHomeomorph.left_inv (e₂.mem_source.2 (by rwa [e₁.proj_symm_apply' h₁]))

/-- The fibre inclusion of `e₁` over `b` is that of `e₂` after the coordinate change from `e₁`
to `e₂` over `b`. -/
lemma coe_fiberInclusionMap_eq_comp_coordChange (e₁ e₂ : Trivialization F proj) {b : B}
    (h₁ : b ∈ e₁.baseSet) (h₂ : b ∈ e₂.baseSet) :
    ⇑(e₁.fiberInclusionMap h₁) = e₂.fiberInclusionMap h₂ ∘ e₁.coordChange e₂ b :=
  funext fun f ↦ (e₁.fiberInclusionMap_coordChange e₂ h₁ h₂ f).symm

/-- The fibre inclusion of a trivialization whose fibre is changed by a homeomorphism `h` is the
fibre inclusion of the original trivialization after the inverse of `h`. -/
theorem coe_fiberInclusionMap_transFiberHomeomorph {F' : Type*} [TopologicalSpace F']
    (e : Trivialization F proj) (h : F ≃ₜ F') {b : B} (hb : b ∈ e.baseSet) :
    ⇑((e.transFiberHomeomorph h).fiberInclusionMap (b := b)
      (by rwa [transFiberHomeomorph_baseSet])) = e.fiberInclusionMap hb ∘ h.symm :=
  funext fun v ↦ by
    rw [fiberInclusionMap_apply, transFiberHomeomorph_symm_apply, Function.comp_apply,
      fiberInclusionMap_apply]

/-- The fibre inclusion over `b ∈ U` of a trivialization `e` followed by a homeomorphism `Φ` of
`U × F` over `U` (`Bundle.Trivialization.transFiberwiseHomeomorph`) is the fibre of `Φ⁻¹` over `b`
followed by the fibre inclusion of `e`. -/
theorem fiberInclusionMap_transFiberwiseHomeomorph_apply (e : Trivialization F proj)
    {U : TopologicalSpace.Opens B} (hU : (U : Set B) ⊆ e.baseSet) (Φ : U × F ≃ₜ U × F)
    (hΦ : ∀ q, (Φ q).1 = q.1) {b : B} (hb : b ∈ U) (v : F) :
    (e.transFiberwiseHomeomorph hU Φ hΦ).fiberInclusionMap (b := b)
      (by rwa [transFiberwiseHomeomorph_baseSet]) v =
      e.fiberInclusionMap (hU hb) (Φ.symm (⟨b, hb⟩, v)).2 := by
  rw [fiberInclusionMap_apply, transFiberwiseHomeomorph_symm_apply, fiberInclusionMap_apply]

/-- If `Φ (p, v) = (p, χ p v)` for a family `χ` of homeomorphisms of `F`, the fibre inclusion
over `b ∈ U` of `e` followed by the inverse of `Φ` is `χ b` followed by the fibre inclusion of
`e`. -/
theorem coe_fiberInclusionMap_transFiberwiseHomeomorph_symm (e : Trivialization F proj)
    {U : TopologicalSpace.Opens B} (hU : (U : Set B) ⊆ e.baseSet) {Φ : U × F ≃ₜ U × F}
    {χ : U → F ≃ₜ F} (hχ : ∀ q, Φ q = (q.1, χ q.1 q.2)) {b : B} (hb : b ∈ U) :
    ⇑(fiberInclusionMap (b := b)
      (e.transFiberwiseHomeomorph hU Φ.symm (Homeomorph.fst_symm_apply_of_apply_eq_prodMk hχ))
      (by rwa [transFiberwiseHomeomorph_baseSet])) =
      e.fiberInclusionMap (hU hb) ∘ χ ⟨b, hb⟩ :=
  funext fun v ↦ by
    rw [fiberInclusionMap_transFiberwiseHomeomorph_apply, Homeomorph.symm_symm, hχ,
      Function.comp_apply]

/-- Precomposing two trivializations with a homeomorphism does not change their coordinate
changes. -/
@[simp]
theorem coordChange_compHomeomorph {Z' : Type*} [TopologicalSpace Z']
    (e e' : Trivialization F proj) (h : Z' ≃ₜ Z) (b : B) :
    (e.compHomeomorph h).coordChange (e'.compHomeomorph h) b = e.coordChange e' b := by
  ext v
  simp [coordChange, Trivialization.compHomeomorph]

/-- A trivialization of a bundle, transported along the identity of its total space, is itself. -/
theorem compTotalSpaceHomeomorph_refl {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
    (e : Trivialization F (π F E)) (hh : ∀ x, (Homeomorph.refl (TotalSpace F E) x).proj = x.proj) :
    e.compTotalSpaceHomeomorph (Homeomorph.refl _) hh = e :=
  Trivialization.ext' _ _
    (OpenPartialHomeomorph.ext _ _ (fun _ ↦ by simp) (fun _ ↦ by simp) (by simp)) (by simp)

end Bundle.Trivialization

namespace TauCeti.MapFiber.Atlas

section Cover

variable {B F Z : Type*} [TopologicalSpace B] [TopologicalSpace F] [TopologicalSpace Z]
  {proj : Z → B} (A : Atlas F proj)

/-- The base sets of the trivializations of an atlas cover the base. -/
@[simp]
theorem iUnion_baseSet_trivAt : ⋃ b, (A.trivAt b).baseSet = Set.univ :=
  Set.eq_univ_of_forall fun b ↦ Set.mem_iUnion.2 ⟨b, A.mem_baseSet_trivAt b⟩

/-- The base sets of the trivializations of an atlas, as open sets of the base, form an open
cover of it. -/
theorem isOpenCover_baseSet_trivAt :
    TopologicalSpace.IsOpenCover fun b ↦
      (⟨(A.trivAt b).baseSet, (A.trivAt b).open_baseSet⟩ : TopologicalSpace.Opens B) :=
  .of_sets (fun b ↦ (A.trivAt b).open_baseSet) A.iUnion_baseSet_trivAt

end Cover

variable {B F : Type*} [TopologicalSpace B] [TopologicalSpace F] {E : B → Type*}
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]

/-- The preferred trivialization at `b` of the fibre bundle structure given by an atlas `A` of a
bundle and the identity of its total space is the trivialization of `A` at `b`. -/
@[simp]
theorem trivializationAt_fiberBundleOfHomeomorph_refl (A : Atlas F (π F E))
    (hE : ∀ b, IsInducing (TotalSpace.mk b : E b → TotalSpace F E)) (b : B) :
    letI := A.fiberBundleOfHomeomorph (Homeomorph.refl _) (fun _ ↦ rfl) hE
    trivializationAt F E b = A.trivAt b :=
  (A.trivializationAt_fiberBundleOfHomeomorph _ _ _ b).trans
    (Trivialization.compTotalSpaceHomeomorph_refl _ _)

/-- The atlas of the fibre bundle structure given by an atlas `A` of a bundle and the identity of
its total space consists of the trivializations of `A`. -/
theorem mem_trivializationAtlas_fiberBundleOfHomeomorph_refl_iff (A : Atlas F (π F E))
    (hE : ∀ b, IsInducing (TotalSpace.mk b : E b → TotalSpace F E))
    (e : Trivialization F (π F E)) :
    letI := A.fiberBundleOfHomeomorph (Homeomorph.refl _) (fun _ ↦ rfl) hE
    e ∈ trivializationAtlas F E ↔ e ∈ Set.range A.trivAt :=
  (A.mem_trivializationAtlas_fiberBundleOfHomeomorph_iff _ _ hE e).trans <| exists_congr fun b ↦
    iff_of_eq (congrArg (· = e) ((A.trivAt b).compTotalSpaceHomeomorph_refl _))

end TauCeti.MapFiber.Atlas

namespace FiberBundle

variable {B F : Type*} {E : B → Type*} [TopologicalSpace B] [TopologicalSpace F]
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]

variable (F E) in
/-- The base sets of the preferred trivializations `trivializationAt F E b` of a fibre bundle
cover its base. -/
@[simp]
theorem iUnion_baseSet_trivializationAt : ⋃ b, (trivializationAt F E b).baseSet = Set.univ :=
  Set.eq_univ_of_forall fun b ↦ Set.mem_iUnion.2 ⟨b, mem_baseSet_trivializationAt F E b⟩

/-- A set `s` of the total space of a fibre bundle is open if there is an open set `t` of the
model fibre such that, for each point `b` of the base, a point `q` of the source of the
trivialization at `b` lies in `s` exactly when its fibre coordinate in that trivialization lies
in `t`. -/
theorem isOpen_of_forall_mem_iff_snd_mem {s : Set (TotalSpace F E)} {t : Set F}
    (ht : IsOpen t)
    (h : ∀ (b : B) (q : TotalSpace F E), q ∈ (trivializationAt F E b).source →
      (q ∈ s ↔ (trivializationAt F E b q).2 ∈ t)) :
    IsOpen s := by
  refine isOpen_iff_forall_mem_open.2 fun p hp ↦ ?_
  let e := trivializationAt F E p.proj
  have hpe : p ∈ e.source := mem_trivializationAt_proj_source
  exact ⟨e.source ∩ e ⁻¹' (Prod.snd ⁻¹' t),
    fun q hq ↦ (h p.proj q hq.1).2 hq.2,
    e.toOpenPartialHomeomorph.isOpen_inter_preimage (ht.preimage continuous_snd),
    hpe, (h p.proj p hpe).1 hp⟩

variable (F E) in
/-- Every fibre of a fibre bundle whose model fibre `F` is nonempty, such as a group, is
nonempty, since it is homeomorphic to `F`.

This is not an instance: `F` does not occur in the conclusion, so instance search could not
find it. -/
theorem nonempty_fiber [Nonempty F] (b : B) : Nonempty (E b) :=
  ⟨(homeomorphAt F E b).symm (Classical.arbitrary F)⟩

end FiberBundle

open Bundle Filter Topology in
/-- A map `f` into the base of a fibre bundle that is continuous at `x₀` takes every point near
`x₀` into the base set of the preferred trivialization at `f x₀`. -/
theorem ContinuousAt.eventually_mem_baseSet_trivializationAt {X B : Type*} (F : Type*)
    (E : B → Type*) [TopologicalSpace X] [TopologicalSpace B] [TopologicalSpace F]
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
    {f : X → B} {x₀ : X} (hf : ContinuousAt f x₀) :
    ∀ᶠ x in 𝓝 x₀, f x ∈ (trivializationAt F E (f x₀)).baseSet :=
  hf.eventually_mem ((trivializationAt F E (f x₀)).open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt' (f x₀)))

end
