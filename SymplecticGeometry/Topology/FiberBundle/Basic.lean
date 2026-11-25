/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.FiberBundle.Basic

/-!
# Fibre bundles read in their trivializations

Let `E` be a fibre bundle over `B` with model fibre `F`. A set `s` of points of the total space
is open as soon as, in the trivialization at each point `b` of the base, membership in `s` of a
point of the source is membership of its fibre coordinate in one fixed open set `t ⊆ F`. This
is how a fibrewise condition, such as nondegeneracy of the forms in a bundle of bilinear or
alternating maps, is shown to be open: the condition is invariant under the fibre equivalences
of the trivializations and open on the model fibre.

A trivialization `e` whose base set contains `b` also gives the inclusion `f ↦ e⁻¹ (b, f)` of
the model fibre onto the fibre over `b` (`Bundle.Trivialization.fiberInclusion`). Read through
two trivializations, these inclusions differ by the coordinate change.

## Main definitions

* `Bundle.Trivialization.fiberInclusion`: the inclusion of the model fibre onto the fibre over a
  point of the base set of a trivialization.

## Main results

* `Bundle.Trivialization.fiberInclusion_coordChange`: the inclusions of a fibre through two
  trivializations differ by their coordinate change.
* `Bundle.Trivialization.coordChange_compHomeomorph`: precomposing two trivializations with a
  homeomorphism leaves their coordinate change unchanged.
* `FiberBundle.isOpen_of_forall_mem_iff_snd_mem`: a set of the total space that every
  trivialization `trivializationAt F E b` reads, on its source, as the preimage of an open set of
  the model fibre under the fibre coordinate, is open.
* `FiberBundle.nonempty_fiber`: the fibres of a fibre bundle with a nonempty model fibre are
  nonempty.

## Implementation notes

The proof is the trivialization argument of Tau Ceti's `TauCeti.isOpen_zeroSectionCompl`
(`TauCeti/Topology/VectorBundle/ZeroSection.lean`): the preimage of `Prod.snd ⁻¹' t` under a
trivialization is open in its source, by `ContinuousOn.isOpen_inter_preimage`.

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
def fiberInclusion (e : Trivialization F proj) {b : B} (hb : b ∈ e.baseSet) : C(F, Z) :=
  (ContinuousMap.subtypeVal (proj ⁻¹' {b})).comp (e.preimageSingletonHomeomorph hb).symm

lemma fiberInclusion_apply (e : Trivialization F proj) {b : B} (hb : b ∈ e.baseSet) (f : F) :
    e.fiberInclusion hb f = e.toOpenPartialHomeomorph.symm (b, f) :=
  (rfl)

/-- The inclusion of the fibre over `b` lands in the fibre over `b`. -/
lemma proj_fiberInclusion (e : Trivialization F proj) {b : B} (hb : b ∈ e.baseSet) (f : F) :
    proj (e.fiberInclusion hb f) = b :=
  ((e.preimageSingletonHomeomorph hb).symm f).property

/-- The inclusions of a fibre read through two trivializations differ by the coordinate
change. -/
lemma fiberInclusion_coordChange (e₁ e₂ : Trivialization F proj) {b : B} (h₁ : b ∈ e₁.baseSet)
    (h₂ : b ∈ e₂.baseSet) (f : F) :
    e₂.fiberInclusion h₂ (e₁.coordChange e₂ b f) = e₁.fiberInclusion h₁ f := by
  rw [fiberInclusion_apply, fiberInclusion_apply, e₁.mk_coordChange e₂ h₁ h₂]
  exact e₂.toOpenPartialHomeomorph.left_inv (e₂.mem_source.2 (by rwa [e₁.proj_symm_apply' h₁]))

/-- Precomposing two trivializations with a homeomorphism does not change their coordinate
changes. -/
@[simp]
theorem coordChange_compHomeomorph {Z' : Type*} [TopologicalSpace Z']
    (e e' : Trivialization F proj) (h : Z' ≃ₜ Z) (b : B) :
    (e.compHomeomorph h).coordChange (e'.compHomeomorph h) b = e.coordChange e' b := by
  ext v
  simp [coordChange, Trivialization.compHomeomorph]

end Bundle.Trivialization

namespace FiberBundle

variable {B F : Type*} {E : B → Type*} [TopologicalSpace B] [TopologicalSpace F]
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]

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
    e.continuousOn.isOpen_inter_preimage e.open_source (ht.preimage continuous_snd),
    hpe, (h p.proj p hpe).1 hp⟩

variable (F E) in
/-- Every fibre of a fibre bundle whose model fibre `F` is nonempty, such as a group, is
nonempty, since it is homeomorphic to `F`.

This is not an instance: `F` does not occur in the conclusion, so instance search could not
find it. -/
theorem nonempty_fiber [Nonempty F] (b : B) : Nonempty (E b) :=
  ⟨(homeomorphAt F E b).symm (Classical.arbitrary F)⟩

end FiberBundle

end
