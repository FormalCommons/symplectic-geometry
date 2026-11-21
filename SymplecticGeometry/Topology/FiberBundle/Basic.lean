/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.FiberBundle.Basic

/-!
# Open sets of a fibre bundle read in its trivializations

Let `E` be a fibre bundle over `B` with model fibre `F`. A set `s` of points of the total space
is open as soon as, in the trivialization at each point `b` of the base, membership in `s` of a
point of the source is membership of its fibre coordinate in one fixed open set `t ⊆ F`. This
is how a fibrewise condition, such as nondegeneracy of the forms in a bundle of bilinear or
alternating maps, is shown to be open: the condition is invariant under the fibre equivalences
of the trivializations and open on the model fibre.

## Main results

* `FiberBundle.isOpen_of_forall_mem_iff_snd_mem`: a set of the total space that every
  trivialization `trivializationAt F E b` reads, on its source, as the preimage of an open set of
  the model fibre under the fibre coordinate, is open.

## Implementation notes

The proof is the trivialization argument of Tau Ceti's `TauCeti.isOpen_zeroSectionCompl`
(`TauCeti/Topology/VectorBundle/EulerClass.lean`): the preimage of `Prod.snd ⁻¹' t` under a
trivialization is open in its source, by `ContinuousOn.isOpen_inter_preimage`.

## References

* D. Husemoller, *Fibre Bundles*, 3rd ed., Graduate Texts in Mathematics 20, Springer, 1994,
  Chapter 4 (general fibre bundles).
-/

public section

open Bundle Topology

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

end FiberBundle

end
