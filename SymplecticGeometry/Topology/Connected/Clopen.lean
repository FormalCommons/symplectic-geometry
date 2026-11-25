/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Connected.Clopen

/-!
# Preconnected sets and clopen sets

A dense subset `s` of a preconnected space is preconnected as soon as every point of the space
has a neighbourhood `t` such that `t ∩ s` is preconnected. Applied to the interior of a manifold
with boundary, this shows that the interior of a connected manifold is connected.

## Main results

* `Dense.isPreconnected_of_forall_exists_mem_nhds`: the criterion above.
* `IsPreconnected.subset_of_isClopen_preimage_val`: a preconnected `s` that meets a set `t` whose
  trace on some `u ⊇ s` is open and closed in `u` lies in `t`.
* `IsPreconnected.inter_of_isClopen_preimage_val`: cutting a preconnected set `s` by a set whose
  trace on some `u ⊇ s` is open and closed in `u` leaves a preconnected set.
* `PreconnectedSpace.eq_zero_of_eventually_eq_zero`: on a preconnected space, let `f` be a
  function such that at every point, zero or not, either `f` vanishes on a neighbourhood or `f`
  has no zero on a punctured neighbourhood. If `f` vanishes near one point, then `f = 0`.

The last result abstracts the open-and-closed argument of Tau Ceti's
`TauCeti.not_eventually_eq_zero_of_conjWirtingerDeriv_apply_one_eq_mul`.
-/

public section

open Set Topology Relation Filter

variable {X : Type*} [TopologicalSpace X]

/-- A dense subset `s` of a preconnected space is preconnected if every point `x` has a
neighbourhood `t` with `t ∩ s` preconnected. The point `x` need not lie in `s`. -/
theorem Dense.isPreconnected_of_forall_exists_mem_nhds [PreconnectedSpace X] {s : Set X}
    (hs : Dense s) (h : ∀ x, ∃ t ∈ 𝓝 x, IsPreconnected (t ∩ s)) : IsPreconnected s := by
  choose t ht hpre using h
  have hU : (⋃ x, t x ∩ s) = s :=
    Subset.antisymm (iUnion_subset fun _ ↦ inter_subset_right)
      fun a ha ↦ mem_iUnion.2 ⟨a, mem_of_mem_nhds (ht a), ha⟩
  -- Two points whose neighbourhoods `t` meet near each other give sets that meet in `s`.
  have hmeet : ∀ x, ∀ᶠ y in 𝓝 x, (t x ∩ s ∩ (t y ∩ s)).Nonempty := fun x ↦ by
    filter_upwards [interior_mem_nhds.2 (ht x)] with y hy
    obtain ⟨z, ⟨hzx, hzy⟩, hz⟩ := hs.inter_open_nonempty (interior (t x) ∩ interior (t y))
      (isOpen_interior.inter isOpen_interior) ⟨y, hy, mem_interior_iff_mem_nhds.2 (ht y)⟩
    exact ⟨z, ⟨interior_subset hzx, hz⟩, interior_subset hzy, hz⟩
  rw [← hU]
  refine IsPreconnected.iUnion_of_reflTransGen hpre fun x y ↦ ?_
  refine PreconnectedSpace.induction₂' _ (fun x ↦ ?_) ⟨fun _ _ _ ↦ ReflTransGen.trans⟩ x y
  filter_upwards [hmeet x] with y hy
  exact ⟨ReflTransGen.single hy, ReflTransGen.single (by rwa [inter_comm])⟩

/-- If `s ⊆ u` is preconnected, the trace of `t` on `u` is open and closed in `u`, and `s` meets
`t`, then `s ⊆ t`. This is `IsPreconnected.subset_isClopen` relative to `u`. -/
theorem IsPreconnected.subset_of_isClopen_preimage_val {s t u : Set X} (hs : IsPreconnected s)
    (hsu : s ⊆ u) (ht : IsClopen ((↑) ⁻¹' t : Set u)) (hne : (s ∩ t).Nonempty) : s ⊆ t := by
  obtain ⟨x, hxs, hxt⟩ := hne
  have hs' : IsPreconnected ((↑) ⁻¹' s : Set u) := by
    rwa [← IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe,
      inter_eq_right.2 hsu]
  have hst := hs'.subset_isClopen ht ⟨⟨x, hsu hxs⟩, hxs, hxt⟩
  exact fun y hy ↦ hst (a := ⟨y, hsu hy⟩) hy

/-- If `s ⊆ u` is preconnected and the trace of `t` on `u` is open and closed in `u`, then
`s ∩ t` is preconnected: it is either empty or all of `s`. -/
theorem IsPreconnected.inter_of_isClopen_preimage_val {s t u : Set X} (hs : IsPreconnected s)
    (hsu : s ⊆ u) (ht : IsClopen ((↑) ⁻¹' t : Set u)) : IsPreconnected (s ∩ t) := by
  rcases (s ∩ t).eq_empty_or_nonempty with h | h
  · rw [h]
    exact isPreconnected_empty
  rwa [inter_eq_left.2 (hs.subset_of_isClopen_preimage_val hsu ht h)]

/-- **Unique continuation from a dichotomy.** On a preconnected space, let `f` be a function
such that at each point `x`, either `f` vanishes on a neighbourhood of `x`, or `f` has no zero on
a punctured neighbourhood of `x`. If `f` vanishes on a neighbourhood of one point, then `f = 0`. -/
theorem PreconnectedSpace.eq_zero_of_eventually_eq_zero [PreconnectedSpace X] {M : Type*}
    [Zero M] {f : X → M}
    (hf : ∀ x, (∀ᶠ y in 𝓝 x, f y = 0) ∨ ∀ᶠ y in 𝓝[≠] x, f y ≠ 0) {z : X}
    (hz : ∀ᶠ y in 𝓝 z, f y = 0) : f = 0 := by
  set S := {x | ∀ᶠ y in 𝓝 x, f y = 0}
  have hS : IsClopen S := by
    refine ⟨isOpen_compl_iff.1 (isOpen_iff_mem_nhds.2 fun x hx ↦ ?_),
      isOpen_setOfPred_eventually_nhds⟩
    filter_upwards [eventually_nhdsWithin_iff.1 ((hf x).resolve_left hx)] with y hy hyS
    obtain rfl | hyx := eq_or_ne y x
    · exact hx hyS
    · exact hy hyx hyS.self_of_nhds
  exact funext fun x ↦ (hS.eq_univ ⟨z, hz⟩ ▸ mem_univ x : x ∈ S).self_of_nhds

end
