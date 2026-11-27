/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.Dimension.Covering
import Mathlib.Topology.ShrinkingLemma

/-!
# Shrinking a finite cover of a closed set of bounded covering dimension

Tau Ceti's `TauCeti.HasCoveringDimensionLE.exists_shrinking_of_isClosed` turns an open cover of a
space `X` into a shrinking whose order is at most `d + 1` at the points of a closed set `K` with
`HasCoveringDimensionLE K d`, with no control elsewhere. In a normal space, for a finite family
of open sets covering `K`, this file bounds the order at every point of `X`: shrink the family so
that the closures of its members still lie in the old ones, and remove the closed set of points
that lie in the closures of `d + 2` members. That set misses `K`, so what remains still covers
`K`.

## Main declarations

* `TauCeti.HasCoveringDimensionLE.exists_shrinking_of_subset_iUnion`: in a normal space, a finite
  family of open sets covering a closed set `K` with `HasCoveringDimensionLE K d` has an open
  shrinking still covering `K` in which every point of `X` lies in at most `d + 1` members.

## References

* J. R. Munkres, *Topology*, 2nd ed., Prentice Hall, 2000, §50 (covering dimension)
-/

public section

open Set

namespace TauCeti

variable {X : Type*} [TopologicalSpace X]

/-- In a normal space, let `K` be a closed set with `HasCoveringDimensionLE K d` and `U` a finite
family of open sets whose union contains `K`. Then there are open sets `V i ⊆ U i` whose union
still contains `K`, such that every point of `X` lies in at most `d + 1` of them. -/
theorem HasCoveringDimensionLE.exists_shrinking_of_subset_iUnion [NormalSpace X] {K : Set X}
    (hK : IsClosed K) {d : ℕ} (h : HasCoveringDimensionLE K d) {ι : Type*} [Finite ι]
    {U : ι → Set X} (hUo : ∀ i, IsOpen (U i)) (hKU : K ⊆ ⋃ i, U i) :
    ∃ V : ι → Set X, (∀ i, IsOpen (V i)) ∧ (∀ i, V i ⊆ U i) ∧ K ⊆ ⋃ i, V i ∧
      ∀ x, {i | x ∈ V i}.encard ≤ ((d + 1 : ℕ) : ℕ∞) := by
  -- Add `Kᶜ` to get a cover of `X`, and shrink it with order at most `d + 1` on `K`.
  obtain ⟨W, hWo, hWU, hWc, hWm⟩ := h.exists_shrinking_of_isClosed hK
    (U := fun j : Option ι => j.elim Kᶜ U) (fun j => j.rec hK.isOpen_compl hUo)
    (eq_univ_of_forall fun x => by
      by_cases hx : x ∈ K
      · obtain ⟨i, hi⟩ := mem_iUnion.1 (hKU hx)
        exact mem_iUnion.2 ⟨some i, hi⟩
      · exact mem_iUnion.2 ⟨none, hx⟩)
  have hKW : K ⊆ ⋃ i, W (some i) := fun x hx => by
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hWc ▸ mem_univ x)
    cases j with
    | none => exact absurd hx (hWU none hj)
    | some i => exact mem_iUnion.2 ⟨i, hj⟩
  obtain ⟨v, hKv, hvo, hvW⟩ := exists_subset_iUnion_closure_subset hK
    (u := fun i => W (some i)) (fun i => hWo _) (fun _ _ => toFinite _) hKW
  -- `B` is the closed set of points in the closures of `d + 2` of the `v i`.
  set B : Set X := ⋃ T : {T : Set ι // T.encard = ((d + 2 : ℕ) : ℕ∞)}, ⋂ i ∈ T.val, closure (v i)
  have hB : IsClosed B := isClosed_iUnion_of_finite fun T => isClosed_biInter fun _ _ =>
    isClosed_closure
  have hmemB : ∀ x, ¬ {i | x ∈ closure (v i)}.encard ≤ ((d + 1 : ℕ) : ℕ∞) → x ∈ B := by
    intro x hx
    obtain ⟨T, hT, hTc⟩ := exists_subset_encard_eq (Order.add_one_le_of_lt (not_le.1 hx))
    exact mem_iUnion.2 ⟨⟨T, by rw [hTc]; push_cast; ring⟩, mem_iInter₂.2 fun i hi => hT hi⟩
  have hKB : ∀ x ∈ K, x ∉ B := by
    intro x hx hxB
    obtain ⟨⟨T, hTc⟩, hxT⟩ := mem_iUnion.1 hxB
    have hle := (encard_le_encard (s := some '' T) (t := {j | x ∈ W j}) (by
      rintro _ ⟨i, hi, rfl⟩
      exact hvW i (mem_iInter₂.1 hxT i hi))).trans (hWm x hx)
    rw [Option.some_injective _ |>.encard_image, hTc] at hle
    exact absurd (ENat.natCast_le_natCast.1 hle) (by omega)
  refine ⟨fun i => v i \ B, fun i => (hvo i).sdiff hB,
    fun i => sdiff_subset.trans (subset_closure.trans ((hvW i).trans (hWU (some i)))),
    fun x hx => ?_, fun x => ?_⟩
  · obtain ⟨i, hi⟩ := mem_iUnion.1 (hKv hx)
    exact mem_iUnion.2 ⟨i, hi, hKB x hx⟩
  · by_contra hx
    beta_reduce at hx
    have hsub : {i | x ∈ v i \ B} ⊆ {i | x ∈ closure (v i)} := fun j hj => subset_closure hj.1
    obtain ⟨i, hi⟩ : {i | x ∈ v i \ B}.Nonempty := by
      by_contra hne
      rw [not_nonempty_iff_eq_empty] at hne
      exact hx (by rw [hne, encard_empty]; exact zero_le)
    exact hi.2 (hmemB x fun hle => hx ((encard_le_encard hsub).trans hle))

end TauCeti

end
