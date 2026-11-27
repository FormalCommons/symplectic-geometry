/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.Topology.Coherent
import TauCeti.Topology.Category.TopCat.Pushout

/-!
# Pushouts in `TopCat` from covers by interiors

Let `S` and `U` be subsets of a topological space `Y` whose interiors cover `Y`, and let
`A ⊆ Y` be their intersection. Then `Y` is the pushout in `TopCat` of the subspaces `S` and `U`
along `A`, the four maps being the subspace inclusions
(`CategoryTheory.IsPushout.of_interior_union_interior_eq_univ`). This is the counterpart, for a
cover by interiors, of Tau Ceti's
`CategoryTheory.IsPushout.of_isClosedEmbedding_of_range_union_range` for a cover by two closed
subspaces. It applies for instance to a closed set `S` and an open set `U` with
`interior S ∪ U = univ`.

The proof checks the two conditions of Tau Ceti's
`CategoryTheory.IsPushout.of_isPushout_forget`: the underlying square of sets is a pushout, by
Mathlib's `CategoryTheory.Limits.Types.isPushout_of_isPullback_of_mono'`, and the topology of `Y`
is coherent with `S` and `U`, by Mathlib's `Topology.IsCoherentWith.of_nhds`.
-/

public section

open CategoryTheory Set Topology

universe u

namespace CategoryTheory.IsPushout

variable {Y : Type u} [TopologicalSpace Y] {A S U : Set Y}

/-- **A cover by two interiors is a pushout.** Let `S` and `U` be subsets of a topological space
`Y` whose interiors cover `Y`, and let `A` be their intersection. Then the square of subspace
inclusions `A → S`, `A → U`, `S → Y` and `U → Y` is a pushout square in `TopCat`.

For an open set `U`, the hypothesis reads `interior S ∪ U = univ`. -/
theorem of_interior_union_interior_eq_univ (hAS : A ⊆ S) (hAU : A ⊆ U) (hSU : S ∩ U ⊆ A)
    (hcover : interior S ∪ interior U = univ) :
    IsPushout (TopCat.ofHom (ContinuousMap.inclusion hAS))
      (TopCat.ofHom (ContinuousMap.inclusion hAU))
      (TopCat.ofHom (ContinuousMap.subtypeVal S)) (TopCat.ofHom (ContinuousMap.subtypeVal U)) := by
  have hmem (x : Y) : x ∈ interior S ∨ x ∈ interior U := hcover.ge (mem_univ x)
  have hcoh : IsCoherentWith {S, U} := .of_nhds fun x ↦ (hmem x).elim
    (fun hx ↦ ⟨S, by simp, mem_interior_iff_mem_nhds.1 hx⟩)
    (fun hx ↦ ⟨U, by simp, mem_interior_iff_mem_nhds.1 hx⟩)
  refine of_isPushout_forget ?_ fun s hS hU ↦ hcoh.isOpen_iff.2 <| by
    simpa only [mem_insert_iff, mem_singleton_iff, forall_eq_or_imp, forall_eq] using ⟨hS, hU⟩
  have : Mono ((forget TopCat).map (TopCat.ofHom (ContinuousMap.subtypeVal S))) :=
    (mono_iff_injective _).2 Subtype.val_injective
  refine Limits.Types.isPushout_of_isPullback_of_mono' ?_ ?_ ?_
  · refine (Limits.Types.isPullback_iff _ _ _ _).2 ⟨by ext; simp, fun a b h ↦ ?_, fun x y h ↦ ?_⟩
    · exact Subtype.ext (by simpa using congrArg Subtype.val h.1)
    · replace h : (x : Y) = y := by simpa using h
      have hx : (x : Y) ∈ A := hSU ⟨x.property, h ▸ y.property⟩
      exact ⟨⟨x, hx⟩, by ext; simp, by ext; simpa using h⟩
  · refine eq_univ_of_forall fun x ↦ ?_
    rcases hmem x with hx | hx
    · exact Or.inl ⟨⟨x, interior_subset hx⟩, by simp⟩
    · exact Or.inr ⟨⟨x, interior_subset hx⟩, by simp⟩
  · exact fun x y _ _ h ↦ Subtype.val_injective h

end CategoryTheory.IsPushout

end
