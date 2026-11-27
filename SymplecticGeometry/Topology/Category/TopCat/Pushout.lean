/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Types.Multicoequalizer
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
Mathlib's `CategoryTheory.Limits.Types.isPushout_of_bicartSq` for the bicartesian square
`Lattice.BicartSq A S U univ`, and the topology of `Y` is coherent with `S` and `U`, by Mathlib's
`Topology.IsCoherentWith.of_nhds`.
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
  have hsq : Lattice.BicartSq A S U univ :=
    ⟨univ_subset_iff.1 fun x _ ↦ (hmem x).imp (interior_subset ·) (interior_subset ·),
      subset_antisymm hSU (subset_inter hAS hAU)⟩
  exact IsPushout.of_iso (Limits.Types.isPushout_of_bicartSq hsq) (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (Equiv.Set.univ Y).toIso rfl rfl rfl rfl

end CategoryTheory.IsPushout

end
