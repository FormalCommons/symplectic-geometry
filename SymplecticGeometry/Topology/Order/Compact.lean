/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Uniform gaps between two real functions on a compact set

* `IsCompact.exists_pos_forall_add_le_of_forall_lt`: if `f < g` on a compact set `s`, with `f` and
  `g` continuous on `s`, then `f + δ ≤ g` on `s` for some `δ > 0`. It is the version on a compact
  set of Tau Ceti's `CircleDeg1Lift.exists_pos_forall_add_le_of_forall_lt`, which compares two
  lifts of circle maps, and follows from `IsCompact.exists_forall_le'` applied to `g - f`.
* If `f` and `g` are real functions, continuous on a compact set `K`, and `O` is a neighbourhood of
  the points of `K` where `f = g`, then `|f - g|` has a positive lower bound on `K \ O`
  (`IsCompact.exists_pos_forall_le_abs_sub_of_mem_nhdsSet`). It follows from
  `IsCompact.exists_forall_le'` on `K` minus an open set between `K ∩ {f = g}` and `O`.
-/

public section

open Set Topology

/-- If `f` and `g` are real functions continuous on a compact set `s`, with `f x < g x` for every
`x ∈ s`, then `f` stays below `g` by a uniform margin: there is `δ > 0` with `f x + δ ≤ g x` for
every `x ∈ s`. -/
theorem IsCompact.exists_pos_forall_add_le_of_forall_lt {X : Type*} [TopologicalSpace X]
    {s : Set X} {f g : X → ℝ} (hs : IsCompact s) (hf : ContinuousOn f s)
    (hg : ContinuousOn g s) (hlt : ∀ x ∈ s, f x < g x) :
    ∃ δ > 0, ∀ x ∈ s, f x + δ ≤ g x := by
  obtain ⟨δ, hδ, h⟩ := hs.exists_forall_le' (hg.sub hf) fun x hx ↦ sub_pos.2 (hlt x hx)
  exact ⟨δ, hδ, fun x hx ↦ le_sub_iff_add_le'.1 (h x hx)⟩

/-- If `f` and `g` are real functions continuous on a compact set `K`, and `O` is a neighbourhood
of the points of `K` where they agree, then `|f - g|` is bounded below on `K \ O` by some
`β > 0`. -/
theorem IsCompact.exists_pos_forall_le_abs_sub_of_mem_nhdsSet {X : Type*} [TopologicalSpace X]
    {K O : Set X} {f g : X → ℝ} (hK : IsCompact K) (hf : ContinuousOn f K)
    (hg : ContinuousOn g K) (hO : O ∈ 𝓝ˢ (K ∩ {x | f x = g x})) :
    ∃ β > 0, ∀ x ∈ K \ O, β ≤ |f x - g x| := by
  obtain ⟨U, hU, hDU, hUO⟩ := mem_nhdsSet_iff_exists.1 hO
  obtain ⟨β, hβ, h⟩ := (hK.diff hU).exists_forall_le' ((hf.sub hg).abs.mono sdiff_subset)
    fun x hx ↦ abs_pos.2 (sub_ne_zero.2 fun h ↦ hx.2 (hDU ⟨hx.1, h⟩))
  exact ⟨β, hβ, fun x hx ↦ h x ⟨hx.1, fun h ↦ hx.2 (hUO h)⟩⟩

end
