/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Algebra.Group.Defs

/-!
# Uniform gaps between two functions on a compact set

* `IsCompact.exists_pos_forall_add_le_of_forall_lt`: if `f < g` on a compact set `s`, with `f` and
  `g` continuous on `s` with values in a nontrivial linearly ordered topological additive group,
  then `f + δ ≤ g` on `s` for some `δ > 0`. It extends Tau Ceti's
  `TauCeti.exists_pos_forall_add_le_of_forall_lt`, which proves this for a finite index type
  under the same order hypotheses, to a compact set. It is also the version on a compact set of
  Tau Ceti's `CircleDeg1Lift.exists_pos_forall_add_le_of_forall_lt`, which compares two lifts
  of circle maps. It follows from `IsCompact.exists_forall_le'` applied to `g - f`.
* `IsCompact.exists_pos_add_le_of_continuousOn`: the case of a real function `g` continuous on a
  compact rectangle `[a, b] × K` and of its values on the side `{b} × K`: if `g (ℓ, r) < g (b, r)`
  for `ℓ ∈ [a, c]` and `r ∈ K`, then `g (ℓ, r) + ε ≤ g (b, r)` there for some `ε > 0`.
* If `f` and `g` are real functions, continuous on a compact set `K`, and `O` is a neighbourhood of
  the points of `K` where `f = g`, then `|f - g|` has a positive lower bound on `K \ O`
  (`IsCompact.exists_pos_forall_le_abs_sub_of_mem_nhdsSet`). It follows from
  `IsCompact.exists_forall_le'` on `K` minus an open set between `K ∩ {f = g}` and `O`.
-/

public section

open Set Topology

/-- If `f` and `g` are continuous on a compact set `s`, with values in a nontrivial linearly
ordered topological additive group, and `f x < g x` for every `x ∈ s`, then `f` stays below `g`
by a uniform margin: there is `δ > 0` with `f x + δ ≤ g x` for every `x ∈ s`. -/
theorem IsCompact.exists_pos_forall_add_le_of_forall_lt {X α : Type*} [TopologicalSpace X]
    [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [Nontrivial α] [TopologicalSpace α]
    [OrderClosedTopology α] [ContinuousSub α] {s : Set X} {f g : X → α} (hs : IsCompact s)
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) (hlt : ∀ x ∈ s, f x < g x) :
    ∃ δ > 0, ∀ x ∈ s, f x + δ ≤ g x := by
  obtain ⟨δ, hδ, h⟩ := hs.exists_forall_le' (hg.sub hf) fun x hx ↦ sub_pos.2 (hlt x hx)
  exact ⟨δ, hδ, fun x hx ↦ le_sub_iff_add_le'.1 (h x hx)⟩

/-- A real function continuous on the compact rectangle `[a, b] × K`, with `K` in a topological
space, that is strictly below its values on the side `{b} × K` over `[a, c] × K`, for some
`c ≤ b`, is below them by a uniform gap there: there is `ε > 0` with `g (ℓ, r) + ε ≤ g (b, r)`
for all `ℓ ∈ [a, c]` and `r ∈ K`. -/
theorem IsCompact.exists_pos_add_le_of_continuousOn {X : Type*} [TopologicalSpace X] {K : Set X}
    {a b c : ℝ} {g : ℝ × X → ℝ} (hK : IsCompact K) (hg : ContinuousOn g (Icc a b ×ˢ K))
    (hcb : c ≤ b) (hlt : ∀ ℓ ∈ Icc a c, ∀ r ∈ K, g (ℓ, r) < g (b, r)) :
    ∃ ε > 0, ∀ ℓ ∈ Icc a c, ∀ r ∈ K, g (ℓ, r) + ε ≤ g (b, r) := by
  have hsub : Icc a c ×ˢ K ⊆ Icc a b ×ˢ K := prod_mono (Icc_subset_Icc_right hcb) subset_rfl
  obtain ⟨ε, hε, hle⟩ := (isCompact_Icc.prod hK).exists_pos_forall_add_le_of_forall_lt
    (hg.mono hsub) (hg.comp (continuous_const.prodMk continuous_snd).continuousOn
      fun x (hx : x ∈ Icc a c ×ˢ K) ↦ ⟨⟨hx.1.1.trans (hx.1.2.trans hcb), le_rfl⟩, hx.2⟩)
    fun x hx ↦ hlt x.1 hx.1 x.2 hx.2
  exact ⟨ε, hε, fun ℓ hℓ r hr ↦ hle (ℓ, r) ⟨hℓ, hr⟩⟩

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
