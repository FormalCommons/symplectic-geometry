/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
/-!
# Neighbourhoods of a sublevel above a compact band

Let `𝕜` be a linearly ordered field with the order topology, such as `ℝ`, let `f : X → 𝕜` be
continuous, and let the band `f⁻¹[a, b]`, `a < b`, be compact. A neighbourhood of the sublevel
`{f ≤ a}` then contains a larger sublevel `{f ≤ a + ε}` for some `ε > 0`, which may be taken with
`ε ≤ b - a` (`exists_pos_sublevel_subset_of_isCompact_preimage_Icc`). Nothing is assumed of `X`
or of the sublevels themselves, which need not be compact; this is what distinguishes it from Tau
Ceti's `TauCeti.exists_pos_sublevel_subset_of_isCompact_of_mem_nhdsSet`, whose argument through
`IsCompact.exists_forall_le'` it follows.
-/

public section

open Set Topology

/-- If the band `f⁻¹[a, b]`, `a < b`, of a continuous function to a linearly ordered field is
compact, then every neighbourhood of the sublevel `{f ≤ a}` contains a sublevel `{f ≤ a + ε}` for
some `ε` with `0 < ε ≤ b - a`. -/
theorem exists_pos_sublevel_subset_of_isCompact_preimage_Icc {X : Type*} [TopologicalSpace X]
    {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜]
    [OrderTopology 𝕜] {f : X → 𝕜} {a b : 𝕜} {U : Set X} (hf : Continuous f)
    (hab : a < b) (hcompact : IsCompact (f ⁻¹' Icc a b)) (hU : U ∈ 𝓝ˢ {x | f x ≤ a}) :
    ∃ ε > 0, ε ≤ b - a ∧ {x | f x ≤ a + ε} ⊆ U := by
  have hsub : {x | f x ≤ a} ⊆ interior U := subset_interior_iff_mem_nhdsSet.2 hU
  -- On the compact part of the band outside `interior U`, `f` is bounded below by some `c > a`.
  obtain ⟨c, hac, hc⟩ := (hcompact.diff isOpen_interior).exists_forall_le' hf.continuousOn
    fun x hx ↦ lt_of_not_ge fun h ↦ hx.2 (hsub h)
  refine ⟨min (b - a) ((c - a) / 2), lt_min (by linarith) (by linarith),
    min_le_left _ _, fun x hx ↦ interior_subset ?_⟩
  have hx' : f x ≤ a + min (b - a) ((c - a) / 2) := hx
  by_contra hxU
  rcases le_or_gt (f x) a with hxa | hxa
  · exact hxU (hsub hxa)
  have := hc x ⟨⟨hxa.le, by linarith [min_le_left (b - a) ((c - a) / 2)]⟩, hxU⟩
  linarith [min_le_right (b - a) ((c - a) / 2)]

end
