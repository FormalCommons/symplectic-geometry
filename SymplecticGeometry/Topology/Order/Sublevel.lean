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
# Open neighbourhoods of a sublevel above a compact band

Let `𝕜` be a linearly ordered field with the order topology, such as `ℝ`, let `f : X → 𝕜` be
continuous, and let the band `f⁻¹[a, b]`, `a < b`, be compact. An open set containing the sublevel
`{f ≤ a}` then contains a larger sublevel `{f ≤ a + ε}` for some `ε > 0`
(`IsOpen.exists_pos_sublevel_subset_of_sublevel_subset`). Nothing is assumed of `X` or of the
sublevels themselves, which need not be compact.
-/

public section

open Set

/-- If the band `f⁻¹[a, b]`, `a < b`, of a continuous function to a linearly ordered field is
compact, then an open set containing the sublevel `{f ≤ a}` contains a sublevel `{f ≤ a + ε}` for
some `ε > 0`. -/
theorem IsOpen.exists_pos_sublevel_subset_of_sublevel_subset {X : Type*} [TopologicalSpace X]
    {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜]
    [OrderTopology 𝕜] {f : X → 𝕜} {a b : 𝕜} {U : Set X} (hU : IsOpen U) (hf : Continuous f)
    (hab : a < b) (hcompact : IsCompact (f ⁻¹' Icc a b)) (hsub : {x | f x ≤ a} ⊆ U) :
    ∃ ε > 0, {x | f x ≤ a + ε} ⊆ U := by
  -- The points of the band outside `U` form a compact set on which `f > a`.
  rcases (f ⁻¹' Icc a b \ U).eq_empty_or_nonempty with hK0 | hKne
  · refine ⟨b - a, by linarith, fun x hx ↦ ?_⟩
    by_contra hxU
    rcases le_or_gt (f x) a with hxa | hxa
    · exact hxU (hsub hxa)
    · have : x ∈ f ⁻¹' Icc a b \ U := ⟨⟨hxa.le, by simpa using hx⟩, hxU⟩
      simp [hK0] at this
  obtain ⟨x₀, hx₀, hmin⟩ := (hcompact.diff hU).exists_isMinOn hKne hf.continuousOn
  have hx₀a : a < f x₀ := lt_of_not_ge fun h ↦ hx₀.2 (hsub h)
  set ε := min (b - a) ((f x₀ - a) / 2)
  have hεb : ε ≤ b - a := min_le_left _ _
  have hεx₀ : ε ≤ (f x₀ - a) / 2 := min_le_right _ _
  refine ⟨ε, lt_min (by linarith) (by linarith), fun x hx ↦ ?_⟩
  have hx' : f x ≤ a + ε := hx
  by_contra hxU
  rcases le_or_gt (f x) a with hxa | hxa
  · exact hxU (hsub hxa)
  have : f x₀ ≤ f x := hmin ⟨⟨hxa.le, by linarith⟩, hxU⟩
  linarith

end
