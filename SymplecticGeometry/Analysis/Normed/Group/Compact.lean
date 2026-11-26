/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Topology.Order.Compact

/-!
# Gaps in the norms of a compact set

If no point of a compact subset `K` of a seminormed group has norm `r`, then `K` also misses a
whole annulus `r ≤ ‖z‖ < m` with `r < m` (`IsCompact.exists_lt_forall_norm_lt_or_le`): take for
`m` the least norm of a point of `K` of norm at least `r`.
-/

public section

/-- If no point of the compact set `K` has norm `r`, then for some `m > r` no point of `K` has
norm in `[r, m)`. -/
theorem IsCompact.exists_lt_forall_norm_lt_or_le {E : Type*} [SeminormedAddCommGroup E]
    {K : Set E} (hK : IsCompact K) {r : ℝ} (h : ∀ z ∈ K, ‖z‖ ≠ r) :
    ∃ m, r < m ∧ ∀ z ∈ K, ‖z‖ < r ∨ m ≤ ‖z‖ := by
  set S := K ∩ {z | r ≤ ‖z‖}
  have hS : IsCompact S := hK.inter_right (isClosed_le (by fun_prop) (by fun_prop))
  rcases S.eq_empty_or_nonempty with hS₀ | hS₀
  · refine ⟨r + 1, by linarith, fun z hz ↦ Or.inl (not_le.mp fun hz' ↦ ?_)⟩
    exact (Set.eq_empty_iff_forall_notMem.mp hS₀) z ⟨hz, hz'⟩
  · obtain ⟨z₀, ⟨hz₀, hz₀'⟩, hmin⟩ := hS.exists_isMinOn hS₀ continuous_norm.continuousOn
    refine ⟨‖z₀‖, lt_of_le_of_ne hz₀' (h z₀ hz₀).symm, fun z hz ↦ ?_⟩
    rcases lt_or_ge ‖z‖ r with hz' | hz'
    · exact Or.inl hz'
    · exact Or.inr (hmin ⟨hz, hz'⟩)

end
