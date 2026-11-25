/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Algebra.Group.Pointwise
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Points that reach a closed set along a line

Let `A` be a closed set in a normed space `E` over a nontrivially normed field `𝕜` whose closed
balls are compact, and `v : E`. The points `c` with `c + s • v ∈ A` for some `‖s‖ ≤ ρ` form a
closed set (`IsClosed.setOf_exists_norm_le_add_smul_mem`): it is the sum of `A` and the compact
image of a closed ball of `𝕜` under `s ↦ -(s • v)`, which is closed by Mathlib's
`IsClosed.add_left_of_isCompact`.
-/

public section

open Metric Set

/-- The points from which a closed set can be reached by a move `s • v` with `‖s‖ ≤ ρ` form a
closed set. -/
theorem IsClosed.setOf_exists_norm_le_add_smul_mem {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [ProperSpace 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] {A : Set E} (hA : IsClosed A)
    (v : E) (ρ : ℝ) :
    IsClosed {c : E | ∃ s : 𝕜, ‖s‖ ≤ ρ ∧ c + s • v ∈ A} := by
  have hD : IsCompact ((fun s : 𝕜 ↦ -(s • v)) '' closedBall 0 ρ) :=
    (isCompact_closedBall 0 ρ).image (by fun_prop)
  convert hA.add_left_of_isCompact hD using 1
  ext c
  simp only [mem_ofPred_eq, Set.mem_add, mem_image, mem_closedBall, dist_zero_right]
  constructor
  · rintro ⟨s, hs, hc⟩
    exact ⟨-(s • v), ⟨s, hs, rfl⟩, c + s • v, hc, by abel⟩
  · rintro ⟨_, ⟨s, hs, rfl⟩, a, ha, rfl⟩
    exact ⟨s, hs, by simpa using ha⟩

end
