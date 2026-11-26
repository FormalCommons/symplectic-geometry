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
closed set (`IsClosed.setOfPred_exists_norm_le_add_smul_mem`): it is the sum of `A` and the compact
image of a closed ball of `𝕜` under `s ↦ -(s • v)`, which is closed by Mathlib's
`IsClosed.add_left_of_isCompact`. The pairs `(c, v)` with `c + s • v ∈ A` for some `‖s‖ ≤ ρ`
also form a closed set (`IsClosed.setOfPred_exists_norm_le_fst_add_smul_snd_mem`), by Mathlib's
`isClosedMap_fst_of_compactSpace` for the compact factor `closedBall 0 ρ` of `𝕜`.
-/

public section

open Metric Set

/-- The points from which a closed set can be reached by a move `s • v` with `‖s‖ ≤ ρ` form a
closed set. -/
theorem IsClosed.setOfPred_exists_norm_le_add_smul_mem {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
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

/-- The pairs `(c, v)` from which a closed set can be reached by a move `s • v` with `‖s‖ ≤ ρ`
form a closed set. -/
theorem IsClosed.setOfPred_exists_norm_le_fst_add_smul_snd_mem {𝕜 E : Type*}
    [NontriviallyNormedField 𝕜] [ProperSpace 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {A : Set E} (hA : IsClosed A) (ρ : ℝ) :
    IsClosed {q : E × E | ∃ s : 𝕜, ‖s‖ ≤ ρ ∧ q.1 + s • q.2 ∈ A} := by
  have : CompactSpace (closedBall (0 : 𝕜) ρ) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall 0 ρ)
  convert isClosedMap_fst_of_compactSpace (X := E × E) (Y := closedBall (0 : 𝕜) ρ) _
    (hA.preimage (f := fun q : (E × E) × closedBall (0 : 𝕜) ρ ↦ q.1.1 + (q.2 : 𝕜) • q.1.2)
      (by fun_prop)) using 1
  ext q
  simp only [mem_ofPred_eq, mem_image, mem_preimage, Prod.exists, exists_and_right,
    exists_eq_right, Subtype.exists, mem_closedBall, dist_zero_right, exists_prop]

end
