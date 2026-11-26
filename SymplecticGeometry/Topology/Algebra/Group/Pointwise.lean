/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Points that reach a closed set along a line

Let `A` be a closed set in a normed space `E` over a nontrivially normed field `𝕜` whose closed
balls are compact. The pairs `(c, v)` with `c + s • v ∈ A` for some `‖s‖ ≤ ρ` form a closed set
(`IsClosed.setOfPred_exists_norm_le_fst_add_smul_snd_mem`), by Mathlib's
`isClosedMap_fst_of_compactSpace` for the compact factor `closedBall 0 ρ` of `𝕜`. For a fixed
`v`, the points `c` with `c + s • v ∈ A` for some `‖s‖ ≤ ρ` are the preimage of that set under
`c ↦ (c, v)`, so they form a closed set too (`IsClosed.setOfPred_exists_norm_le_add_smul_mem`).
-/

public section

open Metric Set

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

/-- The points from which a closed set can be reached by a move `s • v` with `‖s‖ ≤ ρ` form a
closed set. -/
theorem IsClosed.setOfPred_exists_norm_le_add_smul_mem {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [ProperSpace 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] {A : Set E} (hA : IsClosed A)
    (v : E) (ρ : ℝ) :
    IsClosed {c : E | ∃ s : 𝕜, ‖s‖ ≤ ρ ∧ c + s • v ∈ A} := by
  simpa only [preimage_ofPred_eq] using
    (hA.setOfPred_exists_norm_le_fst_add_smul_snd_mem (𝕜 := 𝕜) ρ).preimage
      (by fun_prop : Continuous fun c : E ↦ (c, v))

end
