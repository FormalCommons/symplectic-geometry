/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Open neighbourhoods of closed intervals of the real line

An open set `U ⊆ ℝ` containing the closed interval `[a, b]` contains an open interval
`(a - δ, b + δ)` for some `δ > 0` (`IsOpen.exists_pos_Ioo_subset_of_Icc_subset`): it contains a
half-open interval `(l, a]` to the left of `a` and `[b, u)` to the right of `b`
(`exists_Ioc_subset_of_mem_nhds`, `exists_Ico_subset_of_mem_nhds`). When `b < a` the interval
`[a, b]` is empty, and `δ = (a - b) / 2` makes `(a - δ, b + δ)` empty too.
-/

public section

open Set

/-- An open subset of `ℝ` that contains the closed interval `[a, b]` contains the open interval
`(a - δ, b + δ)` for some `δ > 0`. -/
theorem IsOpen.exists_pos_Ioo_subset_of_Icc_subset {a b : ℝ} {U : Set ℝ} (hU : IsOpen U)
    (h : Icc a b ⊆ U) : ∃ δ > 0, Ioo (a - δ) (b + δ) ⊆ U := by
  rcases lt_or_ge b a with hba | hab
  · refine ⟨(a - b) / 2, by linarith, fun t ht ↦ ?_⟩
    linarith [ht.1, ht.2]
  obtain ⟨l, hl, hlU⟩ := exists_Ioc_subset_of_mem_nhds (hU.mem_nhds (h ⟨le_rfl, hab⟩))
    ⟨a - 1, by linarith⟩
  obtain ⟨u, hu, huU⟩ := exists_Ico_subset_of_mem_nhds (hU.mem_nhds (h ⟨hab, le_rfl⟩))
    ⟨b + 1, by linarith⟩
  refine ⟨min (a - l) (u - b), lt_min (by linarith) (by linarith), fun t ht ↦ ?_⟩
  have := min_le_left (a - l) (u - b)
  have := min_le_right (a - l) (u - b)
  rcases lt_or_ge t a with hta | hat
  · exact hlU ⟨by linarith [ht.1], hta.le⟩
  rcases le_or_gt t b with htb | hbt
  · exact h ⟨hat, htb⟩
  · exact huU ⟨hbt.le, by linarith [ht.2]⟩

end
