/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.Order.Interval.Basic

/-!
# Open neighbourhoods of closed intervals in an ordered field

In a linearly ordered field with the order topology, an open set `U` containing the closed
interval `[a, b]` contains an open interval `(a - δ, b + δ)` for some `δ > 0`
(`IsOpen.exists_pos_Ioo_subset_of_Icc_subset`). This is the symmetric form of Tau Ceti's
`IsOpen.exists_Ioo_subset_of_uIcc_subset`, which gives some open interval `(c, d)` around
`[a, b]` inside `U`; `δ` is the smaller of `a - c` and `d - b`. When `b < a` the interval
`[a, b]` is empty, and `δ = (a - b) / 2` makes `(a - δ, b + δ)` empty too.
-/

public section

open Set

/-- In a linearly ordered field with the order topology, an open set that contains the closed
interval `[a, b]` contains the open interval `(a - δ, b + δ)` for some `δ > 0`. -/
theorem IsOpen.exists_pos_Ioo_subset_of_Icc_subset {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] {a b : 𝕜} {U : Set 𝕜}
    (hU : IsOpen U) (h : Icc a b ⊆ U) : ∃ δ > 0, Ioo (a - δ) (b + δ) ⊆ U := by
  rcases lt_or_ge b a with hba | hab
  · exact ⟨(a - b) / 2, by linarith, fun t ht ↦ by linarith [ht.1, ht.2]⟩
  obtain ⟨c, d, hcd, hs⟩ := hU.exists_Ioo_subset_of_uIcc_subset (uIcc_of_le hab ▸ h)
  have hc := (hcd left_mem_uIcc).1
  have hd := (hcd right_mem_uIcc).2
  refine ⟨min (a - c) (d - b), lt_min (by linarith) (by linarith), fun t ht ↦ hs ⟨?_, ?_⟩⟩
  · linarith [ht.1, min_le_left (a - c) (d - b)]
  · linarith [ht.2, min_le_right (a - c) (d - b)]

end
