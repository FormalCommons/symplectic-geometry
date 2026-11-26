/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Collar.Global

/-!
# Compact parts of a collar

Let `c : N × [0, 1) → M` be a collar of `f : N → M` (`TauCeti.IsCollar`). Tau Ceti's notion is
purely topological, and so is this file. When `N` is compact, the part `c(N × [0, t])` of the
collar of depth at most `t`, for `t < 1`, is compact, as the image of the compact set
`N × [0, t]` (`TauCeti.IsCollar.isCompact_image_setOfPred_le`). In a Hausdorff space it is therefore
closed, which is how pushing along a collar and homotopy extension along a collar use it.

## Main results

* `TauCeti.IsCollar.isCompact_image_setOfPred_le`: for compact `N` and `t < 1`, the image under a
  collar of the points of depth at most `t` is compact.
-/

public section

namespace TauCeti

open Set

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N] {f : N → M}
  {c : N × Ico (0 : ℝ) 1 → M}

namespace IsCollar

/-- For compact `N` and `t < 1`, the part `c(N × [0, t])` of the collar of depth at most `t` is
compact. -/
theorem isCompact_image_setOfPred_le (hc : IsCollar f c) [CompactSpace N] {t : ℝ} (ht : t < 1) :
    IsCompact (c '' {p | (p.2 : ℝ) ≤ t}) := by
  have hs : IsCompact {s : Ico (0 : ℝ) 1 | (s : ℝ) ≤ t} := by
    rw [Subtype.isCompact_iff]
    convert isCompact_Icc (a := (0 : ℝ)) (b := t) using 1
    ext x
    refine ⟨?_, fun hx ↦ ⟨⟨x, hx.1, hx.2.trans_lt ht⟩, hx.2, rfl⟩⟩
    rintro ⟨s, hs, rfl⟩
    exact ⟨s.property.1, hs⟩
  have hp : {p : N × Ico (0 : ℝ) 1 | (p.2 : ℝ) ≤ t} =
      (univ : Set N) ×ˢ {s : Ico (0 : ℝ) 1 | (s : ℝ) ≤ t} := by
    ext; simp
  rw [hp]
  exact (isCompact_univ.prod hs).image hc.isOpenEmbedding.continuous

end IsCollar

end TauCeti

end
