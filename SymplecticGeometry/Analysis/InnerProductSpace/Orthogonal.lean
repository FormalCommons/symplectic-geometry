/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthogonal

/-!
# Sums of a vector of `Kᗮ` and a vector of `K`

In an inner product space, a sum `x + y` with `x ∈ Kᗮ` and `y ∈ K` lies in `K` only for `x = 0`,
since `K` and `Kᗮ` are disjoint (`Submodule.add_mem_iff_eq_zero_of_mem_orthogonal`). For the line
`𝕜 ∙ p` this says that a translate `x + s • p` of a vector `x` orthogonal to `p` lies on the line
only for `x = 0` (`Submodule.add_smul_mem_span_singleton_iff`).
-/

public section

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- For `x ∈ Kᗮ` and `y ∈ K`, the sum `x + y` lies in `K` exactly when `x = 0`. -/
theorem add_mem_iff_eq_zero_of_mem_orthogonal {K : Submodule 𝕜 E} {x y : E} (hx : x ∈ Kᗮ)
    (hy : y ∈ K) : x + y ∈ K ↔ x = 0 := by
  rw [K.add_mem_iff_left hy]
  exact ⟨fun h ↦ disjoint_def.1 K.orthogonal_disjoint x h hx, fun h ↦ h ▸ K.zero_mem⟩

/-- A translate `x + s • p` of a vector `x` orthogonal to `p` lies on the line through `p`
exactly when `x = 0`. -/
theorem add_smul_mem_span_singleton_iff (p : E) (x : (𝕜 ∙ p)ᗮ) (s : 𝕜) :
    (x : E) + s • p ∈ 𝕜 ∙ p ↔ x = 0 :=
  (add_mem_iff_eq_zero_of_mem_orthogonal x.property
    (smul_mem _ s (mem_span_singleton_self p))).trans (coe_eq_zero (x := x))

end Submodule

end
