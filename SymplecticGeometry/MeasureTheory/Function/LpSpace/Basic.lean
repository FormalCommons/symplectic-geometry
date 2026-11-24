/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Composition with continuous linear maps in `Lᵖ`

If continuous linear maps `Pᵢ : F → G` and `Qᵢ : G → F`, with `‖Qᵢ‖ ≤ 1`, decompose the identity
of `F` as `∑ᵢ Qᵢ ∘ Pᵢ`, then the `Lᵖ` norm of `f` is at most the sum of the `Lᵖ` norms of the
`Pᵢ ∘ f` (`MeasureTheory.Lp.norm_le_sum_norm_compLp`). For an orthonormal basis, `Pᵢ` is the
`i`-th coordinate and `Qᵢ` the inclusion of the `i`-th line.
-/

public section

open MeasureTheory

namespace MeasureTheory.Lp

variable {α 𝕜 F G : Type*} [MeasurableSpace α] {μ : Measure α} {p : ENNReal} [Fact (1 ≤ p)]
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G]
  [NormedSpace 𝕜 G] {ι : Type*} [Fintype ι]

/-- If `∑ᵢ Qᵢ ∘ Pᵢ` is the identity of `F` and every `Qᵢ` has norm at most one, then the `Lᵖ` norm
of `f` is at most the sum of the `Lᵖ` norms of the `Pᵢ f`. -/
theorem norm_le_sum_norm_compLp (P : ι → F →L[𝕜] G) (Q : ι → G →L[𝕜] F)
    (hPQ : ∀ x, ∑ i, Q i (P i x) = x) (hQ : ∀ i, ‖Q i‖ ≤ 1) (f : Lp F p μ) :
    ‖f‖ ≤ ∑ i, ‖(P i).compLp f‖ := by
  have hf : f = ∑ i, (Q i).compLp ((P i).compLp f) := by
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ fun i => (Q i).compLp ((P i).compLp f),
      ae_all_iff.2 fun i => (Q i).coeFn_compLp ((P i).compLp f),
      ae_all_iff.2 fun i => (P i).coeFn_compLp f] with x hs hQx hPx
    rw [hs]
    simp only [hQx, hPx, hPQ]
  calc ‖f‖ = ‖∑ i, (Q i).compLp ((P i).compLp f)‖ := congrArg _ hf
    _ ≤ ∑ i, ‖(Q i).compLp ((P i).compLp f)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖(P i).compLp f‖ := Finset.sum_le_sum fun i _ =>
        ((Q i).norm_compLp_le _).trans (mul_le_of_le_one_left (norm_nonneg _) (hQ i))

end MeasureTheory.Lp

end
