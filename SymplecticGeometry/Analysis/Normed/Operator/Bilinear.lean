/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Continuous bilinear maps

* `ContinuousLinearMap.opNorm_apply_apply_le`: evaluation at `v`, the continuous linear map
  `ContinuousLinearMap.apply 𝕜 F v` on `E →L[𝕜] F`, has operator norm at most `‖v‖`.
* `ContinuousLinearMap.nonneg_of_forall_notMem_nonneg`: a continuous bilinear form `B` on a real
  normed space with `B v v ≥ 0` for every `v` outside a proper subspace has `B u u ≥ 0` for
  every `u`, since the complement of a proper subspace is dense.
-/

public section

namespace ContinuousLinearMap

section Apply

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Evaluation at `v`, as a continuous linear map on `E →L[𝕜] F`, has operator norm at most
`‖v‖`. -/
theorem opNorm_apply_apply_le (v : E) : ‖apply 𝕜 F v‖ ≤ ‖v‖ :=
  opNorm_le_bound _ (norm_nonneg v) fun A => by
    rw [apply_apply, mul_comm]
    exact A.le_opNorm v

end Apply

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Let `L` be a proper subspace of a real normed space. If a continuous bilinear form `B`
satisfies `B v v ≥ 0` for every `v ∉ L`, then `B u u ≥ 0` for every `u`. -/
theorem nonneg_of_forall_notMem_nonneg {L : Submodule ℝ E} (hL : L ≠ ⊤)
    {B : E →L[ℝ] E →L[ℝ] ℝ} (h : ∀ v ∉ L, 0 ≤ B v v) (u : E) : 0 ≤ B u u := by
  -- The complement of a proper subspace is dense, and `B u u ≥ 0` is a closed condition.
  have hdense : Dense (L : Set E)ᶜ :=
    interior_eq_empty_iff_dense_compl.1
      (Set.not_nonempty_iff_eq_empty.1 fun hi ↦ hL (L.eq_top_of_nonempty_interior' hi))
  have hclosed : IsClosed {u : E | 0 ≤ B u u} :=
    isClosed_le continuous_const (B.continuous.clm_apply continuous_id)
  exact hclosed.closure_subset_iff.2 (fun v hv ↦ h v hv) (hdense.closure_eq ▸ Set.mem_univ u)

end ContinuousLinearMap

end
