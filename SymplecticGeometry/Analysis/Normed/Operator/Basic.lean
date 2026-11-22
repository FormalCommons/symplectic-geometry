/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.RCLike.Basic
public import Mathlib.Analysis.Normed.Ring.Units

/-!
# The Neumann series for a fixed-point equation

On a Banach space, for a continuous linear endomorphism `A` with `‖A‖ < 1`, the equation
`v + A x = x` has the solution `x = (1 - A)⁻¹ v`, with `‖x‖ ≤ ‖v‖ / (1 - ‖A‖)`
(`ContinuousLinearMap.exists_add_apply_eq_of_norm_lt_one`).

These declarations are a part of Tau Ceti's file
`TauCeti/Analysis/Normed/Operator/Basic.lean`, on its main branch, as of the commit
`0fef288e2f0539135f050168f1153e762b0189a8` (Tau Ceti's pull request #40860), and are not yet in
the pinned release. They keep their Tau Ceti names, namespaces, statements and proofs unchanged,
so that moving Tau Ceti past them deletes this file without renames.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

section Inverse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **The Neumann series solves `v + A x = x`.** On a Banach space, if `‖A‖ < 1` then the
equation `v + A x = x` has the solution `x = (1 - A)⁻¹ v`, and `‖x‖ ≤ ‖v‖ / (1 - ‖A‖)`. -/
theorem exists_add_apply_eq_of_norm_lt_one [CompleteSpace E] (v : E) {A : E →L[𝕜] E}
    (hA : ‖A‖ < 1) : ∃ x, v + A x = x ∧ ‖x‖ ≤ ‖v‖ / (1 - ‖A‖) := by
  set u := Units.oneSub A hA
  set x := (↑u⁻¹ : E →L[𝕜] E) v
  have hx : x - A x = v := by
    have h := congr($(u.mul_inv) v)
    rwa [Units.val_oneSub, mul_apply_eq_comp, sub_apply, one_apply_eq_self,
      one_apply_eq_self] at h
  refine ⟨x, by rw [← hx, sub_add_cancel], ?_⟩
  rw [le_div_iff₀ (sub_pos.2 hA), ← hx]
  calc ‖x‖ * (1 - ‖A‖) = ‖x‖ - ‖A‖ * ‖x‖ := by ring
    _ ≤ ‖x‖ - ‖A x‖ := by gcongr; exact le_opNorm A x
    _ ≤ ‖x - A x‖ := norm_sub_norm_le _ _

end Inverse

end ContinuousLinearMap

end
