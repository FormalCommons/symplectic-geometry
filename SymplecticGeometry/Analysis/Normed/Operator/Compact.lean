/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
import TauCeti.Analysis.Normed.Operator.Compact.Interpolation
import TauCeti.Analysis.Normed.Operator.Compact.Pi

/-!
# Operators dominated by finitely many compact operators

A linear map `T` into a Banach space whose norm is bounded by a finite combination
`‖T x‖ ≤ ∑ i, C i * ‖S i x‖` of the norms of compact operators `S i` is compact
(`IsCompactOperator.of_norm_le_sum`). The family `x ↦ (S i x)ᵢ` is compact by Tau Ceti's
`IsCompactOperator.pi`, and it dominates `T`, so this is the case `θ = 0` of Tau Ceti's
interpolation criterion `IsCompactOperator.of_norm_le_mul_rpow_mul_rpow`.

## References

* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., proof of Theorem 6.3.
-/

public section

namespace IsCompactOperator

variable {𝕜 X Y ι : Type*} [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup X]
  [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y] [Fintype ι]
  {F : ι → Type*} [∀ i, SeminormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]

/-- **Domination by compact operators.** A linear map `T` into a Banach space with
`‖T x‖ ≤ ∑ i, C i * ‖S i x‖` for all `x`, for finitely many compact operators `S i`, is
compact. -/
theorem of_norm_le_sum {S : ∀ i, X →ₗ[𝕜] F i} (hS : ∀ i, IsCompactOperator (S i))
    {T : X →ₗ[𝕜] Y} (C : ι → ℝ) (hT : ∀ x, ‖T x‖ ≤ ∑ i, C i * ‖S i x‖) :
    IsCompactOperator T := by
  refine of_norm_le_mul_rpow_mul_rpow (T₀ := LinearMap.pi S) (IsCompactOperator.pi hS)
    (ContinuousLinearMap.id 𝕜 X) (C := ∑ i, |C i|) le_rfl zero_lt_one fun x ↦ ?_
  rw [sub_zero, Real.rpow_one, Real.rpow_zero, mul_one, Finset.sum_mul]
  refine (hT x).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  exact mul_le_mul (le_abs_self _) (norm_le_pi_norm (LinearMap.pi S x) i) (norm_nonneg _)
    (abs_nonneg _)

end IsCompactOperator

end
