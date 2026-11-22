/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import TauCeti.Analysis.Calculus.ContDiff.Matrix

/-!
# Smoothness of the entries of an inverse matrix

By Cramer's rule, the entries of `M⁻¹` are those of the adjugate of `M` divided by `det M`, so
they are polynomials in the entries of `M` divided by `det M`. Hence a matrix-valued map whose
entries are `C^n` on a set, and whose determinant does not vanish there, has an inverse with
`C^n` entries there (`ContDiffOn.matrix_inv_apply`). It is the `C^n` counterpart of Mathlib's
`continuousAt_matrix_inv`, and follows from Tau Ceti's `ContDiffOn.matrix_det`.
-/

public section

variable {𝕜 E ι : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [Fintype ι] [DecidableEq ι] {n : WithTop ℕ∞} {s : Set E}

/-- A matrix-valued map whose entries are `C^n` on a set, and whose determinant does not vanish
there, has an inverse whose entries are `C^n` there. -/
theorem ContDiffOn.matrix_inv_apply {M : E → Matrix ι ι 𝕜}
    (hM : ∀ i j, ContDiffOn 𝕜 n (fun x ↦ M x i j) s) (hdet : ∀ x ∈ s, (M x).det ≠ 0) (i j : ι) :
    ContDiffOn 𝕜 n (fun x ↦ (M x)⁻¹ i j) s := by
  simp_rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply, smul_eq_mul,
    Ring.inverse_eq_inv']
  refine ((ContDiffOn.matrix_det hM).inv hdet).mul (ContDiffOn.matrix_det fun i' j' ↦ ?_)
  rcases eq_or_ne i' j with rfl | h
  · simpa using contDiffOn_const
  · simpa [Matrix.updateRow_ne h] using hM i' j'

end
