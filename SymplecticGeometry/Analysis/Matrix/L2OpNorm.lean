/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Smoothness of matrix-valued maps under the ℓ² operator norm

Mathlib puts no global norm on `Matrix m n 𝕜`: the entrywise norm
`Matrix.Norms.Elementwise` and the ℓ² operator norm `Matrix.Norms.L2Operator` are scoped
instances, and `ContDiff 𝕜 k f` for a map `f : E → Matrix m n 𝕜` is a statement about the
normed structure that is open. Under the entrywise norm, `contDiff_pi` says that `f` is `C^k`
exactly when every entry `fun x ↦ f x i j` is. This file proves the same under the ℓ² operator
norm, so that smoothness of a matrix-valued map does not depend on which of the two norms is
open (`Matrix.contDiff_l2Op_iff_contDiff_elementwise`).

Mathlib builds the ℓ² operator norm so that its topology is the entrywise topology of
`Matrix m n 𝕜`. The linear equivalence `(Matrix.ofLinearEquiv 𝕜).symm` with `m → n → 𝕜` is
between finite-dimensional spaces, hence a continuous linear equivalence
(`LinearEquiv.toContinuousLinearEquiv`). Composing with it and with `contDiffWithinAt_pi` gives
the entrywise criteria; this follows the proof of Mathlib's `contDiffWithinAt_piLp`, with
`PiLp.continuousLinearEquiv` replaced by that equivalence.

## Main results

* `Matrix.contDiffWithinAt_l2Op_iff`, `Matrix.contDiffAt_l2Op_iff`, `Matrix.contDiffOn_l2Op_iff`,
  `Matrix.contDiff_l2Op_iff`: under `Matrix.Norms.L2Operator`, a matrix-valued map is `C^k`
  exactly when each of its entries is.
* `Matrix.contDiff_l2Op_iff_contDiff_elementwise`: a matrix-valued map is `C^k` for the ℓ²
  operator norm exactly when it is `C^k` for the entrywise norm.
-/

public section

namespace Matrix

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] {k : WithTop ℕ∞} {f : E → Matrix m n 𝕜}

section L2Op

open scoped Matrix.Norms.L2Operator

variable {s : Set E} {x : E}

/-- Under the ℓ² operator norm, a matrix-valued map is `C^k` within `s` at `x` if and only if
each of its entries is. -/
theorem contDiffWithinAt_l2Op_iff :
    ContDiffWithinAt 𝕜 k f s x ↔ ∀ i j, ContDiffWithinAt 𝕜 k (fun y ↦ f y i j) s x := by
  rw [← (ofLinearEquiv 𝕜).symm.toContinuousLinearEquiv.comp_contDiffWithinAt_iff,
    contDiffWithinAt_pi]
  simp only [contDiffWithinAt_pi, Function.comp_def, LinearEquiv.coe_toContinuousLinearEquiv',
    coe_ofLinearEquiv_symm, of_symm_apply]

/-- Under the ℓ² operator norm, a matrix-valued map is `C^k` at `x` if and only if each of its
entries is. -/
theorem contDiffAt_l2Op_iff :
    ContDiffAt 𝕜 k f x ↔ ∀ i j, ContDiffAt 𝕜 k (fun y ↦ f y i j) x := by
  simp_rw [← contDiffWithinAt_univ, contDiffWithinAt_l2Op_iff]

/-- Under the ℓ² operator norm, a matrix-valued map is `C^k` on `s` if and only if each of its
entries is. -/
theorem contDiffOn_l2Op_iff :
    ContDiffOn 𝕜 k f s ↔ ∀ i j, ContDiffOn 𝕜 k (fun y ↦ f y i j) s := by
  simp only [ContDiffOn, contDiffWithinAt_l2Op_iff]
  exact ⟨fun h i j y hy ↦ h y hy i j, fun h y hy i j ↦ h i j y hy⟩

/-- Under the ℓ² operator norm, a matrix-valued map is `C^k` if and only if each of its entries
is. -/
theorem contDiff_l2Op_iff :
    ContDiff 𝕜 k f ↔ ∀ i j, ContDiff 𝕜 k fun y ↦ f y i j := by
  simp_rw [← contDiffOn_univ, contDiffOn_l2Op_iff]

end L2Op

/-- A matrix-valued map is `C^k` for the ℓ² operator norm `Matrix.Norms.L2Operator` if and only
if it is `C^k` for the entrywise norm `Matrix.Norms.Elementwise`. -/
theorem contDiff_l2Op_iff_contDiff_elementwise :
    @ContDiff 𝕜 _ E _ _ (Matrix m n 𝕜) instL2OpNormedAddCommGroup instL2OpNormedSpace k f ↔
      @ContDiff 𝕜 _ E _ _ (Matrix m n 𝕜) Matrix.normedAddCommGroup Matrix.normedSpace k f := by
  rw [contDiff_l2Op_iff]
  exact (forall_congr' fun _ ↦ contDiff_pi.symm).trans contDiff_pi.symm

end Matrix

end
