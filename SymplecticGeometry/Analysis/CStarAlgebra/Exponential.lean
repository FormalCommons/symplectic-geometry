/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Exponential
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import TauCeti.Geometry.Lie.Exponential.OneParameter

/-!
# Smoothness of one-parameter groups of exponential unitaries

For a self-adjoint element `a` of a complete normed `ℂ`-algebra with a continuous star,
Mathlib's `selfAdjoint.expUnitary` gives the unitary `exp (I • a)`. The one-parameter group
`t ↦ expUnitary (t • a)` is `exp (t • (I • a))`, hence `C^k` in `t` for every `k : ℕ∞ω`, since the
exponential curve `t ↦ exp (t • x)` is analytic (Tau Ceti's `TauCeti.contDiff_exp_smul`). Mathlib
has its continuity, `selfAdjoint.continuous_expUnitary`.

## Main results

* `selfAdjoint.contDiff_expUnitary_smul`: `t ↦ expUnitary (t • a)`, as a map into the algebra, is
  `C^k` for every `k : ℕ∞ω`.
-/

public section

open NormedSpace
open scoped ContDiff

namespace selfAdjoint

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [ContinuousStar A]
  [CompleteSpace A] [StarModule ℂ A]

/-- For a self-adjoint `a`, the one-parameter group of unitaries `t ↦ expUnitary (t • a)`, viewed
in the algebra, is `C^k` over `ℝ` for every `k : ℕ∞ω`, the analytic case included. -/
theorem contDiff_expUnitary_smul (a : selfAdjoint A) {k : ℕ∞ω} :
    ContDiff ℝ k fun t : ℝ ↦ (expUnitary (t • a) : A) := by
  have h (t : ℝ) : (expUnitary (t • a) : A) = exp (t • (Complex.I • (a : A))) := by
    simp [expUnitary_coe, smul_comm Complex.I t]
  simp_rw [h]
  exact (TauCeti.contDiff_exp_smul _).of_le le_top

end selfAdjoint

end
