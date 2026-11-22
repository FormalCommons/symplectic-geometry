/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog
import TauCeti.Geometry.Lie.Exponential.OneParameter

/-!
# Smoothness of real powers in the exponent

For a strictly positive element `a` of a complete normed `ℝ`-algebra with a continuous functional
calculus, Tau Ceti's `CFC.rpow_eq_exp_smul_log` writes `a ^ t` as `exp (t • log a)`. Since the
exponential curve `t ↦ exp (t • x)` is analytic (`TauCeti.contDiff_exp_smul`), `t ↦ a ^ t` is
`C^k` for every `k : ℕ∞ω`. This complements Tau Ceti's `CFC.contDiffOn_rpow`, which is
smoothness in the base for a fixed exponent, and `Matrix.PosDef.continuous_const_rpow`, which is
continuity in the exponent for matrices.

For a positive definite real or complex matrix `P`, under the operator norm
`Matrix.Norms.L2Operator`, `CFC.contDiff_const_rpow` applies with
`Matrix.PosDef.isStrictlyPositive`.

## Main results

* `CFC.contDiff_const_rpow`: for strictly positive `a`, the map `t ↦ a ^ t` is `C^k` for every
  `k : ℕ∞ω`.
-/

public section

open NormedSpace
open scoped ContDiff

namespace CFC

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [PartialOrder A] [StarOrderedRing A]
  [NonnegSpectrumClass ℝ A]

/-- For a strictly positive element `a`, the real power `t ↦ a ^ t` is `C^k` in the exponent, for
every `k : ℕ∞ω`, the analytic case included. -/
theorem contDiff_const_rpow {a : A} (ha : IsStrictlyPositive a) {k : ℕ∞ω} :
    ContDiff ℝ k fun t : ℝ ↦ a ^ t := by
  simp_rw [rpow_eq_exp_smul_log a _ ha]
  exact (TauCeti.contDiff_exp_smul _).of_le le_top

end CFC

end
