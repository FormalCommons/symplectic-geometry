/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import TauCeti.Analysis.Matrix.Exponential.Log
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

The same identity, with Tau Ceti's smoothness of the logarithm `CFC.contDiffOn_log`, gives
smoothness in the base and the exponent together, provided the derivative of the exponential is
invertible at every self-adjoint element, as it is for matrices
(`Matrix.IsHermitian.isUnit_expFDeriv`). This is the smooth counterpart of Tau Ceti's joint
continuity `CFC.continuousOn_rpow_prod`, and its proof follows Tau Ceti's
`Matrix.GeneralLinearGroup.contMDiff_polarDeformation`, which runs the same argument for the
positive polar factor of an invertible matrix.

## Main results

* `CFC.contDiff_const_rpow`: for strictly positive `a`, the map `t ↦ a ^ t` is `C^k` for every
  `k : ℕ∞ω`.
* `CFC.contDiffOn_rpow_prod`: if the derivative of the exponential is invertible at every
  self-adjoint element, then `(a, s) ↦ a ^ s` is `C^k` on the pairs with `a` strictly positive.
* `Matrix.contDiff_rpow_of_posDef`: for a `C^k` family `M` of positive definite real matrices and
  a `C^k` real function `f`, the map `x ↦ M x ^ f x` is `C^k`, for the ℓ² operator norm.
-/

public section

open NormedSpace
open scoped ContDiff

namespace CFC

section Exponent

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [PartialOrder A] [StarOrderedRing A]
  [NonnegSpectrumClass ℝ A]

/-- For a strictly positive element `a`, the real power `t ↦ a ^ t` is `C^k` in the exponent, for
every `k : ℕ∞ω`, the analytic case included. -/
theorem contDiff_const_rpow {a : A} (ha : IsStrictlyPositive a) {k : ℕ∞ω} :
    ContDiff ℝ k fun t : ℝ ↦ a ^ t := by
  simp_rw [rpow_eq_exp_smul_log a _ ha]
  exact (TauCeti.contDiff_exp_smul _).of_le le_top

end Exponent

section Joint

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [ContinuousStar A] [PartialOrder A]
  [StarOrderedRing A] [NonnegSpectrumClass ℝ A]

/-- **Real powers are jointly smooth** in the base and the exponent: if the derivative of the
exponential is invertible at every self-adjoint element, then `(a, s) ↦ a ^ s` is `C^k` on the
pairs whose base is strictly positive, for every `k : ℕ∞ω`. -/
theorem contDiffOn_rpow_prod (hda : ∀ a : A, IsSelfAdjoint a → IsUnit (TauCeti.expFDeriv ℝ a))
    {k : ℕ∞ω} :
    ContDiffOn ℝ k (fun p : A × ℝ ↦ p.1 ^ p.2) ({a : A | IsStrictlyPositive a} ×ˢ Set.univ) := by
  have hlog : ContDiffOn ℝ k (fun p : A × ℝ ↦ log p.1)
      ({a : A | IsStrictlyPositive a} ×ˢ Set.univ) :=
    (contDiffOn_log hda).comp contDiffOn_fst fun _ hp ↦ hp.1
  exact ((contDiff_exp ℝ).comp_contDiffOn (contDiffOn_snd.smul hlog)).congr
    fun p hp ↦ rpow_eq_exp_smul_log p.1 p.2 hp.1

end Joint

end CFC

namespace Matrix

open scoped Matrix.Norms.L2Operator MatrixOrder

variable {n E : Type*} [Fintype n] [DecidableEq n] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {k : ℕ∞ω}

/-- **Joint smoothness of real powers of positive definite matrices.** For a `C^k` family `M` of
positive definite real matrices and a `C^k` real function `f`, the map `x ↦ M x ^ f x` is `C^k`,
for the ℓ² operator norm `Matrix.Norms.L2Operator`. -/
theorem contDiff_rpow_of_posDef {M : E → Matrix n n ℝ} {f : E → ℝ} (hM : ContDiff ℝ k M)
    (hf : ContDiff ℝ k f) (hpos : ∀ x, (M x).PosDef) :
    ContDiff ℝ k fun x ↦ M x ^ f x :=
  (CFC.contDiffOn_rpow_prod fun _ hX ↦ (isHermitian_iff_isSelfAdjoint.2 hX).isUnit_expFDeriv)
    |>.comp_contDiff (hM.prodMk hf) fun x ↦
      ⟨isStrictlyPositive_iff_posDef.2 (hpos x), Set.mem_univ _⟩

end Matrix

end
