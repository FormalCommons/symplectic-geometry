/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.ComplexLinearPart
import TauCeti.Analysis.Complex.Wirtinger.Basic

/-!
# Bounds for the complex-linear and complex-antilinear parts of an operator

For a continuous real-linear operator `Ψ` between complex normed spaces, Tau Ceti's
`ContinuousLinearMap.complexLinearPart` and `ContinuousLinearMap.complexAntilinearPart` both have
operator norm at most `‖Ψ‖` (`ContinuousLinearMap.norm_complexLinearPart_le`,
`ContinuousLinearMap.norm_complexAntilinearPart_le`), with pointwise forms.

The Wirtinger derivatives of a map are the complex-linear and complex-antilinear parts of its
real derivative, and the derivative of `Ψ` is `Ψ`. So the bounds are Tau Ceti's
`TauCeti.norm_wirtingerDeriv_apply_le` and `TauCeti.norm_conjWirtingerDeriv_apply_le` for the
map `Ψ` itself.
-/

public section

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]

/-- The complex-linear part of a real-linear operator has norm at most that of the operator. -/
theorem norm_complexLinearPart_le (Ψ : E →L[ℝ] F) :
    ‖Ψ.complexLinearPart‖ ≤ ‖Ψ‖ :=
  opNorm_le_bound _ (norm_nonneg Ψ) fun v ↦ by
    simpa [TauCeti.wirtingerDeriv_eq_complexLinearPart] using
      TauCeti.norm_wirtingerDeriv_apply_le (⇑Ψ) 0 v

/-- The complex-antilinear part of a real-linear operator has norm at most that of the
operator. -/
theorem norm_complexAntilinearPart_le (Ψ : E →L[ℝ] F) :
    ‖Ψ.complexAntilinearPart‖ ≤ ‖Ψ‖ :=
  opNorm_le_bound _ (norm_nonneg Ψ) fun v ↦ by
    simpa [TauCeti.conjWirtingerDeriv_eq_complexAntilinearPart] using
      TauCeti.norm_conjWirtingerDeriv_apply_le (⇑Ψ) 0 v

/-- Pointwise form of `ContinuousLinearMap.norm_complexLinearPart_le`. -/
theorem norm_complexLinearPart_apply_le (Ψ : E →L[ℝ] F) (v : E) :
    ‖Ψ.complexLinearPart v‖ ≤ ‖Ψ‖ * ‖v‖ :=
  Ψ.complexLinearPart.le_of_opNorm_le Ψ.norm_complexLinearPart_le v

/-- Pointwise form of `ContinuousLinearMap.norm_complexAntilinearPart_le`. -/
theorem norm_complexAntilinearPart_apply_le (Ψ : E →L[ℝ] F) (v : E) :
    ‖Ψ.complexAntilinearPart v‖ ≤ ‖Ψ‖ * ‖v‖ :=
  Ψ.complexAntilinearPart.le_of_opNorm_le Ψ.norm_complexAntilinearPart_le v

end ContinuousLinearMap

end
