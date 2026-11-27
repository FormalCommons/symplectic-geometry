/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity

/-!
# Subtraction of oriented integrals of continuous top forms on a compact manifold

On a compact manifold every continuous top form is compactly supported, hence integrable, so
Tau Ceti's oriented integral `TauCeti.integralTopForm` turns differences of such forms into
differences of integrals (`TauCeti.integralTopForm_sub_of_compactSpace`).

The proof follows Tau Ceti's `TauCeti.integralTopForm_add` and
`TauCeti.integralTopForm_add_of_compactSpace`, with Tau Ceti's
`TauCeti.integralTopForm_sub_of_integrable` in place of
`TauCeti.integralTopForm_add_of_integrable`.
-/

public section

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] {k : ℕ} {φ ψ : RoughForm I M ℝ k}

/-- On a compact manifold, the oriented integral of a difference of continuous top forms is the
difference of their integrals. -/
theorem integralTopForm_sub_of_compactSpace [CompactSpace M]
    (o : Manifold.Orientation I M (Fin k)) (hφ : IsSmoothForm I 0 φ)
    (hψ : IsSmoothForm I 0 ψ) :
    integralTopForm o (φ - ψ) = integralTopForm o φ - integralTopForm o ψ := by
  let b := Module.finBasisOfFinrankEq ℝ E (by simpa using o.card_eq.symm)
  exact integralTopForm_sub_of_integrable o
    (hφ.integrableTopForm (isClosed_tsupport _).isCompact b)
    (hψ.integrableTopForm (isClosed_tsupport _).isCompact b)

end TauCeti

end
