/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
public import TauCeti.Geometry.Manifold.DeRham.Integration.Bijective

/-!
# Differences of oriented integrals of top forms on a compact manifold

On a compact manifold every continuous top form is compactly supported, hence integrable, so
Tau Ceti's oriented integral `TauCeti.integralTopForm` turns differences of such forms into
differences of integrals (`TauCeti.integralTopForm_sub_of_compactSpace`).

If the manifold is moreover boundaryless, Hausdorff and preconnected, two smooth top forms differ
by an exact form exactly when they have the same integral
(`TauCeti.sub_mem_exactForms_iff_integralTopForm_eq`). This combines Tau Ceti's top-degree
Poincaré lemma `TauCeti.mem_exactCompactlySupportedForms_iff_integralTopForm_eq_zero` with
`TauCeti.exactCompactlySupportedForms_eq_exactForms`.

The proof follows Tau Ceti's `TauCeti.integralTopForm_add` and
`TauCeti.integralTopForm_add_of_compactSpace`, with Tau Ceti's
`TauCeti.integralTopForm_sub_of_integrable` in place of
`TauCeti.integralTopForm_add_of_integrable`.
-/

public section

open scoped ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {k : ℕ}

section

variable [IsManifold I 1 M] {φ ψ : RoughForm I M ℝ k}

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

end

/-- On a compact, preconnected, boundaryless, Hausdorff manifold of dimension `k` with an
orientation `o`, two smooth top forms differ by an exact form if and only if they have the same
integral. -/
theorem sub_mem_exactForms_iff_integralTopForm_eq [IsManifold I ∞ M] [BoundarylessManifold I M]
    [T2Space M] [CompactSpace M] [PreconnectedSpace M]
    (o : Manifold.Orientation I M (Fin k)) {σ τ : SmoothForm I M ℝ k} :
    σ - τ ∈ exactForms I M k ↔ integralTopForm o σ.val = integralTopForm o τ.val := by
  rw [← exactCompactlySupportedForms_eq_exactForms,
    mem_exactCompactlySupportedForms_iff_integralTopForm_eq_zero o
      (by simp [compactlySupportedForms_eq_top]),
    Submodule.coe_sub, integralTopForm_sub_of_compactSpace o (σ.isSmoothForm.of_le (by simp))
      (τ.isSmoothForm.of_le (by simp)), sub_eq_zero]

end TauCeti

end
