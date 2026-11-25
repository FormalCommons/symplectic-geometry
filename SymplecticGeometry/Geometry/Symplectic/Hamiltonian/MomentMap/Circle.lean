/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.GroupAction.Circle
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Critical

/-!
# Critical points of a circle moment map

Let a circle act smoothly on a Hausdorff boundaryless manifold `M`, with moment map `μ` for a
two-form `σ`, and let `H = ⟨μ, ξ₁⟩` be its component along the period-one generator
`ξ₁ = circlePeriodOneGenerator`. Where `σ` is nondegenerate, `x` is a critical point of `H`
exactly when the whole circle fixes `x`: by Tau Ceti's
`TauCeti.SmoothTwoForm.IsMomentMap.mem_criticalPoints_iff`, `dH_x = 0` exactly when the
fundamental vector field of `ξ₁` vanishes at `x`, and by
`SymplecticGeometry.mem_fixedPoints_circle_iff_fundamentalVectorField_eq_zero` this happens
exactly at the fixed points of the action.

## Main results

* `TauCeti.SmoothTwoForm.IsMomentMap.mem_criticalPoints_circlePeriodOneGenerator_iff`: at a
  point where `σ` is nondegenerate, `x` is critical for `⟨μ, ξ₁⟩` exactly when `x` is a fixed
  point of the circle action.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Proposition 5.1.9.
-/

public section

open Manifold TauCeti SymplecticGeometry
open scoped ContDiff Manifold

namespace TauCeti.SmoothTwoForm.IsMomentMap

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M] [MulAction Circle M]
  [ContMDiffSMul (𝓡 1) I ∞ Circle M] {σ : SmoothTwoForm I M}
  {μ : M → Module.Dual ℝ (GroupLieAlgebra (𝓡 1) Circle)}

/-- **Critical points of a circle Hamiltonian.** For a smooth circle action on a Hausdorff
boundaryless manifold with moment map `μ` for `σ`, and a point `x` at which `σ` is
nondegenerate, `x` is a critical point of `H = ⟨μ, circlePeriodOneGenerator⟩` exactly when every
element of the circle fixes `x`. -/
theorem mem_criticalPoints_circlePeriodOneGenerator_iff
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental (𝓡 1) Circle I M) μ)
    {x : M} (hσ : (σ.bilinFormAt x).Nondegenerate) :
    x ∈ criticalPoints I (fun y ↦ μ y circlePeriodOneGenerator) ↔
      x ∈ MulAction.fixedPoints Circle M := by
  rw [hμ.mem_criticalPoints_iff hσ, InfinitesimalAction.fundamental_apply,
    mem_fixedPoints_circle_iff_fundamentalVectorField_eq_zero (I' := I)]

end TauCeti.SmoothTwoForm.IsMomentMap

end
