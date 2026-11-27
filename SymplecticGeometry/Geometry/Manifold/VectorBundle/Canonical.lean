/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Canonical

/-!
# The coordinate form of a chart as a pull-back

Tau Ceti's `TauCeti.CanonicalBundle.coordForm I x₀ b` is the coordinate form `dz₁ ∧ ⋯ ∧ dzₙ` of
the chart at `x₀`, defined through the trivialization of the tangent bundle. This file identifies
it, on the source of the chart, with the pull-back of the determinant form `b.continuousDet` of
the model space by the differential of the extended chart
(`TauCeti.CanonicalBundle.coordForm_eq_compContinuousLinearMap_mfderiv`). In that form the
coordinate form makes sense for any chart of the maximal atlas, and the chain rule computes its
pull-backs.

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978], Chapter 1,
  §1 (the canonical bundle of a complex manifold).
-/

public section

open scoped Manifold

namespace TauCeti.CanonicalBundle

variable {𝕜 E H : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- On the source of the chart at `x₀`, the coordinate form of that chart is the determinant form
of `b` pulled back by the differential of the extended chart. -/
theorem coordForm_eq_compContinuousLinearMap_mfderiv {x₀ x : M}
    (hx : x ∈ (chartAt H x₀).source) (b : Module.Basis (Fin (Module.finrank 𝕜 E)) 𝕜 E) :
    coordForm I x₀ b x =
      b.continuousDet.compContinuousLinearMap (mfderiv I 𝓘(𝕜, E) (extChartAt I x₀) x) := by
  ext v
  rw [coordForm_apply, TangentBundle.continuousLinearMapAt_trivializationAt hx,
    ← Module.Basis.continuousDet_apply]
  exact (ContinuousAlternatingMap.compContinuousLinearMap_apply (M' := TangentSpace I x)
    (M := E) b.continuousDet _ v).symm

end TauCeti.CanonicalBundle

end
