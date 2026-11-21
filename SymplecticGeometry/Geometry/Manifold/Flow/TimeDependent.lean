/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.TimeDependent

/-!
# Joint smoothness of time-dependent flows

Let `X` be a `C^n` time-dependent vector field, `1 ≤ n`, on a finite-dimensional boundaryless
manifold `M`, whose suspension on `ℝ × M` is complete. Tau Ceti's
`TauCeti.timeDependentFlowDiffeomorph hc hn hX s t` is the flow of `X` from time `s` to time `t`,
as a `C^n` diffeomorphism of `M`. For a fixed initial time `s`, these diffeomorphisms form a
jointly `C^n` family in `(t, x)`.

## Main results

* `TauCeti.contMDiff_timeDependentFlowDiffeomorph`: the map
  `(t, x) ↦ timeDependentFlowDiffeomorph hc hn hX s t x` is `C^n` on `ℝ × M`. It is Tau Ceti's
  `TauCeti.contMDiff_timeDependentFlowOf` restricted to a fixed initial time.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- The time-dependent flow from a fixed time `s` of a `C^n` time-dependent vector field, `1 ≤ n`,
with complete suspension is jointly `C^n` in the final time and the initial point. -/
theorem contMDiff_timeDependentFlowDiffeomorph [FiniteDimensional ℝ E] [T2Space M]
    [BoundarylessManifold I M] [IsManifold I 1 M] {n : ℕ∞} (hn : 1 ≤ n) [IsManifold I n M]
    {X : ℝ → (x : M) → TangentSpace I x}
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent n
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (hc : IsCompleteVectorField (timeDependentSuspensionField X)) (s : ℝ) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I n
      (fun p : ℝ × M ↦ timeDependentFlowDiffeomorph hc hn hX s p.1 p.2) :=
  (contMDiff_timeDependentFlowOf hc hn hX).comp
    ((contMDiff_const.prodMk contMDiff_fst).prodMk contMDiff_snd) |>.congr fun p ↦
      timeDependentFlowDiffeomorph_apply hc hn hX s p.1 p.2

end TauCeti

end
