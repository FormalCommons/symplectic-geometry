/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Model
public import TauCeti.Geometry.Manifold.Boundary.Orientation

/-!
# Outward fields near the boundary

Let `W` be a manifold modelled on the half-space `𝓡∂ (n + 1)` and `Y` a vector field on `W` that
points out of `W` along its boundary (`TauCeti.IsOutwardPointing`). Integral curves of `Y` cannot
start at a boundary point and go forward, but they can go backward, into the interior. Tau Ceti
builds these curves along the whole boundary, as the forward flow of `-Y`
(`TauCeti.IsOutwardPointingField.exists_contMDiffOn_boundaryFlow`), and shows that their flow-out
from the boundary is a local diffeomorphism at each boundary point
(`TauCeti.isLocalDiffeomorphAt_flowOut_boundary`); `Flow/Basic.lean` makes a collar out of them.
This file adds what the library uses besides.

An integral curve of an outward field stays in the interior at times from which it is defined for
a while forward, since its velocity there within `[t, ∞)` would be outward, which Tau Ceti's
`TauCeti.not_isOutwardPointing_curveVelocityWithin_Ici` rules out
(`IsMIntegralCurveOn.mem_interior_of_isOutwardPointing`).

## Main results

* `IsMIntegralCurveOn.mem_interior_of_isOutwardPointing`: an integral curve of an outward field is
  in the interior at each time `t` of its domain `s` with `s ∈ 𝓝[≥] t`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218, 2013,
  Chapter 9 (flows; the flow-out theorem 9.20, and the collar theorem 9.25).
* M. Hirsch, *Differential Topology*, Springer GTM 33, 1976, Chapter 4, Theorem 6.1.
-/

public section

open Set Function Topology
open scoped Manifold

namespace TauCeti

variable {n : ℕ} {W : Type*} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
  {Y : (x : W) → TangentSpace (𝓡∂ (n + 1)) x}

/-- An integral curve of a vector field that points outward along the boundary is in the interior
at every time `t` of its domain `s` from which it is defined for a while forward, that is with
`s ∈ 𝓝[≥] t`. -/
theorem _root_.IsMIntegralCurveOn.mem_interior_of_isOutwardPointing
    (hY : ∀ x ∈ (𝓡∂ (n + 1)).boundary W, IsOutwardPointing x (Y x)) {γ : ℝ → W} {s : Set ℝ}
    (hγ : IsMIntegralCurveOn γ Y s) {t : ℝ} (hs : s ∈ 𝓝[≥] t) :
    γ t ∈ (𝓡∂ (n + 1)).interior W := by
  rw [← ModelWithCorners.compl_boundary]
  intro hb
  -- The velocity of `γ` at `t` within `[t, ∞)` is `Y (γ t)`, which is outward, but no curve
  -- running forward from `t` has an outward velocity there.
  apply not_isOutwardPointing_curveVelocityWithin_Ici (n := n) γ t
  rw [Manifold.curveVelocityWithin_eq_of_hasMFDerivWithinAt
    ((hγ t (mem_of_mem_nhdsWithin self_mem_Ici hs)).mono_of_mem_nhdsWithin hs)
    (uniqueDiffOn_Ici t t self_mem_Ici)]
  exact hY _ hb

end TauCeti

end
