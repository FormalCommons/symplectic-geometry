/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Curve

/-!
# Velocities of curves along which a map is constant

This file adds to Tau Ceti's API for `TauCeti.Manifold.curveVelocityWithin`
(`TauCeti/Geometry/Manifold/MFDeriv/Curve.lean`).

## Main results

* `TauCeti.Manifold.mfderiv_curveVelocityWithin_eq_zero_of_eqOn`: if `f ∘ γ` is constant on a
  parameter set `s`, the derivative of `f` kills the velocity of `γ` within `s` at every point of
  `s` where `f` and `γ` are differentiable. Where the derivative within `s` is unique, this is
  Tau Ceti's chain rule `TauCeti.Manifold.curveVelocityWithin_map`; elsewhere the velocity is `0`.
-/

public section

open Set
open scoped Manifold

namespace TauCeti.Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F H G M N : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]

/-- Let `γ` be a curve, differentiable within `s` at `t ∈ s`, and `f` a map differentiable at
`γ t`. If `f ∘ γ` is constant on `s`, then the derivative of `f` at `γ t` sends the velocity of
`γ` within `s` at `t` to `0`. -/
theorem mfderiv_curveVelocityWithin_eq_zero_of_eqOn {f : M → N} {γ : 𝕜 → M} {s : Set 𝕜}
    {t : 𝕜} {y : N} (hf : MDifferentiableAt I J f (γ t))
    (hγ : MDifferentiableWithinAt 𝓘(𝕜, 𝕜) I γ s t) (hfγ : EqOn (f ∘ γ) (fun _ ↦ y) s)
    (ht : t ∈ s) : mfderiv I J f (γ t) (curveVelocityWithin I γ s t) = 0 := by
  by_cases hs : UniqueDiffWithinAt 𝕜 s t
  · rw [← curveVelocityWithin_map hf hs hγ, curveVelocityWithin_apply,
      mfderivWithin_congr hfγ (hfγ ht), mfderivWithin_const]
    exact zero_apply _
  · rw [curveVelocityWithin_eq_zero_of_not_uniqueDiffWithinAt hs, map_zero]

end TauCeti.Manifold

end
