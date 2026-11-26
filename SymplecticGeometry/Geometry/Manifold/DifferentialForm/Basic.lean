/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import TauCeti.Geometry.Manifold.DifferentialForm.Basic

/-!
# Rough forms evaluated on vector fields

A rough `k`-form `φ` on `M` with values in `F` (Tau Ceti's `TauCeti.RoughForm`) is a section of
the bundle of continuous alternating maps on the tangent spaces. If that section is
differentiable at `x`, then evaluating `φ` on `k` vector fields that are differentiable at `x`
gives an `F`-valued function differentiable at `x`
(`TauCeti.RoughForm.mdifferentiableAt_apply_vectorField`). This is the rough-form version of
Tau Ceti's `TauCeti.SmoothForm.mdifferentiableAt_apply_vectorField`, and its proof is the same,
through Mathlib's `MDifferentiableAt.continuousAlternatingMap_bundle_apply`.

## Main results

* `TauCeti.RoughForm.mdifferentiableAt_apply_vectorField`: a rough form differentiable at `x`,
  evaluated on vector fields differentiable at `x`, is differentiable at `x`.
-/

public section

open Bundle
open scoped Manifold

namespace TauCeti.RoughForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- If a rough `k`-form `φ` is differentiable at `x`, as a section of the bundle of alternating
maps, then its values on `k` vector fields differentiable at `x` form a function differentiable
at `x`. -/
theorem mdifferentiableAt_apply_vectorField {φ : RoughForm I M F k}
    {V : Fin k → (y : M) → TangentSpace I y} {x : M}
    (hφ : MDiffAt (fun y ↦
      (TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y (φ y) :
        TotalSpace (E [⋀^Fin k]→L[ℝ] F)
          (fun y ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Bundle.Trivial M F y))) x)
    (hV : ∀ i, MDifferentiableAt I I.tangent (fun y ↦ (V i y : TangentBundle I M)) x) :
    MDifferentiableAt I 𝓘(ℝ, F) (fun y ↦ φ y (V · y)) x := by
  have h := hφ.continuousAlternatingMap_bundle_apply (b := id) hV
  simpa using ((mdifferentiableAt_totalSpace _ _).1 h).2

end TauCeti.RoughForm

end
