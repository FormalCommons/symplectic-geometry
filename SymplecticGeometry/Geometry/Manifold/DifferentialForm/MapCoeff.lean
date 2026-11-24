/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.MapCoeff

/-!
# Injectivity of coefficient maps of differential forms

Tau Ceti's `TauCeti.RoughForm.mapCoeff L` and `TauCeti.SmoothForm.mapCoeff L` apply a continuous
linear map `L : F →L[ℝ] G` of coefficient spaces to the values of a form. This file shows that
they are injective when `L` is.

## Main results

* `TauCeti.RoughForm.mapCoeff_injective`, `TauCeti.SmoothForm.mapCoeff_injective`: the coefficient
  map along an injective continuous linear map is injective, on rough and on smooth forms.
-/

public section

namespace TauCeti

variable {E H M F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] {k : ℕ}

/-- The coefficient map of rough forms along an injective continuous linear map is injective. -/
theorem RoughForm.mapCoeff_injective {L : F →L[ℝ] G} (hL : Function.Injective L) :
    Function.Injective (mapCoeff (I := I) (M := M) (k := k) L) := fun φ ψ h ↦ by
  ext x v
  exact hL (by simpa using congrArg (fun φ ↦ φ x v) h)

/-- The coefficient map of smooth forms along an injective continuous linear map is
injective. -/
theorem SmoothForm.mapCoeff_injective [IsManifold I 1 M] {L : F →L[ℝ] G}
    (hL : Function.Injective L) :
    Function.Injective (mapCoeff (I := I) (M := M) (k := k) L) := fun _ _ h ↦
  Subtype.ext <| RoughForm.mapCoeff_injective hL <| by
    simpa only [coe_mapCoeff] using congrArg Subtype.val h

end TauCeti

end
