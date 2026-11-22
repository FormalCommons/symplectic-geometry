/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity

/-!
# Regularity of differential forms: the function underlying a smooth `0`-form

This file is a part of Tau Ceti's `TauCeti/Geometry/Manifold/DifferentialForm/Regularity.lean`,
copied from Tau Ceti's main branch at commit `d876102e502589a76a0d1c5b2ec35f4bb8656208`, which
the pinned version of Tau Ceti does not have yet. It contains one declaration,
`TauCeti.SmoothForm.contMDiff_apply_zero`: the function underlying a smooth `0`-form is smooth.

Changes from Tau Ceti's text: apart from this module docstring, the variables are only those the
declaration needs, and the file opens only the scopes `ContDiff` and `Manifold`, not Tau Ceti's
`open Set Filter Bundle` nor the scope `Topology`. No statement or proof is changed.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 14.
* Mathlib's alternating-bundle coordinates (`ContinuousAlternatingMap.inCoordinates`) and
  inverse tangent coordinates (`TangentBundle.symmL_trivializationAt`).
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace SmoothForm

/-- The function underlying a smooth `0`-form is smooth. -/
theorem contMDiff_apply_zero [IsManifold I 1 M] (f : SmoothForm I M F 0) :
    ContMDiff I 𝓘(ℝ, F) ∞ fun y ↦ f.val y 0 := by
  rw [← isSmoothForm_ofFunction_iff, ← RoughForm.eq_ofFunction]
  exact f.isSmoothForm

end SmoothForm

end TauCeti
