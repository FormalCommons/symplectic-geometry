/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.ContMDiff

/-!
# Changing the regularity of a smooth almost complex structure

Tau Ceti's `TauCeti.SmoothAlmostComplexStructure.toContMDiff` views a smooth almost complex
structure as a `C^n` one. This file records that the pointwise structures do not change:

* `TauCeti.SmoothAlmostComplexStructure.almostComplexStructureAt_toContMDiff`: the pointwise
  almost complex structures of `J.toContMDiff n` and of `J` agree. So, for instance, a map is
  totally real for one exactly when it is totally real for the other.
-/

public section

open scoped ContDiff

namespace TauCeti.SmoothAlmostComplexStructure

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Viewing a smooth almost complex structure at a finite regularity leaves its pointwise
structures unchanged. -/
@[simp]
theorem almostComplexStructureAt_toContMDiff (J : SmoothAlmostComplexStructure I M) (n : ℕ∞) :
    (J.toContMDiff n).almostComplexStructureAt = J.almostComplexStructureAt := by
  funext x
  ext v
  rw [ContMDiffAlmostComplexStructure.almostComplexStructureAt_toLinearMap,
    almostComplexStructureAt_toLinearMap, toContMDiff_toEndomorphism_apply]

end TauCeti.SmoothAlmostComplexStructure

end
