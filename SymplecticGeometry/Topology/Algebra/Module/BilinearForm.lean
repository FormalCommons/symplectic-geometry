/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear

/-!
# Continuous bilinear forms in finite dimensions

On a finite-dimensional Hausdorff topological vector space over a complete field, every bilinear
form is continuous. Tau Ceti shows that making a bilinear form continuous and then forgetting
continuity gives the form back (`LinearMap.BilinForm.toBilinForm_toContinuousBilinearMap`). This
file gives the other round trip: forgetting the continuity of a continuous bilinear form and
making it continuous again gives the same continuous bilinear form.

## Main results

* `ContinuousLinearMap.toContinuousBilinearMap_toBilinForm`:
  `L.toBilinForm.toContinuousBilinearMap = L`.
-/

public section

namespace ContinuousLinearMap

/-- Forgetting the continuity of a continuous bilinear form on a finite-dimensional space, and
then making it continuous again, returns the original form. -/
@[simp]
theorem toContinuousBilinearMap_toBilinForm
    {𝕜 V : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousSMul 𝕜 V] [FiniteDimensional 𝕜 V] [T2Space V]
    (L : V →L[𝕜] V →L[𝕜] 𝕜) : L.toBilinForm.toContinuousBilinearMap = L :=
  (rfl)

end ContinuousLinearMap

end
