/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.DegreeZero

/-!
# Closed `0`-forms on a connected manifold

On a connected manifold the closed smooth `0`-forms are the constant functions, so they form a
finite-dimensional space. This follows from Tau Ceti's identification `closedFormsZeroEquiv` of
the closed `0`-forms with `H⁰_dR(M)` through `deRhamCohomologyZeroEquiv`, and
`finrank_deRhamCohomology_zero`.

## Main results

* `TauCeti.finiteDimensional_closedForms_zero`: on a connected manifold, the closed smooth
  `0`-forms form a finite-dimensional real vector space (an instance).
-/

public section

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M]

/-- On a connected manifold, the closed smooth `0`-forms form a finite-dimensional space. -/
instance finiteDimensional_closedForms_zero [ConnectedSpace M] :
    FiniteDimensional ℝ (closedForms I M 0) :=
  have : FiniteDimensional ℝ (deRhamCohomology I M 0) :=
    Module.finite_of_finrank_eq_succ (finrank_deRhamCohomology_zero I M)
  ((closedFormsZeroEquiv I M).trans (deRhamCohomologyZeroEquiv I M).symm).symm.finiteDimensional

end TauCeti
