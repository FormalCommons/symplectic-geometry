/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# The differential of a locally constant map

A locally constant map between manifolds has zero differential at every point
(`IsLocallyConstant.mfderiv_eq_zero`). This is the converse of Tau Ceti's
`MDifferentiable.isLocallyConstant_of_mfderiv_eq_zero`, which needs real manifolds and a
differentiable map; the converse holds over any nontrivially normed field.

The proof is the step that Tau Ceti's
`CovariantDerivative.hasParallelCurvature_iff_isLocallyConstant_scalarCurvature_of_finrank_eq_two`
(in `TauCeti/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/LocallySymmetric.lean`)
takes inline: near each point the map agrees with a constant map, whose differential is zero.
-/

public section

open scoped Manifold

namespace IsLocallyConstant

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N] {f : M → N}

/-- A locally constant map between manifolds has zero differential at every point. -/
theorem mfderiv_eq_zero (hf : IsLocallyConstant f) (x : M) : mfderiv I J f x = 0 := by
  rw [Filter.EventuallyEq.mfderiv_eq ((IsLocallyConstant.iff_eventually_eq f).mp hf x)]
  exact mfderiv_const

end IsLocallyConstant

end
