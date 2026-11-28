/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.OneParameter

import TauCeti.Geometry.Lie.Exponential.Derivative.Basic

/-!
# Closed one-parameter subgroups

API for Tau Ceti's closed one-parameter subgroup `T_ξ = TauCeti.Lie.closedOneParameterSubgroup ξ`
of an element `ξ` of the Lie algebra of a Lie group: the closure of `{exp (t ξ) | t ∈ ℝ}`.

## Main results

* `TauCeti.Lie.closedOneParameterSubgroup_eq_bot_iff`: `T_ξ` is trivial exactly when `ξ = 0`.
  Tau Ceti's `TauCeti.Lie.closedOneParameterSubgroup_zero` is the backward direction; the
  forward one follows from `TauCeti.Lie.forall_mulInvariantExp_smul_eq_one_iff`.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti.Lie

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I (minSmoothness ℝ 3) G] [T2Space G] [BoundarylessManifold I G]
  [IsTopologicalGroup G]

/-- The closed one-parameter subgroup `T_ξ` is trivial exactly when `ξ = 0`. -/
@[simp]
theorem closedOneParameterSubgroup_eq_bot_iff {ξ : GroupLieAlgebra I G} :
    closedOneParameterSubgroup ξ = ⊥ ↔ ξ = 0 := by
  refine ⟨fun h ↦ forall_mulInvariantExp_smul_eq_one_iff.1 fun t ↦ ?_, fun h ↦ by simp [h]⟩
  simpa [h] using mulInvariantExp_smul_mem_closedOneParameterSubgroup ξ t

end TauCeti.Lie

end
