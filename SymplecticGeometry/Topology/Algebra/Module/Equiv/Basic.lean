/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# Basic facts about continuous linear equivalences

General lemmas about `ContinuousLinearEquiv` that Mathlib does not state at the pinned version,
kept in its namespace so that they can move upstream unchanged.

## Main results

* `ContinuousLinearEquiv.toLinearEquiv_refl`: the underlying linear equivalence of the identity
  is the identity, as Mathlib states for `LinearIsometryEquiv.toLinearEquiv_refl`.
-/

public section

namespace ContinuousLinearEquiv

variable (R : Type*) [Semiring R] (M : Type*) [TopologicalSpace M] [AddCommMonoid M]
  [Module R M]

/-- The linear equivalence underlying the identity continuous linear equivalence is
`LinearEquiv.refl`. -/
@[simp]
theorem toLinearEquiv_refl :
    (ContinuousLinearEquiv.refl R M).toLinearEquiv = LinearEquiv.refl R M :=
  rfl

end ContinuousLinearEquiv

end
