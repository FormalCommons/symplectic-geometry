/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.Order.LocalExtr

/-!
# Local minima of squared norms

For a dependent map `φ : ∀ p, V p` from a topological space into seminormed groups, such as a
section of a normed vector bundle, the function `p ↦ ‖φ p‖ ^ 2` is nonnegative, so it has a local
minimum at each zero of `φ` (`isLocalMin_norm_sq_of_eq_zero`).
-/

public section

open Filter

variable {M : Type*} [TopologicalSpace M] {V : M → Type*} [∀ p, SeminormedAddGroup (V p)]
  {φ : ∀ p, V p} {x : M}

/-- At a zero `x` of a dependent map `φ` into seminormed groups, such as a section of a normed
vector bundle, the function `p ↦ ‖φ p‖²` has a local minimum: it is nonnegative and vanishes at
`x`. -/
theorem isLocalMin_norm_sq_of_eq_zero (hφx : φ x = 0) :
    IsLocalMin (fun p ↦ ‖φ p‖ ^ 2) x :=
  Eventually.of_forall fun p ↦ by simp [hφx]

end
