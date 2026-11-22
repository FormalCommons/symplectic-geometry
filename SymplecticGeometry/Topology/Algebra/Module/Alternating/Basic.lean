/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Alternating.Basic

/-!
# Continuous alternating maps of one vector

A continuous alternating map of degree one is determined by its values on the one-element
families `![w]`. This file states that as the extensionality lemma
`ContinuousAlternatingMap.ext_fin_one`, so that a proof that two such maps agree can start with
`ext w` and work with a vector `w` instead of a family `v : Fin 1 → M`.
-/

public section

namespace ContinuousAlternatingMap

variable {R M N : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [TopologicalSpace M]
  [AddCommMonoid N] [Module R N] [TopologicalSpace N]

/-- Two continuous alternating maps of one vector are equal when they agree on every one-element
family `![w]`. -/
@[ext]
theorem ext_fin_one {f g : M [⋀^Fin 1]→L[R] N} (h : ∀ w, f ![w] = g ![w]) : f = g :=
  ext fun v ↦ by
    rw [show v = ![v 0] from funext fun i ↦ by simp [Fin.fin_one_eq_zero i]]
    exact h (v 0)

end ContinuousAlternatingMap

end
