/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.DiscreteSubset

/-!
# Discrete subsets by isolated points

A subset `s` of a topological space is discrete exactly when each of its points has a punctured
neighbourhood that misses `s` (`isDiscrete_iff_forall_eventually_notMem`). This is Mathlib's
`isDiscrete_iff_nhdsNE`, with the condition `𝓝[≠] x ⊓ 𝓟 s = ⊥` written as an `Eventually`
statement, the form in which isolation of a point is usually proved.
-/

public section

open Filter
open scoped Topology

variable {X : Type*} [TopologicalSpace X] {s : Set X}

/-- A set is discrete if and only if each of its points has a punctured neighbourhood disjoint
from the set. -/
theorem isDiscrete_iff_forall_eventually_notMem :
    IsDiscrete s ↔ ∀ x ∈ s, ∀ᶠ y in 𝓝[≠] x, y ∉ s := by
  simp only [isDiscrete_iff_nhdsNE, inf_principal_eq_bot, eventually_iff, Set.compl_def]

end
