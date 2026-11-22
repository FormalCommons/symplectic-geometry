/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Sets.Opens

/-!
# The empty open set

The bottom element `⊥ : Opens X` of the open sets of a topological space has no points
(`TopologicalSpace.Opens.isEmpty_bot`). As an instance, it lets the empty open set serve as an
empty space, for instance as an empty open submanifold, without an inline proof each time.
-/

public section

namespace TopologicalSpace.Opens

/-- The empty open set of a topological space has no points. -/
instance isEmpty_bot {X : Type*} [TopologicalSpace X] : IsEmpty (⊥ : Opens X) :=
  ⟨fun x ↦ x.property⟩

end TopologicalSpace.Opens

end
