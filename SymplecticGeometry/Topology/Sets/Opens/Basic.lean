/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Sets.Opens
public import Mathlib.Topology.Separation.Basic

/-!
# The empty open set and complements of finite sets

The bottom element `⊥ : Opens X` of the open sets of a topological space has no points
(`TopologicalSpace.Opens.isEmpty_bot`). As an instance, it lets the empty open set serve as an
empty space, for instance as an empty open submanifold, without an inline proof each time.

In a T1 space a finite set is closed, so the complement of a finite set `B` is an open set,
`B.complOpens` (`Finset.complOpens`), with `Finset.coe_complOpens` and `Finset.mem_complOpens`.
It carries the manifold structure of an open subset, for instance as the domain of a map defined
away from finitely many points.
-/

public section

namespace TopologicalSpace.Opens

/-- The empty open set of a topological space has no points. -/
instance isEmpty_bot {X : Type*} [TopologicalSpace X] : IsEmpty (⊥ : Opens X) :=
  ⟨fun x ↦ x.property⟩

end TopologicalSpace.Opens

namespace Finset

variable {X : Type*} [TopologicalSpace X] [T1Space X]

/-- The complement of a finite subset `B` of a T1 space, as an open set. -/
def complOpens (B : Finset X) : TopologicalSpace.Opens X :=
  ⟨(B : Set X)ᶜ, B.finite_toSet.isClosed.isOpen_compl⟩

@[simp]
theorem coe_complOpens (B : Finset X) : (B.complOpens : Set X) = (B : Set X)ᶜ :=
  (rfl)

@[simp]
theorem mem_complOpens {B : Finset X} {x : X} : x ∈ B.complOpens ↔ x ∉ B :=
  Iff.rfl

end Finset

end
