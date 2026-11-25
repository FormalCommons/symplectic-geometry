/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Fixed points and stabilizers

A point with trivial stabilizer under the action of a nontrivial group is not fixed by the
whole group (`MulAction.notMem_fixedPoints_of_stabilizer_eq_bot`).
-/

public section

namespace MulAction

/-- Under the action of a nontrivial group, a point with trivial stabilizer is not a fixed point
of the action. -/
theorem notMem_fixedPoints_of_stabilizer_eq_bot {G α : Type*} [Group G] [MulAction G α]
    [Nontrivial G] {x : α} (h : stabilizer G x = ⊥) : x ∉ fixedPoints G α := fun hx ↦ by
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  exact hg (Subgroup.mem_bot.1 (h ▸ mem_stabilizer_iff.2 (hx g)))

end MulAction

end
