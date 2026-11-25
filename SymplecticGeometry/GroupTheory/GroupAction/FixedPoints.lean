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

A point is fixed by a group action exactly when its stabilizer is the whole group
(`MulAction.mem_fixedPoints_iff_stabilizer_eq_top`). Consequently, a point with trivial
stabilizer under the action of a nontrivial group is not fixed by the whole group
(`MulAction.notMem_fixedPoints_of_stabilizer_eq_bot`).
-/

public section

namespace MulAction

/-- A point is a fixed point of a group action if and only if its stabilizer is the whole
group. -/
@[to_additive /-- A point is a fixed point of an additive group action if and only if its
stabilizer is the whole group. -/]
theorem mem_fixedPoints_iff_stabilizer_eq_top {G α : Type*} [Group G] [MulAction G α] {x : α} :
    x ∈ fixedPoints G α ↔ stabilizer G x = ⊤ := by
  simp only [mem_fixedPoints, Subgroup.eq_top_iff', mem_stabilizer_iff]

/-- Under the action of a nontrivial group, a point with trivial stabilizer is not a fixed point
of the action. -/
theorem notMem_fixedPoints_of_stabilizer_eq_bot {G α : Type*} [Group G] [MulAction G α]
    [Nontrivial G] {x : α} (h : stabilizer G x = ⊥) : x ∉ fixedPoints G α := by
  rw [mem_fixedPoints_iff_stabilizer_eq_top, h]
  exact bot_ne_top

end MulAction

end
