/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Free actions on sub-actions

A group acts freely on a sub-action `p : SubMulAction G M` as soon as every point of `p` has
trivial stabilizer, even when the action on `M` is not free
(`SubMulAction.isCancelSMul_of_forall_stabilizer_eq_bot`). Mathlib's instance for `p` asks for
`IsCancelSMul G M` on the whole space.
-/

public section

namespace SubMulAction

/-- If every point of the sub-action `p` has trivial stabilizer, then `G` acts freely on `p`. -/
theorem isCancelSMul_of_forall_stabilizer_eq_bot {G M : Type*} [Group G] [MulAction G M]
    (p : SubMulAction G M) (hfree : ∀ x ∈ p, MulAction.stabilizer G x = ⊥) :
    IsCancelSMul G p :=
  isCancelSMul_iff_stabilizer_eq_bot.2 fun x ↦
    (SubMulAction.stabilizer_of_subMul x).trans (hfree x x.property)

end SubMulAction

end
