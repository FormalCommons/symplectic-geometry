/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The graph of `t ↦ t / (1 + |t|)`

In a linear ordered field, the map `t ↦ t / (1 + |t|)` is an order isomorphism onto `(-1, 1)`,
with inverse `u ↦ u / (1 - |u|)`; Mathlib builds its `orderIsoIooNegOneOne` from this map. This
file describes its graph by the relation `u * (1 + |t|) = t`
(`mul_one_add_abs_eq_iff`), which is the form in which semialgebraic arguments use it.
-/

public section

/-- `u * (1 + |t|) = t` says that `u` lies in `(-1, 1)` and `t = u / (1 - |u|)`: this is the
graph of the order isomorphism `t ↦ t / (1 + |t|)` of a linear ordered field onto `(-1, 1)`. -/
theorem mul_one_add_abs_eq_iff {k : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k]
    {u t : k} : u * (1 + |t|) = t ↔ |u| < 1 ∧ u / (1 - |u|) = t := by
  refine ⟨fun h ↦ ?_, fun ⟨hu, ht⟩ ↦ ?_⟩
  · have hpos : 0 < 1 + |t| := by positivity
    have habs : |u| * (1 + |t|) = |t| := by
      rw [← abs_of_pos hpos, ← abs_mul, h]
    have hu : |u| < 1 := by nlinarith [abs_nonneg t]
    refine ⟨hu, div_eq_of_eq_mul (by linarith) ?_⟩
    -- `t * |u| = u * |t|`, since both equal `|u| * u * (1 + |t|)`.
    have : t * |u| = u * |t| := by
      calc t * |u| = u * (|u| * (1 + |t|)) := by nth_rewrite 1 [← h]; ring
        _ = u * |t| := by rw [habs]
    linarith
  · have hpos : 0 < 1 - |u| := sub_pos.2 hu
    subst ht
    rw [abs_div, abs_of_pos hpos]
    field_simp
    ring

end
