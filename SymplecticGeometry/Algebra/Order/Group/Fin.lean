/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Order.Fin.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Data.Nat.Find

/-!
# Splitting a finite monotone family by a point far from it

In a linearly ordered additive commutative group, let `c 0 ≤ ⋯ ≤ c (n - 1)` be monotone and let
`t` be at distance at least `w` from each `c i`. Then `t` splits the family:
`Monotone.exists_forall_add_le_and_forall_le_sub` gives an index `l ≤ n` such that the terms
before `l` lie at least `w` below `t` and the others at least `w` above it.
-/

public section

/-- If `c 0 ≤ ⋯ ≤ c (n - 1)` is monotone and `t` lies at distance at least `w` from each term,
then for some `l ≤ n`, the terms of index below `l` lie at least `w` below `t` and the others
at least `w` above it. -/
theorem Monotone.exists_forall_add_le_and_forall_le_sub {α : Type*} [AddCommGroup α]
    [LinearOrder α] [IsOrderedAddMonoid α] {n : ℕ} {c : Fin n → α} (hc : Monotone c)
    {w t : α} (ht : ∀ i, w ≤ |t - c i|) :
    ∃ l ≤ n, (∀ i : Fin n, (i : ℕ) < l → c i + w ≤ t) ∧ ∀ i : Fin n, l ≤ (i : ℕ) → t ≤ c i - w := by
  classical
  have hex : ∃ l : ℕ, ∀ i : Fin n, l ≤ (i : ℕ) → t ≤ c i - w :=
    ⟨n, fun i hi ↦ absurd i.isLt (not_lt.2 hi)⟩
  refine ⟨Nat.find hex, Nat.find_min' hex fun i hi ↦ absurd i.isLt (not_lt.2 hi),
    fun i hi ↦ ?_, Nat.find_spec hex⟩
  obtain ⟨i', hii', hi'⟩ := not_forall₂.1 (Nat.find_min hex hi)
  have hle : c i ≤ c i' := hc (Fin.mk_le_mk.2 hii')
  rcases le_abs'.1 (ht i') with h | h
  · exact absurd ((sub_le_iff_le_add.1 h).trans_eq (neg_add_eq_sub w (c i'))) hi'
  · exact (add_le_add_left hle w).trans ((add_comm _ _).trans_le (le_sub_iff_add_le.1 h))

end
