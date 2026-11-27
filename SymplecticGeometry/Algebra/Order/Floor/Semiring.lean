/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Order.Interval.Set.Defs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The cells of a uniform mesh

A supplement to `Mathlib.Algebra.Order.Floor.Semiring`: in a linearly ordered field with a floor,
the closed intervals `[a + j h, a + (j + 1) h]`, `j < N`, of the mesh of step `h > 0` cover
`[a, a + N h]` (`SymplecticGeometry.exists_lt_mem_Icc_add_mul`). Left of `a + N h`, a point lies
in the cell of index `⌊(x - a) / h⌋₊`; the right end lies in the last cell.
-/

public section

namespace SymplecticGeometry

open Set

/-- A point `x` of `[a, a + N h]`, for `h > 0` and `N > 0`, lies in one of the intervals
`[a + j h, a + (j + 1) h]` of the mesh with `j < N`. -/
theorem exists_lt_mem_Icc_add_mul {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [FloorSemiring K] {a h x : K} {N : ℕ} (hh : 0 < h) (hN : 0 < N)
    (hx : x ∈ Icc a (a + N * h)) : ∃ j < N, x ∈ Icc (a + j * h) (a + (j + 1) * h) := by
  rcases hx.2.lt_or_eq with hlt | heq
  · have hx₀ : 0 ≤ (x - a) / h := div_nonneg (by linarith [hx.1]) hh.le
    refine ⟨⌊(x - a) / h⌋₊, (Nat.floor_lt hx₀).2 ((div_lt_iff₀ hh).2 (by linarith)), ?_, ?_⟩
    · linarith [(le_div_iff₀ hh).1 (Nat.floor_le hx₀)]
    · linarith [(div_lt_iff₀ hh).1 (Nat.lt_floor_add_one ((x - a) / h))]
  · refine ⟨N - 1, Nat.sub_lt hN one_pos, ?_⟩
    rw [Nat.cast_pred hN, heq]
    exact ⟨by nlinarith, le_of_eq (by ring)⟩

end SymplecticGeometry

end
