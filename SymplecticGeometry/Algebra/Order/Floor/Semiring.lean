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
in the cell of index `⌊(x - a) / h⌋₊`; the right end lies in the last cell. For `a < b`, `[a, b]`
has such a mesh with cells as small as wanted (`SymplecticGeometry.exists_mesh_Icc`).
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

/-- For `a < b` and `h₀ > 0`, `[a, b]` has a uniform mesh of `N > 0` cells of size `h < h₀`,
`N h = b - a`, with a sequence `t` that runs through its points, `t i = a + i h` for `i ≤ N`,
and stays in `[a, b]`. -/
theorem exists_mesh_Icc {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [FloorSemiring K] {a b h₀ : K} (hab : a < b) (hh₀ : 0 < h₀) :
    ∃ N : ℕ, 0 < N ∧ ∃ h : K, 0 < h ∧ h < h₀ ∧ N * h = b - a ∧ ∃ t : ℕ → K,
      (∀ i ≤ N, t i = a + i * h) ∧ ∀ i, t i ∈ Icc a b := by
  set N := ⌊(b - a) / h₀⌋₊ + 1
  have hN : (0 : K) < N := Nat.cast_pos.2 (Nat.succ_pos _)
  have hNh₀ : b - a < h₀ * N := by
    have := Nat.lt_floor_add_one ((b - a) / h₀)
    rw [div_lt_iff₀ hh₀] at this
    push_cast [N]
    linarith
  have hNh : (N : K) * ((b - a) / N) = b - a := mul_div_cancel₀ _ hN.ne'
  have hh : 0 < (b - a) / N := div_pos (sub_pos.2 hab) hN
  refine ⟨N, Nat.succ_pos _, (b - a) / N, hh, (div_lt_iff₀ hN).2 hNh₀, hNh,
    fun i ↦ a + (min i N : ℕ) * ((b - a) / N), fun i hi ↦ by simp only [min_eq_left hi], fun i ↦ ?_⟩
  have h₁ : ((min i N : ℕ) : K) ≤ N := Nat.cast_le.2 (min_le_right i N)
  have h₂ : (0 : K) ≤ (min i N : ℕ) := Nat.cast_nonneg _
  exact ⟨le_add_of_nonneg_right (mul_nonneg h₂ hh.le),
    by nlinarith [mul_le_mul_of_nonneg_right h₁ hh.le]⟩

end SymplecticGeometry

end
