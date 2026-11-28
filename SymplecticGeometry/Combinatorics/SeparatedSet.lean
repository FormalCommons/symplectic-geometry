/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Preorder.Finite

/-!
# Separated finite sets that cannot be enlarged

Let `d` be a symmetric function on `α` with values in a linear order, and `r` a value above every
`d x x`. If the `r`-separated finite sets, those whose distinct points are at `d` at least `r`,
have bounded size, then one of largest size cannot be enlarged, so every point of `α` is at `d`
less than `r` from one of its points.

This is the finite, function-valued form of `SetRel.IsCover.of_maximal_isSeparated`, which says
that a maximal separated subset of a set covers it. Here separation is a bound on a function `d`,
not a relation, and the bound on the size gives the maximal set through
`Set.Finite.exists_maximalFor'`. The step that enlarges a set by a point it does not reach
follows the proof of `SetRel.IsCover.of_maximal_isSeparated`.

## Main results

* `Finset.exists_separated_forall_exists_lt`: under a bound on the size of `r`-separated finite
  sets, there is an `r`-separated finite set `S` such that every point is at `d` less than `r`
  from a point of `S`.
-/

public section

namespace Finset

variable {α β : Type*} [LinearOrder β]

/-- Let `d` be a symmetric function on `α` with values in a linear order, and `r` larger than
every `d x x`. If every finite set whose distinct points are at `d` at least `r` has at most `K`
points, then there is such a finite set `S` with every point of `α` at `d` less than `r` from a
point of `S`. -/
theorem exists_separated_forall_exists_lt {d : α → α → β} (hd : ∀ x y, d x y = d y x) {r : β}
    (hr : ∀ x, d x x < r) {K : ℕ}
    (hK : ∀ S : Finset α, (∀ x ∈ S, ∀ x' ∈ S, x ≠ x' → r ≤ d x x') → #S ≤ K) :
    ∃ S : Finset α, (∀ x ∈ S, ∀ x' ∈ S, x ≠ x' → r ≤ d x x') ∧ ∀ y, ∃ x ∈ S, d x y < r := by
  classical
  obtain ⟨S, hS, hmax⟩ := Set.Finite.exists_maximalFor' card
    {S : Finset α | ∀ x ∈ S, ∀ x' ∈ S, x ≠ x' → r ≤ d x x'}
    ((Set.finite_Iic K).subset (by rintro _ ⟨S, hS, rfl⟩; exact hK S hS)) ⟨∅, by simp⟩
  refine ⟨S, hS, fun y ↦ ?_⟩
  by_contra! hy
  have hyS : y ∉ S := fun h ↦ (hy y h).not_gt (hr y)
  have hins : ∀ x ∈ insert y S, ∀ x' ∈ insert y S, x ≠ x' → r ≤ d x x' := by
    simp only [mem_insert]
    rintro x (rfl | hx) x' (rfl | hx') hne
    · exact absurd rfl hne
    · rw [hd]
      exact hy x' hx'
    · exact hy x hx
    · exact hS x hx x' hx' hne
  have h := hmax hins (by rw [card_insert_of_notMem hyS]; omega)
  rw [card_insert_of_notMem hyS] at h
  omega

end Finset

end
