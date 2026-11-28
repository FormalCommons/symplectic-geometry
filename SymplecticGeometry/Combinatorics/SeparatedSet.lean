/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Basic.Rel.Cover
public import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Preorder.Finite

/-!
# Separated finite sets that cannot be enlarged

Let `U` be a reflexive symmetric relation on `α`. If the finite `U`-separated sets have bounded
size, then one of largest size is maximal among the `U`-separated sets, so it is a `U`-cover of
the whole of `α`.

The maximal set is given by `Set.Finite.exists_maximalFor'`, applied to the size of the finite
separated sets, and the cover by `SetRel.IsCover.of_maximal_isSeparated`.

The second result is the case of the relation `d x y < r` for a symmetric function `d` with
values in a linear order and a value `r` above every `d x x`.

## Main results

* `SetRel.exists_finset_isSeparated_isCover`: under a bound on the size of finite `U`-separated
  sets, there is a finite `U`-separated set that is a `U`-cover of `α`.
* `Finset.exists_separated_forall_exists_lt`: under a bound on the size of `r`-separated finite
  sets, there is an `r`-separated finite set `S` such that every point is at `d` less than `r`
  from a point of `S`.
-/

public section

namespace SetRel

variable {α : Type*}

/-- Let `U` be a reflexive symmetric relation on `α`. If every finite `U`-separated set has at
most `K` points, then there is a finite `U`-separated set that is a `U`-cover of `α`. -/
theorem exists_finset_isSeparated_isCover {U : SetRel α α} [U.IsRefl] [U.IsSymm] {K : ℕ}
    (hK : ∀ S : Finset α, U.IsSeparated (S : Set α) → S.card ≤ K) :
    ∃ S : Finset α, U.IsSeparated (S : Set α) ∧ U.IsCover Set.univ S := by
  classical
  obtain ⟨S, hS, hmax⟩ := Set.Finite.exists_maximalFor' Finset.card
    {S : Finset α | U.IsSeparated (S : Set α)}
    ((Set.finite_Iic K).subset (by rintro _ ⟨S, hS, rfl⟩; exact hK S hS)) ⟨∅, by simp⟩
  refine ⟨S, hS, IsCover.of_maximal_isSeparated ⟨⟨Set.subset_univ _, hS⟩, ?_⟩⟩
  rintro N ⟨-, hN⟩ hSN x hx
  by_contra hxS
  rw [Finset.mem_coe] at hxS
  have hins : U.IsSeparated (insert x S : Finset α) := by
    rw [Finset.coe_insert]
    exact hN.mono_right (Set.insert_subset hx hSN)
  have h := hmax hins (by rw [Finset.card_insert_of_notMem hxS]; omega)
  rw [Finset.card_insert_of_notMem hxS] at h
  omega

end SetRel

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
  let U : SetRel α α := {p | d p.1 p.2 < r}
  have : U.IsRefl := ⟨fun x ↦ by simpa [U] using hr x⟩
  have : U.IsSymm := ⟨fun x y h ↦ by simpa [U, hd x y] using h⟩
  have hsep (S : Finset α) :
      U.IsSeparated (S : Set α) ↔ ∀ x ∈ S, ∀ x' ∈ S, x ≠ x' → r ≤ d x x' := by
    simp [SetRel.IsSeparated, Set.Pairwise, U]
  obtain ⟨S, hS, hcov⟩ := SetRel.exists_finset_isSeparated_isCover (U := U) (K := K)
    fun S h ↦ hK S ((hsep S).1 h)
  refine ⟨S, (hsep S).1 hS, fun y ↦ ?_⟩
  obtain ⟨x, hx, hyx⟩ := hcov (Set.mem_univ y)
  exact ⟨x, hx, by simpa [U, hd y x] using hyx⟩

end Finset

end
