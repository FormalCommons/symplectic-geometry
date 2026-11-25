/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Data.Set.Function
public import Mathlib.Order.Interval.Set.Defs

/-!
# Sequences of maps that agree with their successors

Supplements to `Mathlib/Data/Set/Function.lean` about a sequence of maps `f : ℕ → α → β` in which
each `f (j + 1)` agrees with `f j` on a set `S j`.

## Main results

* `Set.eqOn_of_eqOn_succ`: if the sets `S j` increase, every later map agrees with `f j` on `S j`.
* `Set.mapsTo_Icc_compl_of_eqOn_succ`: if `f (j + 1)` agrees with `f j` on `(-∞, T j]` and maps
  `[T j, T (j + 1)]` outside `K j`, for increasing sets `K j`, then each later `f k` maps
  `[T j, T k]` outside `K j`.
-/

public section

namespace Set

variable {α β : Type*} {f : ℕ → α → β}

/-- If each `f (j + 1)` agrees with `f j` on `S j`, and the sets `S j` increase, then every later
`f k` agrees with `f j` on `S j`. -/
theorem eqOn_of_eqOn_succ {S : ℕ → Set α} (hS : Monotone S)
    (hf : ∀ j, EqOn (f (j + 1)) (f j) (S j)) {j k : ℕ} (hjk : j ≤ k) :
    EqOn (f k) (f j) (S j) := by
  induction k, hjk using Nat.le_induction with
  | base => exact eqOn_refl _ _
  | succ k hjk ih => exact fun t ht ↦ (hf k (hS hjk ht)).trans (ih ht)

/-- If each `f (j + 1)` agrees with `f j` on `(-∞, T j]` and maps `[T j, T (j + 1)]` outside
`K j`, for an increasing family of sets `K`, then every later `f k` maps `[T j, T k]` outside
`K j`. -/
theorem mapsTo_Icc_compl_of_eqOn_succ [LinearOrder α] {T : ℕ → α} {K : ℕ → Set β}
    (hK : Monotone K) (hf : ∀ j, EqOn (f (j + 1)) (f j) (Iic (T j)))
    (hfK : ∀ j, MapsTo (f (j + 1)) (Icc (T j) (T (j + 1))) (K j)ᶜ) {j k : ℕ} (hjk : j < k) :
    MapsTo (f k) (Icc (T j) (T k)) (K j)ᶜ := by
  induction k, hjk using Nat.le_induction with
  | base => exact hfK j
  | succ k hjk ih =>
    intro t ht
    rcases le_total t (T k) with htk | htk
    · rw [mem_compl_iff, hf k htk]
      exact ih ⟨ht.1, htk⟩
    · exact fun h ↦ hfK k ⟨htk, ht.2⟩ (hK (by omega) h)

end Set

end
