/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Notation.Pi.Basic

/-!
# Folding a list of maps along a parameter supported at one index

Given maps `φ i : α → β → β` with `φ i 0 = id`, and a parameter `Pi.single k d` supported at
one index `k`, folding the maps `φ i (Pi.single k d i)` over a duplicate-free list `l` applies
only `φ k d`, and only if `k ∈ l`.

## Main results

* `List.foldr_pi_single_eq`: the fold equals `φ k d z` if `k ∈ l`, and `z` otherwise.
-/

public section

namespace List

/-- Applying in turn the maps `φ i (s i)`, for `i` in a duplicate-free list `l`, to `z`, where
`s` is supported at `k` and every `φ i 0` is the identity, gives `φ k (s k) z` if `k ∈ l` and
`z` if not. -/
theorem foldr_pi_single_eq {ι α β : Type*} [DecidableEq ι] [Zero α] {φ : ι → α → β → β}
    (hφ0 : ∀ i, φ i 0 = id) (k : ι) (d : α) (z : β) {l : List ι} (hl : l.Nodup) :
    l.foldr (fun i w ↦ φ i (Pi.single (M := fun _ ↦ α) k d i) w) z =
      if k ∈ l then φ k d z else z := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.nodup_cons] at hl
    rw [List.foldr_cons, ih hl.2]
    by_cases hik : i = k
    · subst hik
      simp [hl.1]
    · simp [hφ0, Ne.symm hik]

end List

end
