/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import TauCeti.Data.Fin.Basic

/-!
# Removing an entry of a concatenated tuple

For tuples `a : Fin k → α` and `c : Fin l → α`, the entries of `Fin.append a c` are those of `a`
followed by those of `c`. Removing one entry of the concatenation removes it from the block it
lies in:

* `Fin.removeNth_cast_castAdd_append`: removing the entry `i` of the first block gives
  `Fin.append (Fin.removeNth i a) c`;
* `Fin.removeNth_cast_natAdd_append`: removing the entry `j` of the second block gives
  `Fin.append a (Fin.removeNth j c)`.

The lengths are written so that they match the degrees of differential forms on a product, where
`Fin.removeNth` acts on `Fin (N + 1)` and the blocks have lengths `k + 1` and `m`, or `k` and
`n + 1`, with `N + 1` equal to their sum only propositionally; the casts `Fin.cast` carry these
equalities. Both lemmas undo Tau Ceti's `Fin.insertNth_append_castAdd` and
`Fin.insertNth_append_natAdd`, which insert an entry into a block of a concatenation, by
Mathlib's `Fin.removeNth_insertNth` and `Fin.insertNth_self_removeNth`. Splitting an
alternating sum over the entries of a concatenation into the sums over its two blocks
(`Fin.sum_neg_one_pow_smul_removeNth_append`, and `Fin.sum_neg_one_pow_smul_removeNth_append_zero`
when the second block is empty) follows.

For a block of one entry, `Fin.snoc f z`, removing an entry of `f` keeps `z` last:
`Fin.removeNth_castSucc_snoc`.
-/

public section

namespace Fin

variable {α : Type*}

/-- Removing the entry `i` of the first block of `Fin.append a c` (an entry of `a`) gives the
concatenation of `Fin.removeNth i a` with `c`. -/
theorem removeNth_cast_castAdd_append {k m : ℕ} (a : Fin (k + 1) → α) (c : Fin m → α)
    (i : Fin (k + 1)) (h : k + m + 1 = k + 1 + m) :
    removeNth (Fin.cast h.symm (castAdd m i)) (append a c ∘ Fin.cast h) =
      append (removeNth i a) c := by
  have h := insertNth_append_castAdd i (a i) (removeNth i a) c
  rw [insertNth_self_removeNth] at h
  rw [← h, removeNth_insertNth]

/-- Removing the entry `j` of the second block of `Fin.append a c` (an entry of `c`) gives the
concatenation of `a` with `Fin.removeNth j c`. -/
theorem removeNth_cast_natAdd_append {k n N : ℕ} (a : Fin k → α) (c : Fin (n + 1) → α)
    (j : Fin (n + 1)) (h₁ : N + 1 = k + (n + 1)) (h₂ : N = k + n) :
    removeNth (Fin.cast h₁.symm (natAdd k j)) (append a c ∘ Fin.cast h₁) =
      append a (removeNth j c) ∘ Fin.cast h₂ := by
  subst h₂
  have h := insertNth_append_natAdd j (c j) a (removeNth j c)
  rw [insertNth_self_removeNth] at h
  rw [← h]
  exact removeNth_insertNth _ _ _

/-- **An alternating sum over the entries of a concatenation, split into its blocks.** For
`a : Fin (k + 1) → α` and `c : Fin (n + 1) → α` with concatenation `V`, the alternating sum over
`p` of `δ (V without its entry p) (V p)` is the alternating sum over the entries of `a` plus
`(-1) ^ (k + 1)` times the alternating sum over the entries of `c`. This is the shape of the
coordinate formula for the exterior derivative on a family of vectors listed in two blocks. -/
theorem sum_neg_one_pow_smul_removeNth_append {G : Type*} [AddCommGroup G] {k n : ℕ}
    (δ : (Fin (k + (n + 1)) → α) → α → G) (a : Fin (k + 1) → α) (c : Fin (n + 1) → α)
    (h₁ : k + (n + 1) + 1 = k + 1 + (n + 1)) (h₂ : k + (n + 1) = k + 1 + n) :
    ∑ p : Fin (k + (n + 1) + 1), (-1 : ℤ) ^ (p : ℕ) •
        δ (p.removeNth (append a c ∘ Fin.cast h₁)) ((append a c ∘ Fin.cast h₁) p) =
      ∑ i : Fin (k + 1), (-1 : ℤ) ^ (i : ℕ) • δ (append (removeNth i a) c) (a i) +
        (-1 : ℤ) ^ (k + 1) • ∑ j : Fin (n + 1), (-1 : ℤ) ^ (j : ℕ) •
          δ (append a (removeNth j c) ∘ Fin.cast h₂) (c j) := by
  rw [← sum_congr' _ h₁.symm, sum_univ_add, Finset.smul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [removeNth_cast_castAdd_append a c i h₁]
    simp
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [removeNth_cast_natAdd_append a c j h₁ h₂, smul_smul, ← pow_add]
    simp

/-- The case of `sum_neg_one_pow_smul_removeNth_append` where the second block is empty: the
alternating sum over the entries of `Fin.append a c`, for `c : Fin 0 → α`, is the alternating
sum over the entries of `a`. -/
theorem sum_neg_one_pow_smul_removeNth_append_zero {G : Type*} [AddCommGroup G] {k : ℕ}
    (δ : (Fin (k + 0) → α) → α → G) (a : Fin (k + 1) → α) (c : Fin 0 → α)
    (h : k + 0 + 1 = k + 1 + 0) :
    ∑ p : Fin (k + 0 + 1), (-1 : ℤ) ^ (p : ℕ) •
        δ (p.removeNth (append a c ∘ Fin.cast h)) ((append a c ∘ Fin.cast h) p) =
      ∑ i : Fin (k + 1), (-1 : ℤ) ^ (i : ℕ) • δ (append (removeNth i a) c) (a i) := by
  rw [← sum_congr' _ h.symm, sum_univ_add, sum_univ_zero, add_zero]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [removeNth_cast_castAdd_append a c i h, Function.comp_apply, cast_cast, cast_eq_self,
    append_left]
  simp

/-- Removing an entry `i` of `f` from `Fin.snoc f z` gives `Fin.snoc (Fin.removeNth i f) z`: the
last entry stays last. -/
@[simp]
theorem removeNth_castSucc_snoc {n : ℕ} (i : Fin (n + 1)) (f : Fin (n + 1) → α) (z : α) :
    removeNth i.castSucc (snoc f z : Fin (n + 2) → α) = snoc (removeNth i f) z := by
  funext m
  refine lastCases ?_ (fun m ↦ ?_) m <;> simp [removeNth_apply]

end Fin

end
