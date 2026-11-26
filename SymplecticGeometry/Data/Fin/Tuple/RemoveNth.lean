/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Data.Fin.VecNotation

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
equalities. Both proofs read the entries off their values, by `Fin.append_apply_eq_dite`, the
form of Mathlib's `Matrix.vecAppend_eq_ite` for `Fin.append`.
-/

public section

namespace Fin

variable {α : Type*}

/-- The entry of `Fin.append a c` at `p` is that of `a` at `p` if `p < k`, and otherwise that of
`c` at `p - k`. -/
theorem append_apply_eq_dite {k l : ℕ} (a : Fin k → α) (c : Fin l → α) (p : Fin (k + l)) :
    append a c p = if h : (p : ℕ) < k then a ⟨p, h⟩ else c ⟨p - k, by omega⟩ :=
  congrFun (Matrix.vecAppend_eq_ite rfl a c) p

/-- Removing the entry `i` of the first block of `Fin.append a c` (an entry of `a`) gives the
concatenation of `Fin.removeNth i a` with `c`. -/
theorem removeNth_cast_castAdd_append {k m : ℕ} (a : Fin (k + 1) → α) (c : Fin m → α)
    (i : Fin (k + 1)) (h : k + m + 1 = k + 1 + m) :
    removeNth (Fin.cast h.symm (castAdd m i)) (append a c ∘ Fin.cast h) =
      append (removeNth i a) c := by
  funext q
  by_cases h1 : (q : ℕ) < i <;> by_cases h2 : (q : ℕ) < k <;>
    simp only [removeNth, succAbove, lt_def, val_castSucc, val_cast, val_castAdd, h1, ↓reduceIte,
      Function.comp_apply, append_apply_eq_dite, val_succ, Nat.add_lt_add_iff_right, h2,
      ↓reduceDIte, castSucc_mk, succ_mk, Nat.reduceSubDiff] <;>
    first | omega | (split_ifs <;> first | omega | rfl)

/-- Removing the entry `j` of the second block of `Fin.append a c` (an entry of `c`) gives the
concatenation of `a` with `Fin.removeNth j c`. -/
theorem removeNth_cast_natAdd_append {k n N : ℕ} (a : Fin k → α) (c : Fin (n + 1) → α)
    (j : Fin (n + 1)) (h₁ : N + 1 = k + (n + 1)) (h₂ : N = k + n) :
    removeNth (Fin.cast h₁.symm (natAdd k j)) (append a c ∘ Fin.cast h₁) =
      append a (removeNth j c) ∘ Fin.cast h₂ := by
  funext q
  by_cases h1 : (q : ℕ) < k + j <;> by_cases h2 : (q : ℕ) < k <;>
    simp only [removeNth, succAbove, lt_def, val_castSucc, val_cast, val_natAdd, h1, ↓reduceIte,
      Function.comp_apply, cast_castSucc, cast_succ_eq, Nat.add_eq, append_apply_eq_dite, val_succ,
      h2, ↓reduceDIte, castSucc_mk, succ_mk] <;>
    first | omega | (split_ifs <;> first | omega | rfl) |
      (rw [dite_eq_right (by omega), ite_eq_right (by omega)]; congr 3; omega)

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

end Fin

end
