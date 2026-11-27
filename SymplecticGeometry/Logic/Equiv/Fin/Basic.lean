/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Tuples indexed by a sum and `finSumFinEquiv`

A tuple `Sum.elim u w` indexed by `Fin r ⊕ Fin m`, reindexed along `finSumFinEquiv.symm`, is the
tuple `Fin.append u w` indexed by `Fin (r + m)` (`Fin.sumElim_comp_finSumFinEquiv_symm`). This is
the bridge between constructions on index types `ι ⊕ κ`, such as currying along a sum, and those
on `Fin (r + m)`, such as `Fin.append`.
-/

public section

namespace Fin

/-- Reindexing `Sum.elim u w` along `finSumFinEquiv.symm` gives `Fin.append u w`. -/
@[simp]
theorem sumElim_comp_finSumFinEquiv_symm {α : Type*} {r m : ℕ} (u : Fin r → α) (w : Fin m → α) :
    Sum.elim u w ∘ finSumFinEquiv.symm = Fin.append u w := by
  funext p
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) p <;> simp

end Fin

end
