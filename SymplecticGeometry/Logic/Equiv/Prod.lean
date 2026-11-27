/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Logic.Equiv.Defs

/-!
# Equivalences of a product over its first factor

An equivalence `Φ` of `X × F` that preserves the first coordinate, so that it acts fibre by fibre
over `X`, has an inverse that preserves it too (`Equiv.fst_symm_apply_of_forall_fst_apply`).
-/

public section

namespace Equiv

/-- An equivalence of `X × F` that preserves the first coordinate has an inverse that preserves
it too. -/
theorem fst_symm_apply_of_forall_fst_apply {X F : Type*} {Φ : X × F ≃ X × F}
    (hΦ : ∀ q, (Φ q).1 = q.1) (q : X × F) : (Φ.symm q).1 = q.1 := by
  simpa using (hΦ (Φ.symm q)).symm

end Equiv

end
