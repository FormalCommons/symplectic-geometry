/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Support of iterated derivatives

The iterated derivatives of a compactly supported function of one variable have compact support
(`HasCompactSupport.iteratedDeriv`), the one-variable form of Mathlib's
`HasCompactSupport.iteratedFDeriv`, from which it follows.
-/

public section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {f : 𝕜 → E}

/-- The iterated derivatives of a compactly supported function have compact support. -/
protected theorem HasCompactSupport.iteratedDeriv (hf : HasCompactSupport f) (n : ℕ) :
    HasCompactSupport (iteratedDeriv n f) := by
  have h : iteratedDeriv n f = (fun L ↦ L fun _ ↦ 1) ∘ iteratedFDeriv 𝕜 n f :=
    funext fun _ ↦ iteratedDeriv_eq_iteratedFDeriv
  rw [h]
  exact (hf.iteratedFDeriv n).comp_left (by simp)

end
