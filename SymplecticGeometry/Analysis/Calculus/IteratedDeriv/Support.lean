/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic

/-!
# Support of iterated derivatives

The iterated derivatives of a compactly supported function of one variable have compact support
(`HasCompactSupport.iteratedDeriv`), and their supports lie in the topological support of the
function (`support_iteratedDeriv_subset`): the one-variable forms of Tau Ceti's
`HasCompactSupport.iteratedFDeriv_apply` and Mathlib's `support_iteratedFDeriv_subset`, from
which they follow.
-/

public section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {f : 𝕜 → E}

/-- The iterated derivatives of a compactly supported function have compact support. -/
protected theorem HasCompactSupport.iteratedDeriv (hf : HasCompactSupport f) (n : ℕ) :
    HasCompactSupport (iteratedDeriv n f) := by
  simpa only [← iteratedDeriv_eq_iteratedFDeriv] using
    hf.iteratedFDeriv_apply (𝕜 := 𝕜) (n := n) fun _ ↦ 1

/-- The support of an iterated derivative lies in the topological support of the function. -/
theorem support_iteratedDeriv_subset (n : ℕ) :
    Function.support (iteratedDeriv n f) ⊆ tsupport f := fun x hx ↦
  support_iteratedFDeriv_subset (𝕜 := 𝕜) n fun h ↦ hx (by simp [iteratedDeriv_eq_iteratedFDeriv, h])

end
