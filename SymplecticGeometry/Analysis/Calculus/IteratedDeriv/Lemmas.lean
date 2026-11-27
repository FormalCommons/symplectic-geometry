/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Iterated derivatives of a function shifted by a constant

Adding or subtracting a constant on the right does not change the iterated derivatives of order
at least one: `iteratedDeriv_add_const` and `iteratedDeriv_sub_const`, the counterparts of
Mathlib's `iteratedDeriv_const_add`, from which they follow.
-/

public section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] {n : ℕ} {x : 𝕜} {f : 𝕜 → F}

/-- For `0 < n`, the `n`-th iterated derivative of `z ↦ f z + c` is that of `f`. -/
theorem iteratedDeriv_add_const (hn : 0 < n) (c : F) :
    iteratedDeriv n (fun z ↦ f z + c) x = iteratedDeriv n f x := by
  simpa only [add_comm] using iteratedDeriv_const_add (f := f) (x := x) hn c

/-- For `0 < n`, the `n`-th iterated derivative of `z ↦ f z - c` is that of `f`. -/
theorem iteratedDeriv_sub_const (hn : 0 < n) (c : F) :
    iteratedDeriv n (fun z ↦ f z - c) x = iteratedDeriv n f x := by
  simpa only [sub_eq_add_neg] using iteratedDeriv_add_const (f := f) (x := x) hn (-c)

end
