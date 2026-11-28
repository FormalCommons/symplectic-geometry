/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Complex.LeviForm.Basic

/-!
# The difference rule and constants for the Levi form of functions

Tau Ceti's `TauCeti.leviForm` of a real function on a complex normed space comes with the sum
rule `TauCeti.leviForm_add` and the rule `TauCeti.leviForm_neg` for negation. This file adds the
rule for a difference, `L(f - g) = L f - L g` at a point where `f` and `g` are of class `C²`
(`TauCeti.leviForm_sub`), the analogue for functions of Tau Ceti's
`LinearMap.BilinForm.leviForm_sub` for bilinear forms, and the invariance of the Levi form under
adding a constant on either side, `L(c + f) = L(f + c) = L f`, which needs no smoothness
(`TauCeti.leviForm_const_add`, `TauCeti.leviForm_add_const`).
-/

public section

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {f g : V → ℝ} {x : V}

/-- **The difference rule.** At a point where `f` and `g` are of class `C²`, the Levi form of
`f - g` is the difference of their Levi forms. -/
theorem leviForm_sub (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    leviForm (f - g) x = leviForm f x - leviForm g x := by
  -- `hg.neg` would elaborate to `fun y ↦ -g y`, so state the form `leviForm_add` needs.
  have hg' : ContDiffAt ℝ 2 (-g) x := hg.neg
  rw [sub_eq_add_neg, leviForm_add hf hg', leviForm_neg, sub_eq_add_neg]

/-- Adding a constant to a function does not change its Levi form. -/
@[simp]
theorem leviForm_const_add (c : ℝ) (f : V → ℝ) (x : V) :
    leviForm (fun y ↦ c + f y) x = leviForm f x := by
  have h : fderiv ℝ (fun y ↦ c + f y) = fderiv ℝ f := funext fun _ ↦ fderiv_const_add c
  rw [leviForm_def, leviForm_def, h]

/-- Adding a constant on the right to a function does not change its Levi form. -/
@[simp]
theorem leviForm_add_const (f : V → ℝ) (c : ℝ) (x : V) :
    leviForm (fun y ↦ f y + c) x = leviForm f x := by
  have h : fderiv ℝ (fun y ↦ f y + c) = fderiv ℝ f := funext fun _ ↦ fderiv_add_const c
  rw [leviForm_def, leviForm_def, h]

end TauCeti

end
