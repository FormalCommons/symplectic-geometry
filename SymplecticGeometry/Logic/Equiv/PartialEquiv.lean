/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Logic.Equiv.PartialEquiv

/-!
# Partial equivalences: ranges, and transport of functions

A partial equivalence `e` defined on all of `α` has its target as range
(`PartialEquiv.range_eq_target_of_source_eq_univ`).

For a partial equivalence `e : PartialEquiv α β` and a function `χ` on `α`, the function
`χ ∘ e.symm` on `e '' W`, extended by `0` off `e '' W`, takes the value `χ z` at `e z` for each
`z ∈ W` in the source of `e` (`PartialEquiv.indicator_image_comp_symm_apply_self`), and likewise
on the whole target of `e` (`PartialEquiv.indicator_target_comp_symm_apply_self`). They give the
values of extensions by zero along a chart, such as the one of
`PartialDiffeomorph.contMDiff_indicator_image_comp_symm`, at the images of the points of `W`.
-/

public section

open Set

namespace PartialEquiv

variable {α β M : Type*} [Zero M] (e : PartialEquiv α β)

/-- A partial equivalence whose source is all of `α` has its target as range. -/
theorem range_eq_target_of_source_eq_univ (h : e.source = univ) : range e = e.target := by
  rw [← image_univ, ← h, e.image_source_eq_target]

/-- The function `χ ∘ e.symm` on `e '' W`, extended by `0` off `e '' W`, takes the value `χ z`
at `e z` for each `z ∈ W` in the source of `e`. -/
theorem indicator_image_comp_symm_apply_self (χ : α → M) {W : Set α} {z : α} (hz : z ∈ W)
    (hzs : z ∈ e.source) : (e '' W).indicator (fun y ↦ χ (e.symm y)) (e z) = χ z := by
  rw [indicator_of_mem (mem_image_of_mem _ hz), e.left_inv hzs]

/-- The function `χ ∘ e.symm` on the target of `e`, extended by `0` off it, takes the value `χ z`
at `e z` for each `z` in the source of `e`. -/
theorem indicator_target_comp_symm_apply_self (χ : α → M) {z : α} (hz : z ∈ e.source) :
    e.target.indicator (fun y ↦ χ (e.symm y)) (e z) = χ z := by
  rw [indicator_of_mem (e.map_source hz), e.left_inv hz]

end PartialEquiv

end
