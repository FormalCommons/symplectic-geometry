/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Strict monotonicity from a positive derivative

A real function that has a positive derivative at each point of a convex set `D ⊆ ℝ` is strictly
increasing on `D` (`StrictMonoOn.of_forall_hasDerivAt_pos`). The derivative is only asked to exist
pointwise, as `∃ d, 0 < d ∧ HasDerivAt f d x`, which is the form in which constructions by the
chain rule usually give it. This is Mathlib's mean value theorem `strictMonoOn_of_deriv_pos`, to
which the proof reduces.
-/

public section

/-- A function `f : ℝ → ℝ` that has a positive derivative at every point of a convex set `D` is
strictly increasing on `D`. -/
theorem StrictMonoOn.of_forall_hasDerivAt_pos {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (h : ∀ x ∈ D, ∃ d, 0 < d ∧ HasDerivAt f d x) : StrictMonoOn f D := by
  refine strictMonoOn_of_deriv_pos hD (fun x hx ↦ ?_) fun x hx ↦ ?_
  · obtain ⟨d, -, hd⟩ := h x hx
    exact hd.continuousAt.continuousWithinAt
  · obtain ⟨d, hd0, hd⟩ := h x (interior_subset hx)
    rwa [hd.deriv]

end
