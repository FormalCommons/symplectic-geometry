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
# Consequences of the mean value theorem on the real line

A real function that has a positive derivative at each point of a convex set `D ⊆ ℝ` is strictly
increasing on `D` (`StrictMonoOn.of_forall_hasDerivAt_pos`). The derivative is only asked to exist
pointwise, as `∃ d, 0 < d ∧ HasDerivAt f d x`, which is the form in which constructions by the
chain rule usually give it. This is Mathlib's mean value theorem `strictMonoOn_of_deriv_pos`, to
which the proof reduces.

A real function that is bounded below on `[a, ∞)`, and whose derivative there is at most `c`,
has `0 ≤ c` (`nonneg_of_bddBelow_of_hasDerivAt_le`): for `c < 0`, Mathlib's
`Convex.image_sub_le_mul_sub_of_deriv_le` makes it fall below every bound.
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

open Set in
/-- If `f : ℝ → ℝ` is bounded below on `[a, ∞)` and has a derivative `f' t ≤ c` at every
`t ≥ a`, then `0 ≤ c`. -/
theorem nonneg_of_bddBelow_of_hasDerivAt_le {f f' : ℝ → ℝ} {a c : ℝ}
    (hb : BddBelow (f '' Ici a)) (hf : ∀ t ∈ Ici a, HasDerivAt f (f' t) t)
    (hle : ∀ t ∈ Ici a, f' t ≤ c) : 0 ≤ c := by
  by_contra! hc
  obtain ⟨m, hm⟩ := hb
  -- On `[a, ∞)`, `f t ≤ f a + c * (t - a)`, which falls below `m` at the time `t` below.
  have hdec (t : ℝ) (ht : a ≤ t) : f t - f a ≤ c * (t - a) :=
    (convex_Ici a).image_sub_le_mul_sub_of_deriv_le
      (fun s hs ↦ (hf s hs).continuousAt.continuousWithinAt)
      (fun s hs ↦ (hf s (interior_subset hs)).differentiableAt.differentiableWithinAt)
      (fun s hs ↦ (hf s (interior_subset hs)).deriv ▸ hle s (interior_subset hs))
      a self_mem_Ici t ht ht
  have hma : m ≤ f a := hm (mem_image_of_mem f self_mem_Ici)
  set t := a + (f a - m + 1) / -c
  have hta : a ≤ t := le_add_of_nonneg_right (div_nonneg (by linarith) (by linarith))
  have hmt : m ≤ f t := hm (mem_image_of_mem f hta)
  have hct : c * (t - a) = -(f a - m + 1) := by
    simp only [t, add_sub_cancel_left]
    field_simp [hc.ne]
  linarith [hdec t hta]

end
