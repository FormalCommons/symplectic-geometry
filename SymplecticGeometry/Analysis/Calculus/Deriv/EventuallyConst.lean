/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Derivatives of functions constant on two half-lines

A function of a real variable that is constant on `(-∞, a]` and on `[b, ∞)` is locally constant
near every point outside `[a, b]`, so its derivative vanishes there. Such functions are the cut-off
functions that interpolate between two constant values on an interval.

## Main results

* `deriv_eq_zero_of_notMem_Icc`: a function constant on `(-∞, a]` and on `[b, ∞)` has derivative
  zero outside `[a, b]`.
-/

public section

open Set Filter

/-- A function of a real variable that is constant on `(-∞, a]` and on `[b, ∞)` has derivative
zero outside `[a, b]`. -/
theorem deriv_eq_zero_of_notMem_Icc {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {a b : ℝ} {u w : F} (hfa : ∀ t ≤ a, f t = u) (hfb : ∀ t ≥ b, f t = w) {t : ℝ}
    (ht : t ∉ Icc a b) : deriv f t = 0 := by
  rcases not_and_or.1 ht with h | h
  · have : f =ᶠ[nhds t] fun _ ↦ u :=
      (eventually_lt_nhds (not_le.1 h)).mono fun s hs ↦ hfa s hs.le
    rw [this.deriv_eq, deriv_const]
  · have : f =ᶠ[nhds t] fun _ ↦ w :=
      (eventually_gt_nhds (not_le.1 h)).mono fun s hs ↦ hfb s hs.le
    rw [this.deriv_eq, deriv_const]

end
