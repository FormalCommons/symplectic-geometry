/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# A second-order lower bound from a lower bound on the second derivative

A real function `h` whose second derivative is at least `m` on `[a, x]` lies above the quadratic
`t ↦ h a + h' a * (t - a) + m * (t - a) ^ 2 / 2` at `x`: integrate the bound twice, by two
monotonicity arguments.

## Main results

* `SymplecticGeometry.add_mul_sub_add_mul_sub_sq_div_two_le`: if `h` and `h'` are continuous on
  `[a, x]`, `h` has derivative `h'` and `h'` has derivative `h''` on `(a, x)`, and `m ≤ h''` on
  `(a, x)`, then `h a + h' a * (x - a) + m * (x - a) ^ 2 / 2 ≤ h x`.
-/

public section

namespace SymplecticGeometry

open Set

/-- A real function `h`, continuous on `[a, x]` with derivative `h'` on `(a, x)`, where `h'` is
continuous on `[a, x]` with derivative `h''` on `(a, x)` and `m ≤ h''` on `(a, x)`, satisfies
`h a + h' a * (x - a) + m * (x - a) ^ 2 / 2 ≤ h x`. -/
theorem add_mul_sub_add_mul_sub_sq_div_two_le {h h' h'' : ℝ → ℝ} {m a x : ℝ} (hax : a ≤ x)
    (hc : ContinuousOn h (Icc a x)) (hc' : ContinuousOn h' (Icc a x))
    (hh : ∀ t ∈ Ioo a x, HasDerivWithinAt h (h' t) (Ioo a x) t)
    (hh' : ∀ t ∈ Ioo a x, HasDerivWithinAt h' (h'' t) (Ioo a x) t)
    (hm : ∀ t ∈ Ioo a x, m ≤ h'' t) :
    h a + h' a * (x - a) + m * (x - a) ^ 2 / 2 ≤ h x := by
  -- First `t ↦ h' t - m (t - a)` is monotone, so `h' a + m (t - a) ≤ h' t` on `[a, x]`.
  have h1 : MonotoneOn (fun t ↦ h' t - m * (t - a)) (Icc a x) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t ↦ h'' t - m) (convex_Icc a x)
      (hc'.sub (by fun_prop))
      (fun t ht ↦ by
        rw [interior_Icc] at ht ⊢
        convert (hh' t ht).sub
          (((hasDerivAt_id t).sub_const a).const_mul m).hasDerivWithinAt using 1
        · ext; simp
        · ring)
      (fun t ht ↦ by
        rw [interior_Icc] at ht
        simpa using hm t ht)
  have hle : ∀ t ∈ Icc a x, h' a + m * (t - a) ≤ h' t := fun t ht ↦ by
    have := h1 (left_mem_Icc.2 hax) ht ht.1
    simp only [sub_self, mul_zero, sub_zero] at this
    linarith
  -- Then `t ↦ h t - h' a (t - a) - m (t - a)² / 2` is monotone on `[a, x]`.
  have h2 : MonotoneOn (fun t ↦ h t - h' a * (t - a) - m * (t - a) ^ 2 / 2) (Icc a x) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t ↦ h' t - h' a - m * (t - a))
      (convex_Icc a x) ((hc.sub (by fun_prop)).sub (by fun_prop))
      (fun t ht ↦ by
        rw [interior_Icc] at ht ⊢
        convert ((hh t ht).sub
          (((hasDerivAt_id t).sub_const a).const_mul (h' a)).hasDerivWithinAt).sub
          (((((hasDerivAt_id t).sub_const a).pow 2).const_mul m).div_const 2).hasDerivWithinAt
          using 1
        · ext; simp
        · simp; ring)
      (fun t ht ↦ by
        rw [interior_Icc] at ht
        linarith [hle t (Ioo_subset_Icc_self ht)])
  have := h2 (left_mem_Icc.2 hax) (right_mem_Icc.2 hax) hax
  simp only [sub_self, mul_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_div] at this
  linarith

end SymplecticGeometry

end
