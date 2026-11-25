/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Friedrichs.Basic

/-!
# The Cauchy–Schwarz inequality for the Friedrichs form

Let `S` be a symmetric partial operator on a real Hilbert space `E`, bounded below by `γ`, and
let `q = LinearPMap.friedrichsForm` be the closed form that Tau Ceti builds on its form domain
`LinearPMap.FriedrichsSpace S γ`. This file proves that `|q(u, v)| ≤ ‖u‖ * ‖v‖` when
`0 ≤ γ ≤ 1`.

For such `γ`, Tau Ceti's `LinearPMap.mul_norm_sq_le_re_friedrichsForm` makes `q` nonnegative, and
`LinearPMap.re_friedrichsForm_self` bounds `q(u, u)` by `‖u‖ ^ 2`. The form is symmetric by
`LinearPMap.friedrichsForm_eq_star`, so the Cauchy–Schwarz inequality for nonnegative bilinear
forms, `LinearMap.BilinForm.apply_mul_apply_le_of_forall_zero_le`, gives the bound.

## Main results

* `LinearPMap.abs_friedrichsForm_le`: `|q(u, v)| ≤ ‖u‖ * ‖v‖` for `0 ≤ γ ≤ 1`.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, 2nd ed., Springer, 1976, Chapter VI.
-/

public section

namespace LinearPMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {S : E →ₗ.[ℝ] E} {γ : ℝ}

/-- **Cauchy–Schwarz inequality for the Friedrichs form**: for a real symmetric partial operator
bounded below by `γ` with `0 ≤ γ ≤ 1`, the Friedrichs form satisfies `|q(u, v)| ≤ ‖u‖ * ‖v‖` on
the form domain. -/
theorem abs_friedrichsForm_le (hS : S.IsSymmetricBoundedBelow γ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1)
    (u v : FriedrichsSpace S γ hS) :
    |friedrichsForm hS u v| ≤ ‖u‖ * ‖v‖ := by
  let B : FriedrichsSpace S γ hS →L[ℝ] FriedrichsSpace S γ hS →L[ℝ] ℝ := friedrichsForm hS
  have hnonneg (w : FriedrichsSpace S γ hS) : 0 ≤ B w w := by
    have h := mul_norm_sq_le_re_friedrichsForm hS w
    rw [RCLike.re_to_real] at h
    exact le_trans (by positivity) h
  have hle (w : FriedrichsSpace S γ hS) : B w w ≤ ‖w‖ ^ 2 := by
    have h := re_friedrichsForm_self hS w
    rw [RCLike.re_to_real] at h
    -- `B` is `friedrichsForm hS` read as a real bilinear map; `nlinarith` needs the same term.
    change friedrichsForm hS w w ≤ _
    nlinarith [sq_nonneg ‖friedrichsInclusion hS w‖]
  have hcs : B u v * B v u ≤ B u u * B v v :=
    LinearMap.BilinForm.apply_mul_apply_le_of_forall_zero_le B.toLinearMap₁₂ hnonneg u v
  have hcomm : B v u = B u v := by
    simpa using friedrichsForm_eq_star hS v u
  rw [hcomm] at hcs
  refine abs_le_of_sq_le_sq ?_ (by positivity)
  rw [mul_pow]
  calc B u v ^ 2 ≤ B u u * B v v := by rwa [sq]
    _ ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 := mul_le_mul (hle u) (hle v) (hnonneg v) (sq_nonneg _)

end LinearPMap

end
