/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.Inv
import TauCeti.Analysis.SpecialFunctions.SmoothTransition

/-!
# The derivative of the smooth transition function, and a reparametrization of time

Mathlib's `Real.smoothTransition` is `0` on `(-∞, 0]`, `1` on `[1, ∞)`, and the quotient
`f x / (f x + f (1 - x))` in between, with `f = expNegInvGlue`. Tau Ceti shows that its derivative
vanishes outside `[0, 1]`. This file shows that the derivative is positive on the open interval
`(0, 1)` (`Real.smoothTransition.deriv_pos`): by the quotient rule it is
`(f' x f (1 - x) + f x f' (1 - x)) / (f x + f (1 - x)) ^ 2`, and `f` and `f'` are positive on
`(0, ∞)`.

It also gives a smooth map `c : ℝ → ℝ` that is the identity on a closed interval `[a, b]` and
takes its values in the open interval `(a - ε, b + ε)`
(`SymplecticGeometry.exists_contDiff_eqOn_id_Icc_mem_Ioo`). It is `t ↦ m + f t * (t - m)` for
the midpoint `m` of `[a, b]` and a smooth bump `f` centred at `m`, equal to `1` on `[a, b]` and
supported in `(a - ε, b + ε)`. The construction adapts Tau Ceti's
`TauCeti.exists_contDiff_eventuallyEq_id_forall_mem_ball` to a prescribed interval on which the
map is the identity, including the degenerate case `a = b`.
-/

public section

namespace Real.smoothTransition

/-- The smooth transition function has positive derivative on the open interval `(0, 1)`. -/
theorem deriv_pos {x : ℝ} (h₀ : 0 < x) (h₁ : x < 1) : 0 < deriv smoothTransition x := by
  set f := expNegInvGlue
  have hx : 0 < f x := expNegInvGlue.pos_of_pos h₀
  have hy : 0 < f (1 - x) := expNegInvGlue.pos_of_pos (sub_pos.2 h₁)
  have hd₁ := expNegInvGlue.hasDerivAt x
  have hd₂ : HasDerivAt (fun y ↦ f (1 - y)) ((1 - x)⁻¹ ^ 2 * f (1 - x) * (-1)) x :=
    (expNegInvGlue.hasDerivAt (1 - x)).comp x ((hasDerivAt_id x).const_sub 1)
  have hd := hd₁.div (hd₁.add hd₂) (pos_denom x).ne'
  -- `smoothTransition` is, by definition, the quotient that `hd` differentiates.
  rw [show smoothTransition = f / (f + fun y ↦ f (1 - y)) from rfl, hd.deriv, Pi.add_apply]
  refine div_pos ?_ (pow_pos (pos_denom x) 2)
  have key : x⁻¹ ^ 2 * f x * (f x + f (1 - x)) -
      f x * (x⁻¹ ^ 2 * f x + (1 - x)⁻¹ ^ 2 * f (1 - x) * (-1)) =
      x⁻¹ ^ 2 * f x * f (1 - x) + f x * ((1 - x)⁻¹ ^ 2 * f (1 - x)) := by ring
  rw [key]
  positivity

end Real.smoothTransition

namespace SymplecticGeometry

open scoped ContDiff

/-- A smooth map `ℝ → ℝ` that is the identity on the closed interval `[a, b]` and takes its
values in the open interval `(a - ε, b + ε)`, for any `a ≤ b` and `ε > 0`. -/
theorem exists_contDiff_eqOn_id_Icc_mem_Ioo {a b ε : ℝ} (hab : a ≤ b) (hε : 0 < ε) :
    ∃ c : ℝ → ℝ, ContDiff ℝ ∞ c ∧ Set.EqOn c id (Set.Icc a b) ∧
      ∀ t, c t ∈ Set.Ioo (a - ε) (b + ε) := by
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (a + b) / 2 := ⟨_, rfl⟩
  let f : ContDiffBump m := ⟨(b - a) / 2 + ε / 2, (b - a) / 2 + ε, by linarith, by linarith⟩
  have hrIn : f.rIn = (b - a) / 2 + ε / 2 := rfl
  have hrOut : f.rOut = (b - a) / 2 + ε := rfl
  refine ⟨fun t ↦ m + f t * (t - m), contDiff_const.add (f.contDiff.mul (contDiff_id.sub
    contDiff_const)), fun t ht ↦ ?_, fun t ↦ ?_⟩
  · have : f t = 1 := f.one_of_mem_closedBall <| by
      rw [Metric.mem_closedBall, Real.dist_eq, abs_le, hrIn]
      constructor <;> linarith [ht.1, ht.2]
    simp [this]
  · suffices |f t * (t - m)| < (b - a) / 2 + ε by
      rw [abs_lt] at this
      dsimp only
      constructor <;> linarith [this.1, this.2]
    rw [← hrOut]
    rcases lt_or_ge (dist t m) f.rOut with ht | ht
    · rw [abs_mul, abs_of_nonneg f.nonneg, ← Real.dist_eq]
      exact (mul_le_of_le_one_left dist_nonneg f.le_one).trans_lt ht
    · rw [f.zero_of_le_dist ht, zero_mul, abs_zero]
      exact f.rOut_pos

end SymplecticGeometry

end
