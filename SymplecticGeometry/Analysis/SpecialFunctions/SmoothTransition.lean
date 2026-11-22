/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.Inv
public import TauCeti.Geometry.Manifold.Instances.Icc.CollaredSmoothTransition
import TauCeti.Analysis.SpecialFunctions.SmoothTransition

/-!
# The derivative of the smooth transition function, and a reparametrization of time

Mathlib's `Real.smoothTransition` is `0` on `(-∞, 0]`, `1` on `[1, ∞)`, and the quotient
`f x / (f x + f (1 - x))` in between, with `f = expNegInvGlue`. Tau Ceti shows that its derivative
vanishes outside `[0, 1]`. This file shows that the derivative is positive on the open interval
`(0, 1)` (`Real.smoothTransition.deriv_pos`): by the quotient rule it is
`(f' x f (1 - x) + f x f' (1 - x)) / (f x + f (1 - x)) ^ 2`, and `f` and `f'` are positive on
`(0, ∞)`.

For Tau Ceti's `TauCeti.collaredSmoothTransition`, the map `s ↦ smoothTransition (2 * s - 1 / 2)`,
it adds that the map is `0` near `0` and `1` near `1`
(`TauCeti.collaredSmoothTransition_eventuallyEq_zero`,
`TauCeti.collaredSmoothTransition_eventuallyEq_one`), and that its derivative is positive at
every point where its value is neither `0` nor `1` (`TauCeti.deriv_collaredSmoothTransition_pos`).

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

namespace TauCeti

open Filter Topology

/-- `collaredSmoothTransition` is `0` on a neighbourhood of `0`. -/
theorem collaredSmoothTransition_eventuallyEq_zero :
    collaredSmoothTransition =ᶠ[𝓝 0] fun _ ↦ 0 := by
  filter_upwards [Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)] with s hs
  exact collaredSmoothTransition_eq_zero_of_le hs.le

/-- `collaredSmoothTransition` is `1` on a neighbourhood of `1`. -/
theorem collaredSmoothTransition_eventuallyEq_one :
    collaredSmoothTransition =ᶠ[𝓝 1] fun _ ↦ 1 := by
  filter_upwards [Ioi_mem_nhds (by norm_num : (3 / 4 : ℝ) < 1)] with s hs
  exact collaredSmoothTransition_eq_one_of_ge hs.le

/-- Where `collaredSmoothTransition` is neither `0` nor `1`, its derivative is positive. -/
theorem deriv_collaredSmoothTransition_pos {s : ℝ}
    (h₀ : collaredSmoothTransition s ≠ 0) (h₁ : collaredSmoothTransition s ≠ 1) :
    0 < deriv collaredSmoothTransition s := by
  rw [collaredSmoothTransition_def] at h₀ h₁
  have hs₀ : 0 < 2 * s - 1 / 2 :=
    lt_of_not_ge fun h ↦ h₀ (Real.smoothTransition.zero_of_nonpos h)
  have hs₁ : 2 * s - 1 / 2 < 1 :=
    lt_of_not_ge fun h ↦ h₁ (Real.smoothTransition.one_of_one_le h)
  have hd := (((hasDerivAt_id' s).const_mul 2).sub_const (1 / 2)).smoothTransition
    |>.congr_of_eventuallyEq (Eventually.of_forall fun r ↦ collaredSmoothTransition_def r)
  rw [hd.deriv, mul_one]
  exact mul_pos (Real.smoothTransition.deriv_pos hs₀ hs₁) two_pos

end TauCeti

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
