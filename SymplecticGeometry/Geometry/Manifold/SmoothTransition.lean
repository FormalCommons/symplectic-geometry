/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Geometry.Manifold.Instances.Icc
import SymplecticGeometry.Geometry.Manifold.Instances.Icc
public import TauCeti.Geometry.Manifold.Instances.Icc
import TauCeti.Analysis.SpecialFunctions.SmoothTransition

/-!
# The smooth transition function as a smooth map to the unit interval

Tau Ceti's `unitInterval.smoothTransition` is Mathlib's `Real.smoothTransition` as a map
`ℝ → unitInterval`, which is `0` on `(-∞, 0]` and `1` on `[1, ∞)`. This file shows that it is
surjective and sends `(0, 1)` onto `(0, 1)`, and that it is smooth for the manifold-with-boundary
structure of the unit interval, by Tau Ceti's `ContMDiff.smoothTransition`. Its derivative sends
the unit vector `1` of `ℝ` to `deriv Real.smoothTransition u` times the unit tangent vector of the
interval (`unitInterval.mfderiv_smoothTransition_one`). Tau Ceti's
`TauCeti.collaredSmoothTransitionUnit` is the analogous map for the reparametrization
`t ↦ Real.smoothTransition (2 * t - 1 / 2)`. Since that map is constant near both ends of the
unit interval, Tau Ceti's `TauCeti.collaredFirstHalf` composed with the clamp `Set.projIcc 0 1`
is `t ↦ collaredSmoothTransitionUnit (2 * t)` on all of `ℝ` (`TauCeti.collaredFirstHalf_projIcc`),
and `collaredFirstHalf` is `0` near time `0` and `1` near time `1`
(`TauCeti.eventually_collaredFirstHalf_eq_zero`, `TauCeti.eventually_collaredFirstHalf_eq_one`).
The second half `TauCeti.collaredSecondHalf` leaves `0` only once the first half has reached
`1` (`TauCeti.collaredFirstHalf_eq_one_of_collaredSecondHalf_ne_zero`).
-/

public noncomputable section

open scoped Manifold ContDiff Topology

namespace unitInterval

/-- The map `unitInterval.smoothTransition : ℝ → unitInterval` is surjective. -/
theorem smoothTransition_surjective : Function.Surjective smoothTransition := fun t ↦ by
  obtain ⟨u, -, hu⟩ := Real.smoothTransition.surjOn_Icc t.property
  exact ⟨u, Subtype.ext ((coe_smoothTransition u).trans hu)⟩

/-- The map `unitInterval.smoothTransition : ℝ → unitInterval` sends `(0, 1)` onto the open
interval `(0, 1)`. -/
theorem surjOn_smoothTransition_Ioo :
    Set.SurjOn smoothTransition (Set.Ioo 0 1) (Set.Ioo 0 1) := fun t ht ↦ by
  obtain ⟨u, hu, hut⟩ := intermediate_value_Ioo zero_le_one
    Real.smoothTransition.continuous.continuousOn
    (by
      rw [Real.smoothTransition.zero, Real.smoothTransition.one]
      exact ⟨coe_pos.2 ht.1, coe_lt_one.2 ht.2⟩)
  exact ⟨u, hu, Subtype.ext ((coe_smoothTransition u).trans hut)⟩

/-- The map `unitInterval.smoothTransition : ℝ → unitInterval` is `C^n` for every `n ≤ ∞`. -/
theorem contMDiff_smoothTransition {n : ℕ∞ω} (hn : n ≤ ∞) :
    ContMDiff 𝓘(ℝ) (𝓡∂ 1) n smoothTransition :=
  (contMDiff_id.smoothTransition hn).congr fun u ↦ Subtype.ext (coe_smoothTransition u)

/-- The derivative of `s = unitInterval.smoothTransition : ℝ → unitInterval` at `u` sends `1` to
`s'(u)` times the unit tangent vector `1` of the interval, where
`s' = deriv Real.smoothTransition`. -/
theorem mfderiv_smoothTransition_one (u : ℝ) :
    mfderiv 𝓘(ℝ) (𝓡∂ 1) smoothTransition u 1 = deriv Real.smoothTransition u • 1 := by
  refine SymplecticGeometry.mfderiv_apply_eq_smul_one_Icc
    ((contMDiff_smoothTransition le_rfl).mdifferentiableAt (by simp)) ?_
  have hc : Subtype.val ∘ smoothTransition = Real.smoothTransition :=
    funext coe_smoothTransition
  rw [hc, ← mvfderiv_apply_eq_mfderiv_apply, TauCeti.mvfderiv_eq_fderiv_apply]
  -- The goal is an equation in `TangentSpace 𝓘(ℝ) _`; `F := ℝ` states the lemma over `ℝ`.
  exact fderiv_apply_one_eq_deriv (F := ℝ)

end unitInterval

namespace TauCeti

/-- Clamping the time to `[0, 1]` does not change the first half of a stationary-time
concatenation: `collaredFirstHalf` at the clamp `Set.projIcc 0 1 t` of a real number `t` is
`collaredSmoothTransitionUnit (2 * t)`. -/
theorem collaredFirstHalf_projIcc {n : ℕ∞ω} (hn : n ≤ ∞) (t : ℝ) :
    collaredFirstHalf hn (Set.projIcc 0 1 zero_le_one t) =
      collaredSmoothTransitionUnit (2 * t) := by
  rw [collaredFirstHalf_apply, Set.coe_projIcc]
  rcases le_total t 0 with h | h
  · rw [max_eq_left (min_le_of_right_le h),
      collaredSmoothTransitionUnit_eq_zero_of_le (by norm_num),
      collaredSmoothTransitionUnit_eq_zero_of_le (by linarith)]
  rcases le_total t 1 with h' | h'
  · rw [min_eq_right h', max_eq_right h]
  · rw [min_eq_left h', max_eq_right zero_le_one,
      collaredSmoothTransitionUnit_eq_one_of_ge (by norm_num),
      collaredSmoothTransitionUnit_eq_one_of_ge (by linarith)]

/-- The first half of a stationary-time concatenation is `0` near time `0`. -/
theorem eventually_collaredFirstHalf_eq_zero {n : ℕ∞ω} (hn : n ≤ ∞) :
    ∀ᶠ t in 𝓝 (0 : unitInterval), collaredFirstHalf hn t = 0 := by
  filter_upwards [(continuous_subtypeVal.tendsto 0).eventually
    (gt_mem_nhds (by norm_num : ((0 : unitInterval) : ℝ) < 1 / 8))] with t ht
  exact collaredFirstHalf_eq_zero_of_le hn ht.le

/-- The first half of a stationary-time concatenation is `1` near time `1`. -/
theorem eventually_collaredFirstHalf_eq_one {n : ℕ∞ω} (hn : n ≤ ∞) :
    ∀ᶠ t in 𝓝 (1 : unitInterval), collaredFirstHalf hn t = 1 := by
  filter_upwards [(continuous_subtypeVal.tendsto 1).eventually
    (lt_mem_nhds (by norm_num : (3 / 8 : ℝ) < ((1 : unitInterval) : ℝ)))] with t ht
  exact collaredFirstHalf_eq_one_of_ge hn ht.le

/-- The second half of a stationary-time concatenation leaves `0` only once the first half has
reached `1`. -/
theorem collaredFirstHalf_eq_one_of_collaredSecondHalf_ne_zero {n : ℕ∞ω} (hn : n ≤ ∞)
    {t : unitInterval} (h : collaredSecondHalf hn t ≠ 0) : collaredFirstHalf hn t = 1 := by
  refine collaredFirstHalf_eq_one_of_ge hn ?_
  by_contra ht
  exact h (collaredSecondHalf_eq_zero_of_le hn (by linarith))

end TauCeti

end
