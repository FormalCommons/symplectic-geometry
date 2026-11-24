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

/-!
# The smooth transition function as a smooth map to the unit interval

Tau Ceti's `unitInterval.smoothTransition` is Mathlib's `Real.smoothTransition` as a map
`ℝ → unitInterval`, which is `0` on `(-∞, 0]` and `1` on `[1, ∞)`. This file shows that it is
surjective and sends `(0, 1)` onto `(0, 1)`, and that it is smooth for the manifold-with-boundary
structure of the unit interval, by Tau Ceti's `ContMDiff.smoothTransition`. Its derivative sends
the unit vector `1` of `ℝ` to `deriv Real.smoothTransition u` times the unit tangent vector of the
interval (`unitInterval.mfderiv_smoothTransition_one`). Tau Ceti's
`TauCeti.collaredSmoothTransitionUnit` is the analogous map for the reparametrization
`t ↦ Real.smoothTransition (2 * t - 1 / 2)`.
-/

public noncomputable section

open scoped Manifold ContDiff

namespace unitInterval

/-- The map `unitInterval.smoothTransition : ℝ → unitInterval` is surjective. -/
theorem smoothTransition_surjective : Function.Surjective smoothTransition := fun t ↦ by
  obtain ⟨u, -, hu⟩ := intermediate_value_Icc zero_le_one
    Real.smoothTransition.continuous.continuousOn
    (by simpa only [Real.smoothTransition.zero, Real.smoothTransition.one] using t.property)
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
  rw [hc, mfderiv_eq_fderiv]
  -- `NormedSpace.fromTangentSpace` is the identity by definition and has no apply lemma.
  change fderiv ℝ Real.smoothTransition u 1 = deriv Real.smoothTransition u
  exact fderiv_apply_one_eq_deriv

end unitInterval

end
