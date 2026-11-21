/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Geometry.Manifold.Instances.Icc
import TauCeti.Geometry.Manifold.Instances.Icc

/-!
# The smooth transition function as a smooth map to the unit interval

Mathlib's `Real.smoothTransition` takes its values in `[0, 1]`. This file defines it as a map
`Real.smoothTransitionUnit : ℝ → unitInterval`, which is `0` on `(-∞, 0]` and `1` on `[1, ∞)`,
and shows that it is smooth for the manifold-with-boundary structure of the unit interval, by
Tau Ceti's `ContMDiff.smoothTransition`. Its derivative sends the unit vector `1` of `ℝ` to
`deriv Real.smoothTransition u` times the unit tangent vector of the interval
(`Real.mfderiv_smoothTransitionUnit_one`). Tau Ceti's `TauCeti.collaredSmoothTransitionUnit` is
the analogous map for the reparametrization `t ↦ Real.smoothTransition (2 * t - 1 / 2)`.
-/

public noncomputable section

open scoped Manifold ContDiff

namespace Real

/-- The smooth transition function `Real.smoothTransition`, as a map `s : ℝ → unitInterval`. -/
def smoothTransitionUnit (u : ℝ) : unitInterval :=
  ⟨smoothTransition u, smoothTransition.nonneg u, smoothTransition.le_one u⟩

/-- The point `s u` of the unit interval is `Real.smoothTransition u`. -/
@[simp]
theorem coe_smoothTransitionUnit (u : ℝ) :
    (smoothTransitionUnit u : ℝ) = smoothTransition u :=
  (rfl)

/-- For `u ≤ 0`, `s u = 0`. -/
theorem smoothTransitionUnit_of_nonpos {u : ℝ} (hu : u ≤ 0) : smoothTransitionUnit u = 0 :=
  Subtype.ext (smoothTransition.zero_of_nonpos hu)

/-- For `u ≥ 1`, `s u = 1`. -/
theorem smoothTransitionUnit_of_one_le {u : ℝ} (hu : 1 ≤ u) : smoothTransitionUnit u = 1 :=
  Subtype.ext (smoothTransition.one_of_one_le hu)

/-- The map `s : ℝ → unitInterval` is `C^n` for every `n ≤ ∞`. -/
theorem contMDiff_smoothTransitionUnit {n : ℕ∞ω} (hn : n ≤ ∞) :
    ContMDiff 𝓘(ℝ) (𝓡∂ 1) n smoothTransitionUnit :=
  contMDiff_id.smoothTransition hn

/-- The derivative of `s : ℝ → unitInterval` at `u` sends `1` to `s'(u)` times the unit tangent
vector `1` of the interval, where `s' = deriv Real.smoothTransition`. -/
theorem mfderiv_smoothTransitionUnit_one (u : ℝ) :
    mfderiv 𝓘(ℝ) (𝓡∂ 1) smoothTransitionUnit u 1 = deriv smoothTransition u • 1 := by
  have hσu : MDifferentiableAt 𝓘(ℝ) (𝓡∂ 1) smoothTransitionUnit u :=
    (contMDiff_smoothTransitionUnit le_rfl).mdifferentiableAt (by simp)
  have hval : MDifferentiableAt (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : unitInterval → ℝ)
      (smoothTransitionUnit u) :=
    (contMDiff_subtypeVal_Icc (n := 1)).mdifferentiableAt one_ne_zero
  -- The inclusion of the interval has injective derivative, and sends both sides to `s'(u)`.
  refine (TauCeti.isInvertible_mfderiv_subtypeVal_Icc (smoothTransitionUnit u)).injective ?_
  rw [map_smul, mfderiv_subtypeVal_Icc_one, ← mfderiv_comp_apply u hval hσu]
  have hc : Subtype.val ∘ smoothTransitionUnit = smoothTransition :=
    funext coe_smoothTransitionUnit
  rw [hc, mfderiv_eq_fderiv]
  -- `NormedSpace.fromTangentSpace` is the identity by definition and has no apply lemma.
  change fderiv ℝ smoothTransition u 1 = deriv smoothTransition u • (1 : ℝ)
  rw [fderiv_apply_one_eq_deriv, smul_eq_mul, mul_one]

end Real

end
