/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.Complex.Circle

/-!
# The unit circle: nontriviality and actions

The unit circle is a nontrivial group (`Circle.instNontrivial`, from `Circle.exp_pi_ne_one`).
`Circle.lsmul` is its action on `ℂ` by multiplication, as a monoid homomorphism into the real
continuous linear endomorphisms of `ℂ` (`Circle.lsmul_apply`: `Circle.lsmul z w = z * w`).
-/

public section

namespace Circle

/-- The unit circle has an element other than `1`, namely `Circle.exp π`. -/
instance instNontrivial : Nontrivial Circle :=
  ⟨⟨_, _, exp_pi_ne_one⟩⟩

/-- The action of the unit circle on `ℂ` by multiplication: `z` acts as the real linear map
`w ↦ z * w`. -/
noncomputable def lsmul : Circle →* (ℂ →L[ℝ] ℂ) where
  toFun z := ContinuousLinearMap.lsmul ℝ ℂ (z : ℂ)
  map_one' := by ext; simp
  map_mul' z w := by ext; simp [mul_assoc]

theorem lsmul_def (z : Circle) : lsmul z = ContinuousLinearMap.lsmul ℝ ℂ (z : ℂ) :=
  (rfl)

@[simp]
theorem lsmul_apply (z : Circle) (w : ℂ) : lsmul z w = z * w :=
  (rfl)

end Circle

end
