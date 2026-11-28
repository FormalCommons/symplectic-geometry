/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The unit circle: nontriviality, actions and smoothness of the exponential

The unit circle is a nontrivial group (`Circle.instNontrivial`, from `Circle.exp_pi_ne_one`).
The exponential `t ↦ exp (t i)`, read in `ℂ`, is smooth (`Circle.contDiff_coe_exp`).
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

/-- The exponential `t ↦ exp (t i)` of the unit circle, read in `ℂ`, is smooth. -/
theorem contDiff_coe_exp {n : WithTop ℕ∞} : ContDiff ℝ n fun t : ℝ ↦ (exp t : ℂ) := by
  simp_rw [coe_exp]
  exact (Complex.ofRealCLM.contDiff.mul contDiff_const).cexp

theorem lsmul_def (z : Circle) : lsmul z = ContinuousLinearMap.lsmul ℝ ℂ (z : ℂ) :=
  (rfl)

@[simp]
theorem lsmul_apply (z : Circle) (w : ℂ) : lsmul z w = z * w :=
  (rfl)

end Circle

end
