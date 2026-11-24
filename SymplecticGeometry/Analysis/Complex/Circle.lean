/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Mul
public import TauCeti.Analysis.Complex.Circle.Basic

/-!
# Actions of the unit circle

Two ways in which the unit circle acts as the complex numbers it contains.

* `TauCeti.circleEquivUnitary_smul`: on any type with an action of `ℂ`, the unitary
  `circleEquivUnitary z` of Tau Ceti's isomorphism `TauCeti.circleEquivUnitary : Circle ≃ₜ*
  unitary ℂ` acts as the complex number `z`.
* `Circle.lsmul`: the action of the unit circle on `ℂ` by multiplication, as a monoid
  homomorphism into the real continuous linear endomorphisms of `ℂ`
  (`Circle.lsmul_apply`: `Circle.lsmul z w = z * w`).
-/

public section

namespace TauCeti

/-- The unitary `circleEquivUnitary z` acts on any `ℂ`-set as the complex number `z`. -/
@[simp]
theorem circleEquivUnitary_smul {M : Type*} [MulAction ℂ M] (z : Circle) (x : M) :
    circleEquivUnitary z • x = (z : ℂ) • x := by
  rw [Submonoid.smul_def, coe_circleEquivUnitary]

end TauCeti

namespace Circle

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
