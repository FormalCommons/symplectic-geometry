/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Complex.Circle

/-!
# The action of the unit circle through `unitary ℂ`

A fact about Tau Ceti's isomorphism `TauCeti.circleEquivUnitary : Circle ≃ₜ* unitary ℂ`: on any
type with an action of `ℂ`, the unitary `circleEquivUnitary z` acts as the complex number `z`.

## Main results

* `TauCeti.circleEquivUnitary_smul`: `circleEquivUnitary z • x = (z : ℂ) • x`.
-/

public section

namespace TauCeti

/-- The unitary `circleEquivUnitary z` acts on any `ℂ`-set as the complex number `z`. -/
@[simp]
theorem circleEquivUnitary_smul {M : Type*} [MulAction ℂ M] (z : Circle) (x : M) :
    circleEquivUnitary z • x = (z : ℂ) • x := by
  rw [Submonoid.smul_def, coe_circleEquivUnitary]

end TauCeti

end
