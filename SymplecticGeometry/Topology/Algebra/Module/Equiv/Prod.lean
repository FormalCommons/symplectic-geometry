/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv.Prod

/-!
# Continuous linear equivalences on products

A lemma about `ContinuousLinearEquiv.prodComm` that Mathlib does not state at the pinned version,
kept in its namespace so that it can move upstream unchanged.

## Main results

* `ContinuousLinearEquiv.coe_prodComm`: the function underlying `ContinuousLinearEquiv.prodComm`
  is `Prod.swap`, as Mathlib states for `Homeomorph.coe_prodComm` and `Equiv.coe_prodComm`.
-/

public section

namespace ContinuousLinearEquiv

variable (R : Type*) [Semiring R]
  (M₁ : Type*) [TopologicalSpace M₁] [AddCommMonoid M₁] [Module R M₁]
  (M₂ : Type*) [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M₂]

/-- The function underlying the continuous linear equivalence `prodComm R M₁ M₂` is the swap
`Prod.swap : M₁ × M₂ → M₂ × M₁`. -/
@[simp]
theorem coe_prodComm : ⇑(prodComm R M₁ M₂) = Prod.swap :=
  funext (prodComm_apply R M₁ M₂)

end ContinuousLinearEquiv

end
