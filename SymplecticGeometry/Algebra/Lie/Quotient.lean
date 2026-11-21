/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Lie.Quotient

/-!
# Quotients of Lie modules and Lie algebras

Supplements to Mathlib's `Mathlib/Algebra/Lie/Quotient.lean`.

* `LieHom.coe_quotKerEquivRange_mk`: the first isomorphism theorem for Lie algebras,
  `LieHom.quotKerEquivRange`, sends the class of `x` modulo the kernel of `f` to `f x`, seen as
  an element of the range of `f`. Mathlib's `@[simps]` lemma `LieHom.quotKerEquivRange_toFun`
  states this value through the kernel of the underlying linear map, so `simp` cannot use it on
  a class `LieSubmodule.Quotient.mk x`.
-/

public section

namespace LieHom

variable {R L L' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L']
  [LieAlgebra R L']

/-- The first isomorphism theorem `LieHom.quotKerEquivRange` sends the class of `x` modulo the
kernel of `f` to `f x`. -/
@[simp]
theorem coe_quotKerEquivRange_mk (f : L →ₗ⁅R⁆ L') (x : L) :
    (f.quotKerEquivRange (LieSubmodule.Quotient.mk x) : L') = f x :=
  (rfl)

end LieHom

end
