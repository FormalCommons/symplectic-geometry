/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.AlmostComplex

/-!
# General facts about symplectic forms

This file collects basic facts about Tau Ceti's `TauCeti.SymplecticForm` that Tau Ceti does not
state. They live in the namespace `TauCeti.SymplecticForm`, so that they can move to Tau Ceti
unchanged.

* `TauCeti.SymplecticForm.toBilinForm_apply`: evaluating the underlying bilinear form
  `ω.toBilinForm` at `v, w` is `ω v w`, the value of `ω` through its coercion to a function.

The coercion of `ω` to a function is not a `@[coe]` function, so `ω v w` and
`ω.toBilinForm v w` are only equal up to unfolding, and lemmas stated with one do not rewrite
goals stated with the other. `toBilinForm_apply` closes that gap for `rw`. It is not a `simp`
lemma: its right side reduces to its left side, so `simp` would loop on it.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017]
-/

public section

namespace TauCeti.SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The underlying bilinear form of a symplectic form `ω`, evaluated at `v` and `w`, is `ω v w`,
the value of `ω` through its coercion to a function. -/
theorem toBilinForm_apply (ω : SymplecticForm V) (v w : V) :
    ω.toBilinForm v w = ω v w := (rfl)

end TauCeti.SymplecticForm

end
