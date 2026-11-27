/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Index
public import TauCeti.Geometry.Symplectic.Finrank
import SymplecticGeometry.Geometry.Symplectic.QuadraticForm

/-!
# Morse index lower bounds from complex negativity

For a real-valued function `f` on a real normed space with an almost complex structure `J`, if

`Hess f(v, v) + Hess f(Jv, Jv) < 0`

for every nonzero `v`, then the Morse index of `f` at `x` is at least the complex dimension
defined by `J`. This is the lower-bound counterpart of Tau Ceti's
`TauCeti.AlmostComplexStructure.morseIndex_le_complexFinrank_of_add_comp_posDef`, and follows from
`QuadraticForm.complexFinrank_le_sigNeg_of_add_comp_neg` applied to the Hessian quadratic form.
In infinite dimension both sides are `0`.

## Main declarations

* `TauCeti.AlmostComplexStructure.complexFinrank_le_morseIndex_of_add_comp_neg`: the Morse index
  is at least the complex dimension.

## References

* [D. Auroux, *Asymptotically holomorphic families of symplectic submanifolds*][Auroux1997]
* J. Milnor, *Morse Theory*, Princeton University Press, 1963, Section 7.
-/

public section

namespace TauCeti.AlmostComplexStructure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (J : TauCeti.AlmostComplexStructure E) (f : E → ℝ) (x : E)

/-- If `Hess f(v, v) + Hess f(Jv, Jv)` is negative for every nonzero `v`, then the Morse index of
`f` at `x` is at least the complex dimension defined by `J`. -/
theorem complexFinrank_le_morseIndex_of_add_comp_neg
    (h : ∀ v, v ≠ 0 →
      TauCeti.hessianQuadraticForm f x v + TauCeti.hessianQuadraticForm f x (J v) < 0) :
    J.complexFinrank ≤ TauCeti.morseIndex f x := by
  rw [TauCeti.morseIndex_def]
  exact (TauCeti.hessianQuadraticForm f x).complexFinrank_le_sigNeg_of_add_comp_neg J h

end TauCeti.AlmostComplexStructure
