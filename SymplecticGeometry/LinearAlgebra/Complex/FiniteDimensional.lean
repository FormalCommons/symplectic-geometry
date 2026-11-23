/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Finite-dimensional complex vector spaces are finite-dimensional over `ℝ`

A finite-dimensional complex vector space, with any real structure compatible with the complex
one, is finite-dimensional over `ℝ`, by `Module.Finite.trans`. This file makes that fact the scoped
instance `Module.ComplexToReal.finiteDimensional`, available after
`open scoped Module.ComplexToReal`.

Mathlib's instance `FiniteDimensional.complexToReal` is stated for the real structure
`Module.complexToReal` only. A space that carries its real structure as an argument of its own,
such as the model fibre `[NormedSpace ℝ F]` of a complex vector bundle, is not reached by it.

The instance is scoped rather than global so that the search for `FiniteDimensional ℝ` does not
try a complex structure everywhere. Since `FiniteDimensional` is a proposition, it creates no
diamond.

## Main definitions

* `Module.ComplexToReal.finiteDimensional`: a finite-dimensional complex vector space is
  finite-dimensional over `ℝ`.
-/

public section

namespace Module.ComplexToReal

/-- A finite-dimensional complex vector space, with a real structure compatible with the complex
one, is finite-dimensional over `ℝ`. -/
scoped instance finiteDimensional {F : Type*} [AddCommGroup F] [Module ℝ F] [Module ℂ F]
    [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F] : FiniteDimensional ℝ F :=
  Module.Finite.trans ℂ F

end Module.ComplexToReal

end
