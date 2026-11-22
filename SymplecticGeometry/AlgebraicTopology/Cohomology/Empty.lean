/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Point

/-!
# The singular cohomology of an empty space

The singular cohomology of an empty space has a single element in every degree, for any chain
coefficients `R` and cochain values `M`: `TopCat.subsingleton_singularCohomology_of_isEmpty` is
this as an instance, read off from Tau Ceti's `TauCeti.isZero_singularCohomology_of_isEmpty`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1.
-/

public section

open CategoryTheory Limits

universe w v u

namespace TopCat

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]
  {R : C} {k : Type*} [Ring k] [Linear k C] {M : C}

/-- The singular cohomology `Hⁿ(X; R, M)` of an empty space `X` is a subsingleton, in every degree
and for any coefficients. -/
instance subsingleton_singularCohomology_of_isEmpty (X : TopCat.{w}) [IsEmpty X] (n : ℕ) :
    Subsingleton (X.singularCohomology R k M n) :=
  ModuleCat.subsingleton_of_isZero (TauCeti.isZero_singularCohomology_of_isEmpty R k M X n)

end TopCat

end
