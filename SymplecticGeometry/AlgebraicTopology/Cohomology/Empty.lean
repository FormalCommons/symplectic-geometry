/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Point
public import TauCeti.AlgebraicTopology.Singular.BettiNumber
public import TauCeti.AlgebraicTopology.Singular.SurfaceGenus

import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient.Field

/-!
# The singular cohomology of an empty space

The singular cohomology of an empty space has a single element in every degree, for any chain
coefficients `R` and cochain values `M`: `TopCat.subsingleton_singularCohomology_of_isEmpty` is
this as an instance, read off from Tau Ceti's `TauCeti.isZero_singularCohomology_of_isEmpty`.
Over a field, singular homology has the dimension of singular cohomology (Tau Ceti's
`TopCat.finrank_singularCohomology`), so every Betti number of an empty space is `0`
(`TauCeti.bettiNumber_eq_zero_of_isEmpty`), and so is its genus
(`TauCeti.surfaceGenus_eq_zero_of_isEmpty`).

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1.
-/

public section

open CategoryTheory Limits Module

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

namespace TauCeti

/-- **The Betti numbers of an empty space vanish**, over any field and in every degree. -/
@[simp]
theorem bettiNumber_eq_zero_of_isEmpty (k : Type u) [Field k] (X : Type u) [TopologicalSpace X]
    [IsEmpty X] (j : ℕ) : bettiNumber k X j = 0 := by
  have : IsEmpty (TopCat.of X) := ‹IsEmpty X›
  rw [bettiNumber_def, ← TopCat.finrank_singularCohomology, finrank_zero_of_subsingleton]

/-- **An empty space has genus `0`**: its first rational homology vanishes. -/
@[simp]
theorem surfaceGenus_eq_zero_of_isEmpty (X : Type) [TopologicalSpace X] [IsEmpty X] :
    surfaceGenus X = 0 := by
  rw [surfaceGenus_def, ← bettiNumber_def, bettiNumber_eq_zero_of_isEmpty, Nat.zero_div]

end TauCeti

end
