/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Injective

/-!
# Divisible groups are injective `ℤ`-modules

Mathlib's `AddCommGrpCat.injective_of_divisible` says that a divisible abelian group is an
injective object of `AddCommGrpCat`. This file records the same fact in `ModuleCat ℤ`, where
coefficient objects of singular cohomology over `ℤ` live, so that for instance `ℝ` and `ℚ` are
injective coefficients there.

## Main results

* `ModuleCat.injective_of_divisible`: a divisible abelian group is an injective object of
  `ModuleCat ℤ`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.1.
-/

public section

namespace ModuleCat

/-- A divisible abelian group `A` is an injective object of `ModuleCat ℤ`. -/
instance injective_of_divisible (A : Type*) [AddCommGroup A] [DivisibleBy A ℤ] :
    CategoryTheory.Injective (ModuleCat.of ℤ A) :=
  (AddCommGrpCat.injective_as_module_iff A).2 inferInstance

end ModuleCat

end
