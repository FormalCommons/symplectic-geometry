/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Projectivization
public import TauCeti.AlgebraicTopology.Cohomology.Point
import TauCeti.LinearAlgebra.Projectivization.Basic

/-!
# The singular cohomology of the projectivization of a line

For a vector space `E` of dimension one over a division ring `K`, the projective space `ℙ K E`
has exactly one point, so it is contractible and its singular cohomology, with any chain
coefficients `R` and cochain values `M`, vanishes in every positive degree
(`Projectivization.isZero_singularCohomology_of_finrank_eq_one`). This is read off from Tau
Ceti's `TauCeti.isZero_singularCohomology_of_contractibleSpace`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1.
-/

public section

universe w v u

open CategoryTheory Limits Module
open scoped LinearAlgebra.Projectivization

namespace Projectivization

/-- For a one-dimensional vector space `E` over a division ring `K`, the projective space `ℙ K E`
is a point, so its singular cohomology, with any coefficients, vanishes in every positive
degree. -/
theorem isZero_singularCohomology_of_finrank_eq_one {C : Type u} [Category.{v} C]
    [HasCoproducts.{w} C] [Abelian C] (R : C) (k : Type*) [Ring k] [Linear k C] (M : C)
    {K : Type*} {E : Type w} [DivisionRing K] [AddCommGroup E] [TopologicalSpace E] [Module K E]
    (hE : finrank K E = 1) {n : ℕ} (hn : n ≠ 0) :
    IsZero ((TopCat.of (ℙ K E)).singularCohomology R k M n) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hE
  have : Module.Finite K E := Module.finite_of_finrank_eq_succ hE
  have : Subsingleton (ℙ K E) :=
    subsingleton_of_rank_le_one (by rw [← Module.finrank_eq_rank, hE]; simp)
  exact TauCeti.isZero_singularCohomology_of_contractibleSpace R k M (TopCat.of (ℙ K E)) hn

end Projectivization

end
