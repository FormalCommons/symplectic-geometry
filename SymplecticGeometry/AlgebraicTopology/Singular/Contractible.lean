/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Contractible

/-!
# The connecting morphism of a pair with contractible ambient space

If the ambient space `X` of a pair `(X, A)` is contractible, its homology vanishes in positive
degrees, so by exactness of the long exact sequence of the pair the connecting morphism
`Hₘ₊₁(X, A) ⟶ Hₘ(A)` is a monomorphism
(`TopPair.mono_singularHomologyδ_of_contractibleSpace`). This is the counterpart of Tau Ceti's
`TopPair.singularHomologyδ_eq_zero_of_contractibleSpace`, for a contractible subspace.

The argument is the one that Tau Ceti's `TauCeti.mono_cubeBoundaryPair_singularHomologyδ` makes
for the pair of a cube and its boundary.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.1 (the long exact sequence of a pair, and the homology of contractible spaces).
-/

public section

open CategoryTheory Limits AlgebraicTopology

universe w v u

namespace TopPair

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)

/-- If the ambient space of a pair is contractible, its connecting morphism
`Hₘ₊₁(X, A) ⟶ Hₘ(A)` is a monomorphism. -/
theorem mono_singularHomologyδ_of_contractibleSpace (P : TopPair.{w}) [ContractibleSpace P.fst]
    (m : ℕ) : Mono (P.singularHomologyδ R (m + 1) m) :=
  (P.singularHomology_exact_relative R (m + 1) m).mono_g
    ((TauCeti.isZero_singularHomologyFunctor_of_contractibleSpace R P.fst
      m.succ_ne_zero).eq_of_src _ _)

end TopPair

end
