/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.SimplicialSet.Homology.RestrictScalars
public import TauCeti.AlgebraicTopology.Singular.Coefficients.RestrictScalars

/-!
# Tau Ceti's singular change of coefficient ring as a simplicial one

For a homomorphism `f : R →+* k` of commutative rings and a map `c : T ⟶ f^* k` of
`R`-modules, Tau Ceti's comparison of singular chains `TopCat.restrictScalarsChainMap f c` of a
space `X` is the change of coefficients `SSet.restrictScalarsChainMap f c` on the singular
simplicial set of `X` (`TopCat.restrictScalarsChainMap_eq_sSet_restrictScalarsChainMap`). This
lets results about the simplicial change of coefficients apply to Tau Ceti's comparison.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.A.
-/

public section

open CategoryTheory
open scoped MonoidalCategory

namespace TopCat

universe w

variable (X : TopCat.{w}) {R k : Type w} [CommRing R] [CommRing k] (f : R →+* k)
  {T : ModuleCat.{w} R} (c : T ⟶ (ModuleCat.restrictScalars f).obj (𝟙_ (ModuleCat.{w} k)))

/-- Tau Ceti's comparison of singular chains `TopCat.restrictScalarsChainMap f c` is the change of
coefficients `SSet.restrictScalarsChainMap f c` on the singular simplicial set of `X`. -/
theorem restrictScalarsChainMap_eq_sSet_restrictScalarsChainMap :
    X.restrictScalarsChainMap f c = SSet.restrictScalarsChainMap f c (toSSet.obj X) := by
  ext n : 1
  refine SSet.chainComplex_hom_ext fun σ ↦ ?_
  rw [SSet.ιChainComplex_restrictScalarsChainMap_f, ιChainComplex_restrictScalarsChainMap_f]

end TopCat

end
