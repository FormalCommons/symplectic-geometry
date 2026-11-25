/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.Basic
public import TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Subcomplex

/-!
# Small cochains on an affinely stable subcomplex

Let `S` be an affinely stable subcomplex of the singular simplicial set of a space `X`, and let
`U` be an open cover of `X`. Restricting cochains on `S` to the simplices of `S` subordinate to
`U` is a quasi-isomorphism
(`TauCeti.quasiIso_cochainComplexMap_homOfLE_inf_smallSingularSubcomplex`), for any coefficient
object. This is the cochain counterpart of Tau Ceti's
`TauCeti.quasiIso_chainComplexMap_homOfLE_inf_smallSingularSubcomplex`: it is `Hom(-, Y)` applied
to the chain homotopy equivalence `TauCeti.subcomplexSmallChainHomotopyEquiv`, as Tau Ceti's
`TauCeti.quasiIso_cochainComplexMap_smallSingularSubcomplex_ι` does for `S` the whole singular
simplicial set.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.1 (the
  Mayer–Vietoris sequences in cohomology).
-/

public section

open CategoryTheory Limits SSet.Subcomplex

universe u v w

namespace TauCeti

variable {C : Type v} [Category.{w} C] [HasCoproducts.{u} C] [Abelian C] (R : C)
  (k : Type*) [Ring k] [Linear k C] (Y : C)
  {X : TopCat.{u}} (S : (TopCat.toSSet.obj X).Subcomplex) [S.IsAffineStable]
  {ι : Type*} (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = Set.univ)

include hU hcov in
/-- For an affinely stable subcomplex `S` of the singular simplicial set of `X` and an open cover
`U` of `X`, restricting cochains on `S` with values in `Y` to the simplices of `S` subordinate to
`U` is a quasi-isomorphism. -/
theorem quasiIso_cochainComplexMap_homOfLE_inf_smallSingularSubcomplex :
    QuasiIso (SSet.cochainComplexMap (R := R) (k := k) (M := Y)
      (homOfLE (inf_le_left : S ⊓ X.smallSingularSubcomplex U ≤ S))) := by
  have :=
    ((subcomplexSmallChainHomotopyEquiv R S U hU hcov).linearYonedaFunctorMap k Y).quasiIso_hom
  rwa [HomotopyEquiv.linearYonedaFunctorMap_hom, subcomplexSmallChainHomotopyEquiv_hom] at this

end TauCeti

end
