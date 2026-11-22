/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.Shuffle
public import TauCeti.AlgebraicTopology.Singular.CrossProduct

/-!
# The shuffle product with a vertex, on chains

This file is a part of Tau Ceti's file `TauCeti/AlgebraicTopology/Singular/CrossProduct.lean`, as
of the commit `ef2c0780f7` of Tau Ceti's main branch, which the pinned release does not have yet.
It contains only one lemma that this commit adds there,
`TopCat.rightUnitor_inv_whiskerLeft_shuffle_f_fst`: on chains in degree `p`, the shuffle product
with a vertex `y`, weighted by `t : 𝟙_ C ⟶ S`, followed by the projection `X × Y ⟶ X`, is the
coefficient map `r ↦ r ⊗ t`. Tau Ceti uses it to compute the cross product with the class of a
point.

It is stated under its Tau Ceti name and namespace, with Tau Ceti's statement, proof and docstring,
so that moving Tau Ceti past this commit deletes this file without renames. The changes are:

* the lemma is public, where Tau Ceti's is `private`, since
  `SymplecticGeometry/AlgebraicTopology/Singular/Kunneth/RelativePoint.lean` uses it;
* it is tagged `@[reassoc]`, which gives the form that file uses;
* the imports are replaced by the import of the pinned version of Tau Ceti's file and of the copy
  of `TopCat.ιChainComplex_tensorHom_ιChainComplex_shuffle_f_fst`
  (`SymplecticGeometry/AlgebraicTopology/Singular/Shuffle.lean`), which the proof uses.

The variables are those of Tau Ceti's file.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.B, the cross product in homology.
* S. Eilenberg and J. A. Zilber, *On products of complexes*, Amer. J. Math. 75 (1953).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology HomologicalComplex

universe w v u

namespace TopCat

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable {C : Type u} [Category.{v} C] [Preadditive C] [CategoryWithHomology C]
  [MonoidalCategory C] [MonoidalPreadditive C] [HasCoproducts.{w} C]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)]

omit [CategoryWithHomology C] in
/-- On chains, the shuffle product with a vertex `y`, weighted by `t : 𝟙_ C ⟶ S`, followed by the
projection to the first factor is the coefficient map `r ↦ r ⊗ t`. -/
@[reassoc]
lemma rightUnitor_inv_whiskerLeft_shuffle_f_fst (X Y : TopCat.{w}) (R S : C) (p : ℕ)
    (y : Y) (t : 𝟙_ C ⟶ S) :
    (ρ_ (((toSSet.obj X).chainComplex R).X p)).inv ≫
        (((toSSet.obj X).chainComplex R).X p ◁
          (t ≫ (toSSet.obj Y).ιChainComplex (toSSetObj₀Equiv.symm y))) ≫
        ιTensorObj ((toSSet.obj X).chainComplex R) ((toSSet.obj Y).chainComplex S) p 0 p
          (add_zero p) ≫ (shuffle X Y R S).f p ≫
          (SSet.chainComplexMap (toSSet.map (CartesianMonoidalCategory.fst X Y)) (R ⊗ S)).f p =
      (((SSet.chainComplexFunctor C).map ((ρ_ R).inv ≫ R ◁ t)).app (toSSet.obj X)).f p := by
  ext x
  rw [← rightUnitor_inv_comp_tensorHom_assoc, ← whiskerLeft_comp_tensorHom_assoc,
    ιChainComplex_tensorHom_ιChainComplex_shuffle_f_fst,
    SSet.ιChainComplex_chainComplexFunctor_map_app_f, Category.assoc]

end TopCat

end
