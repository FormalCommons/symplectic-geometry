/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.SimplicialSet.Shuffle
public import TauCeti.AlgebraicTopology.Singular.Shuffle

/-!
# The singular shuffle map on a simplex and a vertex

This file is a part of Tau Ceti's file `TauCeti/AlgebraicTopology/Singular/Shuffle.lean`, as of
the commit `ef2c0780f7` of Tau Ceti's main branch, which the pinned release does not have yet. It
contains only the declaration that this commit adds there,
`TopCat.ιChainComplex_tensorHom_ιChainComplex_shuffle_f_fst`: in bidegree `(p, 0)`, the singular
shuffle map followed by the projection `X × Y ⟶ X` sends the summand of a singular `p`-simplex `x`
of `X` and a singular vertex `y` of `Y` to the summand of `x`.

It is stated under its Tau Ceti name and namespace, with Tau Ceti's statement, proof and docstring
unchanged, so that moving Tau Ceti past this commit deletes this file without renames. The
imports are replaced by the import of the pinned version of Tau Ceti's file and of the copy of
`SSet.ιChainComplex_tensorHom_ιChainComplex_shuffle_f_fst`
(`SymplecticGeometry/AlgebraicTopology/SimplicialSet/Shuffle.lean`), which the proof uses.

## References

* S. Eilenberg and S. Mac Lane, *On the groups `H(Π, n)`, I*, Ann. of Math. 58 (1953).
* S. Eilenberg and J. A. Zilber, *On products of complexes*, Amer. J. Math. 75 (1953).
* C. Weibel, *An Introduction to Homological Algebra*, Section 8.5.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicTopology Simplicial
  HomologicalComplex
open scoped Simplicial
open Functor.LaxMonoidal Functor.Monoidal Functor.OplaxMonoidal
open SSet (chainComplexMap_f_comp)

universe w v u

namespace TopCat

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [MonoidalCategory C] [MonoidalPreadditive C] [HasCoproducts.{w} C]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)]

/-- In bidegree `(p, 0)`, the singular shuffle map followed by the projection `X × Y ⟶ X` sends the
summand of a singular `p`-simplex `x` of `X` and a singular vertex `y` of `Y` to the summand of
`x`. -/
@[reassoc]
lemma ιChainComplex_tensorHom_ιChainComplex_shuffle_f_fst {X Y : TopCat.{w}} (R S : C) {p : ℕ}
    (x : (toSSet.obj X) _⦋p⦌) (y : (toSSet.obj Y) _⦋0⦌) :
    ((toSSet.obj X).ιChainComplex x ⊗ₘ (toSSet.obj Y).ιChainComplex y) ≫
        ιTensorObj _ _ p 0 p (add_zero p) ≫ (shuffle X Y R S).f p ≫
          (SSet.chainComplexMap (toSSet.map (fst X Y)) (R ⊗ S)).f p =
      (toSSet.obj X).ιChainComplex x := by
  rw [shuffle_def, HomologicalComplex.comp_f, Category.assoc, chainComplexMap_f_comp, μ_fst,
    SSet.ιChainComplex_tensorHom_ιChainComplex_shuffle_f_fst]

end TopCat
