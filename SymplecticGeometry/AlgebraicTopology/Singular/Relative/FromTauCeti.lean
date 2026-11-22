/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Relative

/-!
# Relative singular chains: maps of pairs that are the identity on the ambient space

A map of pairs `(X, A) ⟶ (X, B)` whose map of ambient spaces is the identity of `X` carries the
quotient map to the relative singular chains of `(X, A)` to that of `(X, B)`
(`TopPair.singularChainComplexπ_comp_singularChainComplexMap_of_fst_eq_id`).

This lemma is from Tau Ceti's main branch (`TauCeti/AlgebraicTopology/Singular/Relative.lean`,
same name), as of the commit `c9d170eed5`, not yet in the pinned release. It is stated here under
its Tau Ceti name and namespace, so that moving Tau Ceti past it deletes this file without renames.
This file is a part of that file, with only this lemma, and the variables it uses. Tau Ceti's file
follows the quotient-chain presentation of relative chains in Eilenberg--Steenrod, *Foundations of
Algebraic Topology*, Chapters I--III.
-/

@[expose] public section

noncomputable section

open Simplicial CategoryTheory Limits TopologicalSpace

universe w v u

namespace TopPair

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]

variable {C} (R : C)

/-- A map of pairs `(X, A) ⟶ (X, B)` given by the identity of `X` carries the quotient map to the
relative singular chains of `(X, A)` to the quotient map to those of `(X, B)`. -/
@[reassoc]
lemma singularChainComplexπ_comp_singularChainComplexMap_of_fst_eq_id {X A B : TopCat.{w}}
    {i : A ⟶ X} {j : B ⟶ X} {hi : Topology.IsEmbedding i} {hj : Topology.IsEmbedding j}
    (f : TopPair.of i hi ⟶ TopPair.of j hj) (hf : Hom.fst f = 𝟙 X) :
    (TopPair.of i hi).singularChainComplexπ R ≫ singularChainComplexMap f R =
      (TopPair.of j hj).singularChainComplexπ R := by
  rw [← singularChainComplexπ_pair_naturality, hf]
  exact (congrArg (· ≫ _) ((TopCat.toSSet ⋙ (SSet.chainComplexFunctor C).obj R).map_id X)).trans
    (Category.id_comp _)

end TopPair
