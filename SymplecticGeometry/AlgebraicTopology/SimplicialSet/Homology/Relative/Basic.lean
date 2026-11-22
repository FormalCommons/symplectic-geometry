/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Relative.Basic

/-!
# Naturality in the coefficients of the quotient map to relative simplicial homology

This file is a part of Tau Ceti's file
`TauCeti/AlgebraicTopology/SimplicialSet/Homology/Relative/Basic.lean`, as of the commit
`5c90470dae` of Tau Ceti's main branch, which the pinned release does not have yet. It contains
only one lemma that this commit adds there, `SSetPair.homologyπ_coefficient_naturality`: the
quotient maps from ambient to relative simplicial homology are natural in the coefficient object.

It is stated under its Tau Ceti name and namespace, with Tau Ceti's statement, proof and docstring
unchanged, so that moving Tau Ceti past this commit deletes this file without renames. The imports
are replaced by the import of the pinned version of Tau Ceti's file. The variables are those of
the last section of that file.

The source is Eilenberg--Steenrod, *Foundations of Algebraic Topology*, Chapters I--III.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite Simplicial

universe w

namespace SSetPair

variable {D : Type*} [Category* D] [HasCoproducts.{w} D] [Preadditive D]
  [CategoryWithHomology D]

/-- The quotient maps from ambient to relative simplicial homology are natural in the coefficient
object. -/
@[reassoc]
lemma homologyπ_coefficient_naturality (P : SSetPair.{w}) {R R' : D} (φ : R ⟶ R') (n : ℕ) :
    HomologicalComplex.homologyMap (((SSet.chainComplexFunctor D).map φ).app P.right) n ≫
        P.homologyπ R' n =
      P.homologyπ R n ≫
        HomologicalComplex.homologyMap (((chainComplexFunctor D).map φ).app P) n := by
  have h : ((SSet.chainComplexFunctor D).map φ).app P.right ≫ P.chainComplexπ R' =
      P.chainComplexπ R ≫ ((chainComplexFunctor D).map φ).app P :=
    congrArg (fun η ↦ η.app P) ((chainComplexFunctorπ D).naturality φ)
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp, h]

end SSetPair

end
