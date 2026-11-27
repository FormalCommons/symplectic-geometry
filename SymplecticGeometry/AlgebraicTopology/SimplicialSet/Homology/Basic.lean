/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic

/-!
# Simplicial homology: change of coefficients

For a morphism of simplicial sets `f : X ⟶ Y`, this file shows that the map
`SSet.homologyMap f` on simplicial homology commutes with the maps induced by a morphism of
coefficient objects `g : S ⟶ S'`.

## Main results

* `SSet.homologyMap_coefficient_naturality`: the map on homology induced by a map of simplicial
  sets commutes with a change of coefficients.

This is the absolute form of `SSetPair.homologyMap_coefficient_naturality`
(`SymplecticGeometry/AlgebraicTopology/SimplicialSet/Homology/Relative/Pairing.lean`), and its
proof is the same: the naturality of the natural transformation
`(SSet.chainComplexFunctor C).map g`, passed to homology.
-/

public section

open CategoryTheory Limits

universe w v u

namespace SSet

/-- The map on simplicial homology induced by a morphism of simplicial sets `f : X ⟶ Y` commutes
with the maps induced by a coefficient morphism `g : S ⟶ S'`. -/
@[reassoc]
lemma homologyMap_coefficient_naturality {C : Type u} [Category.{v} C] [Preadditive C]
    [HasCoproducts.{w} C] [CategoryWithHomology C] {X Y : SSet.{w}} (f : X ⟶ Y)
    {S S' : C} (g : S ⟶ S') (n : ℕ) :
    HomologicalComplex.homologyMap (((chainComplexFunctor C).map g).app X) n ≫
        SSet.homologyMap f S' n =
      SSet.homologyMap f S n ≫
        HomologicalComplex.homologyMap (((chainComplexFunctor C).map g).app Y) n := by
  rw [SSet.homologyMap, SSet.homologyMap, ← HomologicalComplex.homologyMap_comp,
    ← HomologicalComplex.homologyMap_comp, SSet.chainComplexMap, SSet.chainComplexMap,
    ((chainComplexFunctor C).map g).naturality]

end SSet

end
