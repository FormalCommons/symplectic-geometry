/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.One

/-!
# Naturality of the class of a closed `1`-simplex

Tau Ceti attaches to a `1`-simplex `s` of a simplicial set `X` with equal faces a class
`SSet.ιHomology₁ R X s h` in the first homology of `X` with coefficients in `R`. This file proves
that the class is natural in maps of simplicial sets (`SSet.ιHomology₁_homologyMap`), the
degree-one partner of Tau Ceti's `SSet.ιHomology₀_homologyMap`. The proof adapts that of Tau
Ceti's `SSetPair.relClass₁_homologyMap` from relative classes to absolute ones.

## Main results

* `SSet.ιHomology₁_homologyMap`: a map of simplicial sets carries the class of a closed
  `1`-simplex to the class of its image.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.A (`H₁` and
  loops).
-/

public section

open CategoryTheory Limits Simplicial

namespace SSet

universe w v u

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  [CategoryWithHomology C] (R : C)

/-- **Naturality of the class of a closed `1`-simplex**: a map of simplicial sets carries the class
of a `1`-simplex with equal faces to the class of its image. -/
@[reassoc (attr := simp)]
lemma ιHomology₁_homologyMap {X Y : SSet.{w}} (f : X ⟶ Y) (s : X _⦋1⦌) (h : X.δ 0 s = X.δ 1 s) :
    ιHomology₁ R X s h ≫ SSet.homologyMap f R 1 =
      ιHomology₁ R Y (f.app _ s) (by rw [← δ_naturality_apply, h, δ_naturality_apply]) := by
  rw [ιHomology₁_def, ιHomology₁_def, Category.assoc, HomologicalComplex.homologyπ_naturality,
    ← Category.assoc, HomologicalComplex.liftCycles_comp_cyclesMap]
  congr 2
  exact ι_chainComplexMap_f _ _ _ _ s

end SSet

end
