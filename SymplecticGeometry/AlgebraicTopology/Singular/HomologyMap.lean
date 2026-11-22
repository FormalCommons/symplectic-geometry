/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.AlgebraicTopology.SingularSet

/-!
# Homology isomorphisms in a commutative square

For a commutative square of continuous maps `g ∘ i = j ∘ f` in which `f` and `g` induce
isomorphisms on singular homology in degree `n`, the map `i` induces an isomorphism in degree `n`
exactly when `j` does: `ContinuousMap.isIso_homologyMap_iff_of_comp_eq`. Homology is read, as in
Tau Ceti's `ContinuousMap.HomotopyEquiv.isIso_homologyMap`, as
`SSet.homologyMap (TopCat.toSSet.map _)`. This is the homology counterpart of Tau Ceti's
`ContinuousMap.IsWeakHomotopyEquivalence.isNConnected_iff_of_comp_eq`.
-/

public section

open CategoryTheory Limits

namespace ContinuousMap

universe w v u

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  [CategoryWithHomology C] (R : C) (n : ℕ)
  {X Y X' Y' : Type w} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X']
  [TopologicalSpace Y'] {f : C(X, Y)} {g : C(X', Y')} {i : C(X, X')} {j : C(Y, Y')}

/-- In a commutative square `g ∘ i = j ∘ f` of continuous maps whose sides `f` and `g` induce
isomorphisms on singular homology in degree `n`, `j` induces an isomorphism there exactly when
`i` does. -/
theorem isIso_homologyMap_iff_of_comp_eq
    (hf : IsIso (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom f)) R n))
    (hg : IsIso (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom g)) R n))
    (h : g.comp i = j.comp f) :
    IsIso (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom j)) R n) ↔
      IsIso (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom i)) R n) := by
  have hsq := congrArg (fun φ ↦ SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom φ)) R n) h
  simp only [TopCat.ofHom_comp, Functor.map_comp, SSet.homologyMap_comp] at hsq
  rw [← isIso_comp_right_iff _ (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom g)) R n), hsq,
    isIso_comp_left_iff]

end ContinuousMap

end
