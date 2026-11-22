/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Chains

/-!
# Small chains of a subset of a member of the cover

Let `U` be a family of subsets of a space `X` and `S' ⊆ U i`. The singular simplices of `S'` map
into the subcomplex of simplices of `X` subordinate to `U` (`TopCat.toSmallSingularSubcomplex`).
On chains, following this map by the inclusion of the subordinate chains into all chains of `X`
is the map induced by the inclusion of `S'` into `X`
(`TopCat.chainComplexMap_f_toSmallSingularSubcomplex_ι`).

This lemma is from Tau Ceti's main branch
(`TauCeti/AlgebraicTopology/Singular/Subdivision/Small/Chains.lean`, same name), as of the commit
`e48a7f81a81426270765022681d165be592a3231`, not yet in the pinned release; it is stated here
under its Tau Ceti name, so that moving Tau Ceti past it deletes this file without renames. (On
that branch it replaces `TopCat.chainComplexMap_f_toSmallSingularSubcomplex_comp`, which the
pinned release has, and which is its composite with a cochain.)
-/

public section

open CategoryTheory Limits

universe w v u

namespace TopCat

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  {R : C} {X : TopCat.{w}}

/-- Inclusion of subordinate chains after restricting to a subset is its singular inclusion. -/
lemma chainComplexMap_f_toSmallSingularSubcomplex_ι {ι : Type*} (U : ι → Set X)
    {S' : Set X} {i : ι} (hS' : S' ⊆ U i) (n : ℕ) :
    (SSet.chainComplexMap (toSmallSingularSubcomplex U hS') R).f n ≫
        (SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R).f n =
      (SSet.chainComplexMap (toSSet.map (ofHom (ContinuousMap.subtypeVal S'))) R).f n := by
  rw [← HomologicalComplex.comp_f, ← Functor.map_comp, toSmallSingularSubcomplex_ι]

end TopCat

end
