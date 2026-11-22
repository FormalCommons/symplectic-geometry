/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic

/-!
# The chain map of the identity of a simplicial set

The chain map `SSet.chainComplexMap (𝟙 X) R` induced by the identity of a simplicial set `X` is
the identity of its chain complex with coefficients in `R` (`SSet.chainComplexMap_id`).

This lemma is from Tau Ceti's main branch
(`TauCeti/AlgebraicTopology/SimplicialSet/Homology/Basic.lean`, same name), as of the commit
`e48a7f81a81426270765022681d165be592a3231`, not yet in the pinned release; it is stated here under
its Tau Ceti name, so that moving Tau Ceti past it deletes this file without renames.
-/

public section

open CategoryTheory Limits

universe w v u

namespace SSet

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]

/-- The identity of a simplicial set induces the identity chain map. -/
lemma chainComplexMap_id (X : SSet.{w}) (R : C) : chainComplexMap (𝟙 X) R = 𝟙 _ :=
  CategoryTheory.Functor.map_id _ _

end SSet

end
