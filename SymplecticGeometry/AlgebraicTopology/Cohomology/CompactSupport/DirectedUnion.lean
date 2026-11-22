/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.DirectedUnion

/-!
# Extension of compactly supported classes through nested open sets

For opens `V ≤ W` of a Hausdorff space `X`, extending a class of `Hⁿ_c(V)` by zero to `X` is
extending it to `W` and then to `X` (`TopCat.compactSupportCohomologyExtend_toTopCat_map_comp`):
the naturality of the cocone `TopCat.compactSupportCohomologyOpensCocone`, stated for the
extensions themselves.

This lemma is from Tau Ceti's main branch
(`TauCeti/AlgebraicTopology/Cohomology/CompactSupport/DirectedUnion.lean`, same name), not yet in
the pinned release; it is stated here under its Tau Ceti name, so that moving Tau Ceti past it
deletes this file without renames.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace Topology Opens

universe v u

namespace TopCat

variable {C : Type u} [Category.{v} C] [HasCoproducts.{v} C] [Abelian C] {R : C}
  {k : Type v} [Ring k] [Linear k C] {M : C} {X : TopCat.{v}} [T2Space X]

/-- Extending a class from `V` to `X` is extending it to `W` and then to `X`, for opens `V ≤ W`. -/
@[reassoc, elementwise]
lemma compactSupportCohomologyExtend_toTopCat_map_comp {V W : Opens X} (h : V ⟶ W) (n : ℕ) :
    compactSupportCohomologyExtend (R := R) (k := k) (M := M) (isOpenEmbedding_toTopCat_map h) n ≫
        compactSupportCohomologyExtend W.isOpenEmbedding n =
      compactSupportCohomologyExtend V.isOpenEmbedding n :=
  (compactSupportCohomologyExtend_comp (isOpenEmbedding_toTopCat_map h) W.isOpenEmbedding n
    (W.isOpenEmbedding.comp (isOpenEmbedding_toTopCat_map h))).symm.trans
    (compactSupportCohomologyExtend_congr (toTopCat_map_comp_inclusion' h) _ _ n)

end TopCat

end
