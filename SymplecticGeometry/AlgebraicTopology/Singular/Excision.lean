/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Triple
public import TauCeti.Topology.Category.TopPair

/-!
# The excision map of a product of two pairs

For subsets `A ⊆ X` and `B ⊆ Y`, write `A × Y` and `X × B` for their preimages under the
projections of `X × Y`. This file defines the triple `(X × Y, A × Y ∪ X × B, A × Y)`
(`TopPair.prodUnionTripleFst`) and the inclusion of pairs
`(X × B, A × B) ⟶ (A × Y ∪ X × B, A × Y)` into its inner pair (`TopPair.prodExcisionFst`), with
its map of ambient spaces (`TopPair.prodExcisionFst_fst`).

These declarations are from Tau Ceti's main branch
(`TauCeti/AlgebraicTopology/Singular/Excision.lean`, same names), as of the commit `c9d170eed5`,
not yet in the pinned release. They are stated here under their Tau Ceti names and namespace, so
that moving Tau Ceti past them deletes this file without renames. This file is a part of that
file, with only these three declarations; the excision theorem
`TopPair.isIso_singularHomologyMap_prodExcisionFst`, which the docstring of
`TopPair.prodExcisionFst` names, is not copied. The imports are those of Tau Ceti's file that
these declarations use.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, Theorem 2.20 and Proposition 2.21.
* S. Eilenberg and N. Steenrod, *Foundations of Algebraic Topology*, Chapter VII.
-/

public section

noncomputable section

open CategoryTheory Limits Topology

universe w v u

namespace TopPair

section Prod

variable {X Y : TopCat.{w}} (A : Set X) (B : Set Y)

open MonoidalCategory

/-- The triple `(X × Y, A × Y ∪ X × B, A × Y)`, with `A × Y` and `X × B` the preimages of `A` and
`B` under the projections. -/
abbrev prodUnionTripleFst : TauCeti.TopTriple.{w} :=
  TauCeti.TopTriple.ofSubset (X := X ⊗ Y)
    (A := CartesianMonoidalCategory.fst X Y ⁻¹' A ∪ CartesianMonoidalCategory.snd X Y ⁻¹' B)
    (B := CartesianMonoidalCategory.fst X Y ⁻¹' A) Set.subset_union_left

/-- The inclusion of pairs `(X × B, A × B) ⟶ (A × Y ∪ X × B, A × Y)` into the inner pair of
`TopPair.prodUnionTripleFst`, an excision when the interiors of `A × Y` and `X × B` cover their
union (`TopPair.isIso_singularHomologyMap_prodExcisionFst`). -/
def prodExcisionFst :
    ofSubset (CartesianMonoidalCategory.fst X (ofSubset B).snd ⁻¹' A) ⟶
      TauCeti.TopTriple.innerPair.obj (prodUnionTripleFst A B) :=
  ofHom (TopCat.ofHom ⟨fun p ↦ ⟨(p.1, p.2.val), Or.inr p.2.property⟩, by fun_prop⟩)
    (TopCat.ofHom ⟨fun p ↦ ⟨(CartesianMonoidalCategory.fst X _ p.val,
      (CartesianMonoidalCategory.snd X (ofSubset B).snd p.val).val), p.property⟩, by fun_prop⟩)
    (by ext; rfl)

/-- On ambient spaces, `TopPair.prodExcisionFst` is the inclusion `X × B ⟶ A × Y ∪ X × B`. -/
theorem prodExcisionFst_fst :
    Hom.fst (prodExcisionFst A B) =
      TopCat.ofHom ⟨fun p ↦ ⟨(p.1, p.2.val), Or.inr p.2.property⟩, by fun_prop⟩ :=
  (rfl)

end Prod

end TopPair
