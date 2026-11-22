/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Relative

/-!
# The relative small-chain theorem for the pair of a subset

For a subset `S` of a space `X` and an open cover `F` of `X`, restricting the singular pair of
`(X, S)` to the simplices of `X` subordinate to `F` does not change relative homology
(`TopPair.isIso_homologyMap_restrictι_smallSingularSubcomplex_ofSubset`). This is Tau Ceti's
`TopPair.isIso_homologyMap_restrictι_smallSingularSubcomplex` for the pair `TopPair.ofSubset S`,
with the small subcomplex of the pair written as that of `X`.

This lemma is from Tau Ceti's main branch
(`TauCeti/AlgebraicTopology/Singular/Subdivision/Small/Relative.lean`, same name), as of the
commit `e48a7f81a81426270765022681d165be592a3231`, not yet in the pinned release; it is stated
here under its Tau Ceti name, so that moving Tau Ceti past it deletes this file without renames.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Proposition 2.21.
-/

public section

open CategoryTheory Limits Topology

universe w v u

namespace TopPair

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

/-- The relative small-chain isomorphism for the pair defined by a subset. -/
lemma isIso_homologyMap_restrictι_smallSingularSubcomplex_ofSubset {X : TopCat.{w}}
    (S : Set X) {κ : Type*} (F : κ → Set X) (hF : ∀ i, IsOpen (F i))
    (hcov : ⋃ i, F i = Set.univ) (n : ℕ) :
    IsIso (SSetPair.homologyMap ((toSSetPair.obj (ofSubset S)).restrictι
      (X.smallSingularSubcomplex F)) R n) := by
  have hi := isIso_homologyMap_restrictι_smallSingularSubcomplex R (ofSubset S) F hF hcov n
  erw [smallSingularSubcomplex_eq (ofSubset S) F] at hi
  exact hi

end TopPair

end
