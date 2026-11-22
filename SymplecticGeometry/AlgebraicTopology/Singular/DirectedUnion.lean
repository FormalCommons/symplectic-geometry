/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopCat.Opens
public import TauCeti.AlgebraicTopology.Singular.DirectedUnion
public import TauCeti.Topology.Sets.Compacts

/-!
# Singular homology of a directed union of open sets

Let `X` be covered by a directed family of open sets `U j`. Every compact subset of `X` lies in
some `U j`, so singular homology of `X` is the colimit of the singular homology of the `U j`
along the inclusions (`TauCeti.isColimitMapCoconeOpensInclusionCocone`, from Tau Ceti's
`TauCeti.isColimitMapCoconeSingularHomology`). With coefficients in a module, this says
concretely that every class of `X` comes from some `U j`
(`TauCeti.exists_singularHomologyMap_inclusion'_eq_of_iSup_eq_top`), and that a class of `U i`
that vanishes in `X` already vanishes in some larger `U j`
(`TauCeti.exists_singularHomologyMap_toTopCat_map_eq_zero_of_iSup_eq_top`).

## Main definitions and results

* `TauCeti.opensInclusionCocone`: the inclusions of the members of a monotone family of open sets,
  as a cocone with apex `X`.
* `TauCeti.isColimitMapCoconeOpensInclusionCocone`: singular homology takes it to a colimit cocone
  when the family is directed and covers `X`.
* `TauCeti.exists_singularHomologyMap_inclusion'_eq_of_iSup_eq_top` and
  `TauCeti.exists_singularHomologyMap_toTopCat_map_eq_zero_of_iSup_eq_top`: the elementwise
  description of that colimit.

These are from Tau Ceti's main branch (`TauCeti/AlgebraicTopology/Singular/DirectedUnion.lean`, same
names), as of the commit `b9a3084bbb4cc2ac2c5a0b3ae0323198b47a34b8`, not yet in the pinned release;
they are stated here under their Tau Ceti names, so that moving Tau Ceti past them deletes this file
without renames.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Proposition 3.33: singular
  homology commutes with directed unions of open sets.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology Topology TopCat TopologicalSpace

universe w

namespace TauCeti

variable {A : Type w} [Ring A] (M : ModuleCat.{w} A) (n : ℕ) {X : TopCat.{w}} {J : Type}
  [Preorder J] {U : J → Opens X} (hU : Monotone U) (hcover : ⨆ j, U j = ⊤)

/-- The inclusions of the members of a monotone family of open sets of `X`, as a cocone with apex
`X`. -/
-- Its point and legs must compute, so that the legs are the inclusions on the nose.
@[expose, simps]
def opensInclusionCocone : Cocone (hU.functor ⋙ Opens.toTopCat X) where
  pt := X
  ι := { app j := Opens.inclusion' (U j) }

include hcover in
/-- **Singular homology of a directed union of open sets.** Singular homology of a space covered by
a directed family of open sets is the colimit of the singular homology of its members, along the
inclusions. -/
def isColimitMapCoconeOpensInclusionCocone [IsDirected J (· ≤ ·)] [Nonempty J] :
    IsColimit (((singularHomologyFunctor (ModuleCat.{w} A) n).obj M).mapCocone
      (opensInclusionCocone hU)) :=
  isColimitMapCoconeSingularHomology M n _ (fun j ↦ (U j).isOpenEmbedding.isEmbedding)
    fun K hK ↦ by
      obtain ⟨j, hj⟩ :=
        Compacts.exists_subset_of_iSup_eq_top hU.directed_le hcover ⟨K, hK⟩
      exact ⟨j, fun x hx ↦ ⟨⟨x, hj hx⟩, rfl⟩⟩

include hU hcover in
/-- **Every homology class comes from a member of a directed open cover.** With coefficients in a
module, every singular homology class of a space covered by a directed family of open sets is the
image of a class of one of its members. -/
theorem exists_singularHomologyMap_inclusion'_eq_of_iSup_eq_top [IsDirected J (· ≤ ·)]
    [Nonempty J] (x : ((singularHomologyFunctor (ModuleCat.{w} A) n).obj M).obj X) :
    ∃ j y, ((singularHomologyFunctor _ n).obj M).map (Opens.inclusion' (U j)) y = x := by
  have : PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat.{w} A)) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  exact Concrete.isColimit_exists_rep _ (isColimitMapCoconeOpensInclusionCocone M n hU hcover) x

include hcover in
/-- **Vanishing of a homology class is detected in a member of a directed open cover.** With
coefficients in a module, a singular homology class of one member `U i` of a directed open cover of
a space that vanishes in the space already vanishes in some larger member `U j`. -/
theorem exists_singularHomologyMap_toTopCat_map_eq_zero_of_iSup_eq_top [IsDirected J (· ≤ ·)]
    {i : J}
    (y : ((singularHomologyFunctor (ModuleCat.{w} A) n).obj M).obj ((Opens.toTopCat X).obj (U i)))
    (hy : ((singularHomologyFunctor _ n).obj M).map (Opens.inclusion' (U i)) y = 0) :
    ∃ j, ∃ hij : i ≤ j,
      ((singularHomologyFunctor _ n).obj M).map ((Opens.toTopCat X).map (homOfLE (hU hij))) y =
        0 := by
  have : Nonempty J := ⟨i⟩
  have : PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat.{w} A)) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  obtain ⟨j, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq (j := i) _
    (isColimitMapCoconeOpensInclusionCocone M n hU hcover) y 0 (by rw [map_zero]; exact hy)
  rw [map_zero] at hfg
  exact ⟨j, f.le, hfg⟩

end TauCeti

end
