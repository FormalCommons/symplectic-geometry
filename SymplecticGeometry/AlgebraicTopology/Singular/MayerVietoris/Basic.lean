/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.Basic
public import TauCeti.AlgebraicTopology.Singular.Reduced

/-!
# The middle map of the Mayer–Vietoris sequence of a disjoint cover

For a cover `X = U ∪ V` by two open sets, the second map `Hₙ(U) ⊞ Hₙ(V) ⟶ Hₙ(X)` of the
Mayer–Vietoris sequence of singular homology is an isomorphism when the homology of `U ∩ V`
vanishes in degrees `n` and `n - 1` (`TopCat.isIso_mayerVietorisFromBiprod_of_isZero`), by
exactness at its two ends. When `U` and `V` are disjoint, `U ∩ V` is empty and its homology
vanishes in every degree, so the sum of the maps induced by the inclusions is an isomorphism
(`TopCat.isIso_biprodDesc_singularHomologyFunctor_map_of_disjoint`).

These two lemmas are from Tau Ceti's main branch
(`TauCeti/AlgebraicTopology/Singular/MayerVietoris/Basic.lean`, same names), not yet in the
pinned release; they are stated here under their Tau Ceti names, so that moving Tau Ceti past them
deletes this file without renames. The statements and proofs are those of the commit
`020be269104296e16423165eccaf4c5bf7d05ede`, with one change: the proof of
`TopCat.isIso_biprodDesc_singularHomologyFunctor_map_of_disjoint` uses the pinned
`TauCeti.isZero_singularHomologyFunctor_of_isEmpty` where the main branch uses
`TauCeti.isZero_singularHomology_of_isEmpty`, which the pinned release does not have.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2, the Mayer–Vietoris sequences.
-/

public section

noncomputable section

open CategoryTheory Limits Topology

universe w v u

namespace TopCat

variable {X : TopCat.{w}} {U V : Set X}
  {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)

include hU hV hUV in
/-- If `Hₙ(U ∩ V)` vanishes, and so does `Hₘ(U ∩ V)` when `n = m + 1`, the second map
`Hₙ(U) ⊞ Hₙ(V) ⟶ Hₙ(X)` of the Mayer–Vietoris sequence of an open cover `X = U ∪ V` is an
isomorphism. -/
lemma isIso_mayerVietorisFromBiprod_of_isZero (n : ℕ)
    (h₀ : IsZero ((toSSet.obj (of ↥(U ∩ V))).homology R n))
    (h₁ : ∀ m, n = m + 1 → IsZero ((toSSet.obj (of ↥(U ∩ V))).homology R m)) :
    IsIso (SSet.mayerVietorisFromBiprod R (toSSet.map (ofHom (ContinuousMap.subtypeVal U)))
      (toSSet.map (ofHom (ContinuousMap.subtypeVal V))) n) := by
  have := (mayerVietoris_exact₂ R hU hV hUV n).mono_g (h₀.eq_of_src _ _)
  rcases n with _ | m
  · have := epi_mayerVietorisFromBiprod_zero R hUV
    exact isIso_of_mono_of_epi _
  · have := (mayerVietoris_exact₃ R hU hV hUV (m + 1) m).epi_f ((h₁ m rfl).eq_of_tgt _ _)
    exact isIso_of_mono_of_epi _

include hU hV hUV in
/-- For a cover of `X` by two disjoint open sets `U` and `V`, the sum `Hₙ(U) ⊞ Hₙ(V) ⟶ Hₙ(X)` of
the maps induced by the subspace inclusions is an isomorphism. -/
lemma isIso_biprodDesc_singularHomologyFunctor_map_of_disjoint (hd : Disjoint U V) (n : ℕ) :
    IsIso (biprod.desc
      (((AlgebraicTopology.singularHomologyFunctor C n).obj R).map
        (ofHom (ContinuousMap.subtypeVal U)))
      (((AlgebraicTopology.singularHomologyFunctor C n).obj R).map
        (ofHom (ContinuousMap.subtypeVal V)))) := by
  have : IsEmpty ↥(U ∩ V) := ⟨fun x ↦ Set.disjoint_left.1 hd x.property.1 x.property.2⟩
  have h (m : ℕ) := TauCeti.isZero_singularHomologyFunctor_of_isEmpty R (of ↥(U ∩ V)) m
  have := isIso_mayerVietorisFromBiprod_of_isZero R hU hV hUV n (h n) fun m _ ↦ h m
  -- The Mayer–Vietoris map is this map: singular homology is by definition the homology of the
  -- singular simplicial set (`TauCeti.singularHomologyFunctor_obj_map`).
  rwa [show SSet.mayerVietorisFromBiprod R _ _ n = biprod.desc _ _ from biprod.hom_ext' _ _
    ((SSet.inl_mayerVietorisFromBiprod R _ _ n).trans (biprod.inl_desc _ _).symm)
    ((SSet.inr_mayerVietorisFromBiprod R _ _ n).trans (biprod.inr_desc _ _).symm)] at this

end TopCat

end
