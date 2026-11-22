/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.MayerVietoris
public import TauCeti.AlgebraicTopology.Cohomology.Point

/-!
# The middle map of the compactly supported Mayer–Vietoris sequence of a disjoint cover

For a cover `X = U ∪ V` by two open sets, the middle map `Hⁿ_c(U) ⊞ Hⁿ_c(V) ⟶ Hⁿ_c(X)` of the
Mayer–Vietoris sequence of cohomology with compact supports is an isomorphism when `Hⁿ_c(U ∩ V)`
and `Hⁿ⁺¹_c(U ∩ V)` vanish, by exactness at its two ends
(`TopCat.isIso_compactSupportCohomologyMayerVietorisFromBiprod_of_isZero`). When `U` and `V`
are disjoint, `U ∩ V` is empty, hence compact, and its cohomology vanishes in every degree, so the
sum of the extensions by zero is an isomorphism
(`TopCat.isIso_biprodDesc_compactSupportCohomologyExtend_of_disjoint`).

These two lemmas are from Tau Ceti's main branch
(`TauCeti/AlgebraicTopology/Cohomology/CompactSupport/MayerVietoris.lean`, same names), not yet in
the pinned release; they are stated here under their Tau Ceti names, so that moving Tau Ceti past
them deletes this file without renames.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3, the
  Mayer–Vietoris sequence for cohomology with compact supports in the proof of Lemma 3.36.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace Topology Opens

universe v u

namespace TopCat

variable {C : Type u} [Category.{v} C] [HasCoproducts.{v} C] [Abelian C] {R : C}
  {k : Type v} [Ring k] [Linear k C] {M : C} {X : TopCat.{v}} (U V : Opens X) [T2Space X]

variable (R k M) in
/-- If `Hⁿ_c(U ∩ V)` and `Hⁿ⁺¹_c(U ∩ V)` vanish, the middle map `Hⁿ_c(U) ⊞ Hⁿ_c(V) ⟶ Hⁿ_c(X)` of
the Mayer–Vietoris sequence of an open cover `X = U ∪ V` is an isomorphism. -/
lemma isIso_compactSupportCohomologyMayerVietorisFromBiprod_of_isZero (hUV : U ⊔ V = ⊤) (n : ℕ)
    (h₀ : IsZero (((Opens.toTopCat X).obj (U ⊓ V)).compactSupportCohomology R k M n))
    (h₁ : IsZero (((Opens.toTopCat X).obj (U ⊓ V)).compactSupportCohomology R k M (n + 1))) :
    IsIso (compactSupportCohomologyMayerVietorisFromBiprod R k M U V n) := by
  have := (compactSupportCohomologyMayerVietoris_exact₂ R k M U V hUV n).mono_g
    (h₀.eq_of_src _ _)
  have := (compactSupportCohomologyMayerVietoris_exact₃ R k M U V hUV n (n + 1)).epi_f
    (h₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

variable (R k M) in
/-- For a cover of `X` by two disjoint open sets `U` and `V`, the sum
`Hⁿ_c(U) ⊞ Hⁿ_c(V) ⟶ Hⁿ_c(X)` of the extensions by zero along the subspace inclusions `↥U → X` and
`↥V → X` is an isomorphism. -/
lemma isIso_biprodDesc_compactSupportCohomologyExtend_of_disjoint (hUV : U ⊔ V = ⊤)
    (hd : Disjoint U V) (n : ℕ) :
    IsIso (biprod.desc
      (compactSupportCohomologyExtend (R := R) (k := k) (M := M)
        (f := ofHom (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, X))) U.isOpenEmbedding' n)
      (compactSupportCohomologyExtend (R := R) (k := k) (M := M)
        (f := ofHom (⟨Subtype.val, continuous_subtypeVal⟩ : C(V, X))) V.isOpenEmbedding' n)) := by
  have : IsEmpty ((Opens.toTopCat X).obj (U ⊓ V)) :=
    ⟨fun x ↦ Set.disjoint_left.1 (Opens.coe_disjoint.2 hd) (Opens.mem_inf.1 x.property).1
      (Opens.mem_inf.1 x.property).2⟩
  have h (m : ℕ) := (TauCeti.isZero_singularCohomology_of_isEmpty R k M
    ((Opens.toTopCat X).obj (U ⊓ V)) m).of_iso (compactSupportCohomologyIsoOfCompactSpace m)
  have := isIso_compactSupportCohomologyMayerVietorisFromBiprod_of_isZero R k M U V hUV n (h n)
    (h (n + 1))
  -- The components of the middle Mayer–Vietoris map are these extensions, read on
  -- `(Opens.toTopCat X).obj U = TopCat.of ↥U`, with `Opens.inclusion' U` the subspace inclusion.
  rwa [show compactSupportCohomologyMayerVietorisFromBiprod R k M U V n = biprod.desc _ _ from
    biprod.hom_ext' _ _
      ((inl_compactSupportCohomologyMayerVietorisFromBiprod R k M U V n).trans
        (biprod.inl_desc _ _).symm)
      ((inr_compactSupportCohomologyMayerVietorisFromBiprod R k M U V n).trans
        (biprod.inr_desc _ _).symm)] at this

end TopCat

end
