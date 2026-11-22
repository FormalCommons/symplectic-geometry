/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import SymplecticGeometry.Topology.OpenPartialHomeomorph.Basic
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.System

/-!
# The local homology isomorphism of a chart, through its source

For a chart `φ : M → E` between `T₁` spaces and a point `a` of its source, the local homology
isomorphism `Hₖ(M, M ∖ {a}) ≅ Hₖ(E, E ∖ {φ a})` of the chart
(`TauCeti.singularHomologyComplSingletonIsoOfChart`), composed after the excision map of the
source, is the map of local homology induced by the source restriction `φ.sourceRestrict`
(`TauCeti.localHomologyMap_subtypeVal_comp_singularHomologyComplSingletonIsoOfChart_hom`).

This file is a part of Tau Ceti's
`TauCeti/AlgebraicTopology/Singular/LocalHomology/System.lean`, as of the commit `55525ca744`
(TauCetiProject/TauCeti#37381) of Tau Ceti's main branch, not yet in the pinned release, which
has only a private version of the lemma, without the preimage hypothesis `h`, in
`TauCeti/AlgebraicTopology/Singular/LocalHomology/Orientation/Smooth.lean`. It takes only that
lemma, under its Tau Ceti name, so that moving Tau Ceti past it deletes this file without renames.
Its statement, proof and docstring are Tau Ceti's, unchanged; this module docstring is new, and
`OpenPartialHomeomorph.sourceRestrict` comes from the copy
`SymplecticGeometry/Topology/OpenPartialHomeomorph/Basic.lean` of the same commit.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.3, the local homology groups `Hₙ(M | x)`, local
  orientations, and the comparison through `Hₙ(M | B)` for balls `B` in charts, which Hatcher
  uses to topologize the orientation covering `M_R`.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Set Topology

universe w v u

namespace TauCeti

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

section ChartIso

variable {M : Type w} [TopologicalSpace M] [T1Space M] {E : Type w} [TopologicalSpace E]
  [T1Space E] (φ : OpenPartialHomeomorph M E)

/-- **The chart isomorphism through the source.** The local homology isomorphism of a chart `φ`
at `a` (`TauCeti.singularHomologyComplSingletonIsoOfChart`) is the inverse of the excision
isomorphism of the source of `φ`, followed by the map induced by its canonical source
restriction `φ.sourceRestrict`. -/
theorem localHomologyMap_subtypeVal_comp_singularHomologyComplSingletonIsoOfChart_hom
    {a : M} (ha : a ∈ φ.source)
    (h : φ.sourceRestrict ⁻¹' {φ a} ⊆ ContinuousMap.subtypeVal φ.source ⁻¹' {a}) (k : ℕ) :
    localHomologyMap R (ContinuousMap.subtypeVal φ.source)
        (S := ContinuousMap.subtypeVal φ.source ⁻¹' {a}) (T := {a}) subset_rfl k ≫
          (singularHomologyComplSingletonIsoOfChart R φ ha k).hom =
      localHomologyMap R φ.sourceRestrict h k := by
  have h₁ : localHomologyMap R (ContinuousMap.subtypeVal φ.source)
      (S := ContinuousMap.subtypeVal φ.source ⁻¹' {a}) (T := {a}) subset_rfl k =
        TopPair.singularHomologyMap
        (TopPair.excisionMap (X := TopCat.of M) φ.source {a}ᶜ) R k := by
    -- The pairs agree only after unfolding the preimages of complements.
    erw [localHomologyMap_def]
    congr 1
    apply TopPair.hom_ext_of_fst
    ext z
    erw [TopPair.excisionMap_fst_apply, TopPair.ofSubsetMap_fst_apply]
    rfl
  have h₂ : localHomologyMap R φ.sourceRestrict h k =
      TopPair.singularHomologyMap ((TopPair.ofSubsetIso (X := TopCat.of φ.source)
          (Y := TopCat.of φ.target) φ.toHomeomorphSourceTarget
          (B := Subtype.val ⁻¹' {a}ᶜ) (B' := Subtype.val ⁻¹' {φ a}ᶜ)
          fun z ↦ (φ.injOn.eq_iff z.property ha).not.symm).hom ≫
        TopPair.excisionMap (X := TopCat.of E) φ.target {φ a}ᶜ) R k := by
    -- The pairs agree only after unfolding the preimages of complements.
    erw [localHomologyMap_def]
    congr 1
    apply TopPair.hom_ext_of_fst
    ext z
    rw [TopPair.Hom.fst_comp]
    erw [ConcreteCategory.comp_apply, TopPair.excisionMap_fst_apply, TopPair.ofSubsetIso_hom,
      TopPair.ofSubsetMap_fst_apply,
      TopPair.ofSubsetMap_fst_apply]
    exact φ.sourceRestrict_apply z
  rw [h₁, h₂, TopPair.singularHomologyMap_comp]
  exact singularHomologyMap_excisionMap_comp_singularHomologyComplSingletonIsoOfChart_hom R φ ha k

end ChartIso

end TauCeti
