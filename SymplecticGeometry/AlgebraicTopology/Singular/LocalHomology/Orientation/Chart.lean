/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.System
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Chart
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.OpenEmbedding

/-!
# Oriented charts: restriction to the source, and radial projection under linear isometries

Two facts about the local orientation `φ.localOrientationOfOrientedChart hz ν hX` that a chart
`φ` of `M` with values in an oriented real inner product space selects at a point `z`.

* The restriction `φ.sourceRestrict` of `φ` to its source carries this local orientation, read
  in the source through excision, to the one that the identity chart of the model selects at
  `φ z`
  (`OpenPartialHomeomorph.localHomologyMap_sourceRestrict_localOrientationOfOrientedChart`).
* A linear isometry equivalence `e : E ≃ₗᵢ[ℝ] F` followed by radial projection about `q = e p`
  onto the unit sphere of `F` is radial projection about `p` onto the unit sphere of `E`
  followed by the restriction of `e` to the unit spheres
  (`LinearIsometryEquiv.snd_ofSubsetMap_comp_complSingletonHomotopyEquivSphere`).

This file is a part of Tau Ceti's
`TauCeti/AlgebraicTopology/Singular/LocalHomology/Orientation/Chart.lean`, as of the commit
`55525ca744` (TauCetiProject/TauCeti#37381) of Tau Ceti's main branch, not yet in the pinned
release. That commit added the first lemma, and made the second public and general, from a
private lemma about the point `e p`. Both are stated here under their Tau Ceti names, so that
moving Tau Ceti past them deletes this file without renames. Their statements and proofs are Tau
Ceti's, unchanged. The first uses `OpenPartialHomeomorph.sourceRestrict`,
`OpenPartialHomeomorph.mem_refl_source` and
`TauCeti.localHomologyMap_subtypeVal_comp_singularHomologyComplSingletonIsoOfChart_hom` from the
same commit, which the pinned release lacks; they are copied in
`SymplecticGeometry/Topology/OpenPartialHomeomorph/Basic.lean` and
`SymplecticGeometry/AlgebraicTopology/Singular/LocalHomology/System.lean`.

The local generators of Tau Ceti's file are those of an oriented coordinate chart in Hatcher's
*Algebraic Topology*, Section 3.3.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Module

universe w

namespace TauCeti

section Restriction

variable {M X : Type w} [TopologicalSpace M] [T1Space M] [NormedAddCommGroup X]
  [InnerProductSpace ℝ X] {n : ℕ}

/-- **A chart carries the local orientation it selects to the one selected by the identity chart.**
Let `φ` be a chart of `M` with values in a real inner product space `X` and `ν` an orientation of
`X`. The restriction of `φ` to its source carries the local orientation of `M` at `z` selected by
`ν` in `φ`, read in the source through excision, to the local orientation of `X` at `φ z` selected
by `ν` in the identity chart. -/
theorem _root_.OpenPartialHomeomorph.localHomologyMap_sourceRestrict_localOrientationOfOrientedChart
    (φ : OpenPartialHomeomorph M X) {z : M} (hz : z ∈ φ.source)
    (ν : Orientation ℝ X (Fin (n + 1))) (hX : finrank ℝ X = n + 1)
    (h : φ.sourceRestrict ⁻¹' {φ z} ⊆ {⟨z, hz⟩}) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{w} ℤ)) φ.sourceRestrict (S := {⟨z, hz⟩})
        (T := {φ z}) h (n + 1)
          ((φ.open_source.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨z, hz⟩ (n + 1)).symm
            (φ.localOrientationOfOrientedChart hz ν hX)).val =
      ((OpenPartialHomeomorph.refl X).localOrientationOfOrientedChart
        (OpenPartialHomeomorph.mem_refl_source (φ z)) ν hX).val := by
  set Z := ModuleCat.of ℤ (ULift.{w} ℤ)
  set c := ((φ.open_source.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨z, hz⟩ (n + 1)).symm
    (φ.localOrientationOfOrientedChart hz ν hX)).val
  set sR := φ.sourceRestrict
  have hsR' : sR ⁻¹' {φ z} ⊆ ContinuousMap.subtypeVal φ.source ⁻¹' {z} :=
    φ.sourceRestrict_preimage hz
  -- Read through the excision of the source, `c` is the oriented-chart local orientation, which
  -- is defined by the chart isomorphism.
  have hid : ContinuousMap.id φ.source ⁻¹' (ContinuousMap.subtypeVal φ.source ⁻¹' {z}) ⊆
      {⟨z, hz⟩} := fun x (hx : x.val = z) ↦ Subtype.ext hx
  have hc : localHomologyMap Z (ContinuousMap.subtypeVal φ.source) (S := {⟨z, hz⟩}) (T := {z})
      (fun x (hx : x.val = z) ↦ Subtype.ext hx) (n + 1) c =
        (φ.localOrientationOfOrientedChart hz ν hX).val :=
    φ.open_source.isOpenEmbedding_subtypeVal.localHomologyMap_localOrientationEquiv_symm ⟨z, hz⟩
      (φ.localOrientationOfOrientedChart hz ν hX) (fun x (hx : x.val = z) ↦ Subtype.ext hx)
  have h₁ : localHomologyMap Z sR h (n + 1) c =
      (localHomologyMap Z (ContinuousMap.id φ.source) hid (n + 1) ≫
        localHomologyMap Z sR hsR' (n + 1)) c := by
    rw [localHomologyMap_comp, localHomologyMap_congr Z (ContinuousMap.comp_id sR)]
  have h₂ : (localHomologyMap Z (ContinuousMap.id φ.source) hid (n + 1) ≫
      localHomologyMap Z sR hsR' (n + 1)) c =
      (singularHomologyComplSingletonIsoOfChart Z φ hz (n + 1)).hom
        (localHomologyMap Z (ContinuousMap.subtypeVal φ.source) (S := {⟨z, hz⟩}) (T := {z})
          (fun x (hx : x.val = z) ↦ Subtype.ext hx) (n + 1) c) := by
    rw [← localHomologyMap_subtypeVal_comp_singularHomologyComplSingletonIsoOfChart_hom Z φ hz
      hsR' (n + 1), ← Category.assoc, localHomologyMap_comp,
      localHomologyMap_congr Z (ContinuousMap.comp_id _), ConcreteCategory.comp_apply]
  rw [h₁, h₂, hc, OpenPartialHomeomorph.coe_localOrientationOfOrientedChart,
    OpenPartialHomeomorph.coe_localOrientationOfOrientedChart]
  let e₀ := singularHomologyComplSingletonIsoOfOrientation Z (OpenPartialHomeomorph.refl X)
    (OpenPartialHomeomorph.mem_refl_source (φ z)) ν hX
  apply (ConcreteCategory.bijective_of_isIso e₀.hom).1
  rw [← ConcreteCategory.comp_apply, ← singularHomologyComplSingletonIsoOfOrientation_hom_eq,
    Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]

end Restriction

section LinearIsometryEquiv

variable {E F : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Applying a linear isometry equivalence followed by radial projection about `e p` is radial
projection about `p` followed by the restriction of `e` to the unit spheres. -/
theorem
    _root_.LinearIsometryEquiv.snd_ofSubsetMap_comp_complSingletonHomotopyEquivSphere
    (e : E ≃ₗᵢ[ℝ] F) (p : E) (q : F) (hq : e p = q) :
    TopPair.Hom.snd (TopPair.ofSubsetMap (X := TopCat.of E) (Y := TopCat.of F)
        (TopCat.ofHom ⟨e, e.continuous⟩) (B := {p}ᶜ) (B' := {q}ᶜ)
        (fun _ hy h ↦ hy (e.injective (h.trans hq.symm)))) ≫
      TopCat.ofHom (complSingletonHomotopyEquivSphere q).toFun =
    TopCat.ofHom (complSingletonHomotopyEquivSphere p).toFun ≫
      TopCat.ofHom ⟨e.toLinearIsometry.unitSphereMap,
        e.toLinearIsometry.continuous_unitSphereMap⟩ := by
  subst q
  ext z
  -- The subspace of `TopPair.ofSubset` is the subtype only after unfolding the pair.
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  refine (coe_complSingletonHomotopyEquivSphere_apply (e p) _).trans ?_
  -- Unfold `TopPair.ofSubset` on the subspace component to apply `TopPair.ofSubsetMap_snd_apply`.
  erw [TopPair.ofSubsetMap_snd_apply]
  simp only [TopCat.hom_ofHom, ContinuousMap.coe_mk, LinearIsometry.coe_unitSphereMap_apply,
    LinearIsometryEquiv.coe_toLinearIsometry, ← map_sub, e.norm_map, ← map_smul]
  exact (congrArg e (coe_complSingletonHomotopyEquivSphere_apply p z)).symm

end LinearIsometryEquiv

end TauCeti
