/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Orientation.Chart
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Linear

/-!
# The local orientation of an orientation in the identity chart, and centred charts

In a real inner product space `X` of dimension `n + 1`, the local orientation at the origin
selected by an orientation `ν` (`Orientation.localOrientation`) is the one selected by `ν` in the
identity chart of `X` (`Orientation.localOrientation_eq_localOrientationOfOrientedChart_refl`).
The proof compares both with the Euclidean model through a linear isometry, which carries the
identity-chart local orientations at the origin to one another
(`LinearIsometryEquiv.localHomologyMap_localOrientationOfOrientedChart_refl`).

For a chart `φ` of `M` with values in `X`, a point `z` of its source and a continuous linear
equivalence `L : X ≃L[ℝ] F`, the map `x ↦ L (φ x - φ z)` on the source of `φ` carries the local
orientation that `ν` selects in `φ` at `z`, read in the source through excision, to the local
orientation of `F` at the origin selected by `ν.map L`
(`OpenPartialHomeomorph.localHomologyMap_chart_localOrientationOfOrientedChart`). It factors the
map into the source restriction of `φ`
(`OpenPartialHomeomorph.localHomologyMap_sourceRestrict_localOrientationOfOrientedChart`), a
translation, and `L`.

This file is a part of Tau Ceti's
`TauCeti/AlgebraicTopology/Singular/LocalHomology/Orientation/Linear.lean`, as of the commit
`55525ca744` (TauCetiProject/TauCeti#37381) of Tau Ceti's main branch, not yet in the pinned
release. The three theorems are stated here under their Tau Ceti names, so that moving Tau Ceti
past them deletes this file without renames. The statements and proofs are Tau Ceti's, with one
change that the pinned release requires: the Euclidean model, a private abbreviation `Model n` of
Tau Ceti's file, is written out as `EuclideanSpace ℝ (ULift (Fin (n + 1)))`. The lemmas of the
same commit that the pinned release lacks, `OpenPartialHomeomorph.mem_refl_source` among them,
come from the copies `SymplecticGeometry/Topology/OpenPartialHomeomorph/Basic.lean` and
`SymplecticGeometry/AlgebraicTopology/Singular/LocalHomology/Orientation/Chart.lean`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3 (local orientations).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §9 and §10 (orientations of vector spaces and the fibre normalization of the
  Thom class).
-/

public section

noncomputable section

open CategoryTheory Module TauCeti

universe w

namespace TauCeti

section InnerProduct

variable {X Y : Type w} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] {n : ℕ}

/-- A linear isometry carries the local orientation at the origin selected by `ν` in the identity
chart to the one selected by the transported orientation in the identity chart: both are read
through the connecting morphism, radial projection, and the sphere generators, which the isometry
preserves. -/
theorem _root_.LinearIsometryEquiv.localHomologyMap_localOrientationOfOrientedChart_refl
    (f : X ≃ₗᵢ[ℝ] Y) (ν : Orientation ℝ X (Fin (n + 1))) (hX : finrank ℝ X = n + 1)
    (hY : finrank ℝ Y = n + 1)
    (h : (⟨f, f.continuous⟩ : C(X, Y)) ⁻¹' {0} ⊆ {0}) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{w} ℤ)) (⟨f, f.continuous⟩ : C(X, Y)) h (n + 1)
        ((OpenPartialHomeomorph.refl X).localOrientationOfOrientedChart
          (OpenPartialHomeomorph.mem_refl_source _) ν hX).val =
      ((OpenPartialHomeomorph.refl Y).localOrientationOfOrientedChart
        (OpenPartialHomeomorph.mem_refl_source _)
        (ν.map _ f.toLinearEquiv) hY).val := by
  set R := ModuleCat.of ℤ (ULift.{w} ℤ)
  let eX := singularHomologyComplSingletonIsoOfOrientation R (OpenPartialHomeomorph.refl X)
    (OpenPartialHomeomorph.mem_refl_source 0) ν hX
  let eY := singularHomologyComplSingletonIsoOfOrientation R (OpenPartialHomeomorph.refl Y)
    (OpenPartialHomeomorph.mem_refl_source 0) (ν.map _ f.toLinearEquiv) hY
  -- Radial projection onto the unit spheres commutes with the isometry.
  have hsq : TopPair.Hom.snd (TopPair.ofSubsetMap (X := TopCat.of X) (Y := TopCat.of Y)
        (TopCat.ofHom (⟨f, f.continuous⟩ : C(X, Y))) (B := {0}ᶜ) (B' := {0}ᶜ)
        ((Set.mapsTo_preimage _ _).mono_left (Set.compl_subset_compl.2 h))) ≫
      TopCat.ofHom (complSingletonHomotopyEquivSphere (0 : Y)).toFun =
      TopCat.ofHom (complSingletonHomotopyEquivSphere (0 : X)).toFun ≫
        TopCat.ofHom ⟨f.toLinearIsometry.unitSphereMap,
          f.toLinearIsometry.continuous_unitSphereMap⟩ := by
    exact f.snd_ofSubsetMap_comp_complSingletonHomotopyEquivSphere 0 0 f.map_zero
  have key : localHomologyMap R (⟨f, f.continuous⟩ : C(X, Y)) h (n + 1) ≫ eY.hom = eX.hom := by
    simp only [eX, eY, singularHomologyComplSingletonIsoOfOrientation_refl_hom]
    rw [localHomologyMap_def, ← TopPair.reducedSingularHomologyδ_naturality_assoc]
    congr 1
    -- The composite is only type-correct after unfolding the subspace of the pair.
    erw [← Functor.map_comp_assoc, hsq, Functor.map_comp_assoc]
    exact congrArg _ (reducedSingularHomologySphereIsoOfOrientation_hom_naturality R ν
      (ν.map _ f.toLinearEquiv) f rfl hX)
  rw [OpenPartialHomeomorph.coe_localOrientationOfOrientedChart,
    OpenPartialHomeomorph.coe_localOrientationOfOrientedChart]
  apply (ConcreteCategory.bijective_of_isIso eY.hom).1
  rw [← ConcreteCategory.comp_apply, key]
  exact (eX.inv_hom_id_apply 1).trans (eY.inv_hom_id_apply 1).symm

end InnerProduct

end TauCeti

namespace Orientation

variable {X : Type w} [NormedAddCommGroup X] [InnerProductSpace ℝ X] {n : ℕ}

/-- **The local orientation of an orientation in the identity chart.** In a real inner product
space `X` of dimension `n + 1`, the local orientation at the origin selected by an orientation `ν`
(`Orientation.localOrientation`) is the one selected by `ν` in the identity chart of `X`. -/
theorem localOrientation_eq_localOrientationOfOrientedChart_refl
    (ν : Orientation ℝ X (Fin (n + 1))) (hX : finrank ℝ X = n + 1) :
    ν.localOrientation hX = (OpenPartialHomeomorph.refl X).localOrientationOfOrientedChart
      (OpenPartialHomeomorph.mem_refl_source _) ν hX := by
  have := FiniteDimensional.of_finrank_eq_succ hX
  -- Compare both with the Euclidean model through a linear isometry.
  let f : X ≃ₗᵢ[ℝ] EuclideanSpace ℝ (ULift.{w} (Fin (n + 1))) :=
    ((stdOrthonormalBasis ℝ X).reindex ((finCongr hX).trans Equiv.ulift.symm)).repr
  have hM : finrank ℝ (EuclideanSpace ℝ (ULift.{w} (Fin (n + 1)))) = n + 1 :=
    finrank_euclideanSpace_ulift_fin (n + 1)
  have hmap := localOrientation_map f.toContinuousLinearEquiv ν hX hM
  rw [localOrientation_euclideanSpace] at hmap
  apply Subtype.ext
  apply (ConcreteCategory.bijective_of_isIso (TopPair.singularHomologyMap
    f.toContinuousLinearEquiv.complZeroPairIso.hom (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1))).1
  rw [← LocalOrientation.coe_map, ← hmap, ContinuousLinearEquiv.complZeroPairIso_hom]
  have h := f.localHomologyMap_localOrientationOfOrientedChart_refl ν hX hM
    (fun x hx ↦ by simpa using hx)
  rw [← localHomologyMap_def]
  exact h.symm

end Orientation

namespace TauCeti

section Chart

variable {M X F : Type w} [TopologicalSpace M] [T1Space M] [NormedAddCommGroup X]
  [InnerProductSpace ℝ X] [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}

/-- **An oriented chart, followed by a linear equivalence, reads the local orientation it selects
as the local orientation of the transported orientation.** Let `φ` be a chart of `M` with values in
a real inner product space `X`, `ν` an orientation of `X`, and `L : X ≃L[ℝ] F` a linear
equivalence. The map `x ↦ L (φ x - φ z)` on the source of `φ` carries the local orientation of `M`
at `z` selected by `ν` in `φ`, read in the source through excision, to the local orientation of `F`
at the origin selected by the transported orientation `ν.map L`. -/
theorem _root_.OpenPartialHomeomorph.localHomologyMap_chart_localOrientationOfOrientedChart
    (φ : OpenPartialHomeomorph M X) {z : M} (hz : z ∈ φ.source) (L : X ≃L[ℝ] F)
    (ν : Orientation ℝ X (Fin (n + 1))) (hX : finrank ℝ X = n + 1) (hF : finrank ℝ F = n + 1)
    (h : (((L : X →L[ℝ] F) : C(X, F)).comp
      ((⟨fun y ↦ y - φ z, by fun_prop⟩ : C(X, X)).comp φ.sourceRestrict)) ⁻¹' {0} ⊆ {⟨z, hz⟩}) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{w} ℤ))
        (((L : X →L[ℝ] F) : C(X, F)).comp
          ((⟨fun y ↦ y - φ z, by fun_prop⟩ : C(X, X)).comp φ.sourceRestrict))
        (S := {⟨z, hz⟩}) (T := {0}) h (n + 1)
        ((φ.open_source.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨z, hz⟩ (n + 1)).symm
          (φ.localOrientationOfOrientedChart hz ν hX)).val =
      ((ν.map _ L.toLinearEquiv).localOrientation hF).val := by
  set Z := ModuleCat.of ℤ (ULift.{w} ℤ)
  set c := ((φ.open_source.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨z, hz⟩ (n + 1)).symm
    (φ.localOrientationOfOrientedChart hz ν hX)).val
  -- Factor the canonical map into the restricted chart, the centering translation, and `L`.
  set sR := φ.sourceRestrict
  let T : C(X, X) := ⟨fun y ↦ y - φ z, by fun_prop⟩
  let Lc : C(X, F) := ((L : X →L[ℝ] F) : C(X, F))
  have hsR : sR ⁻¹' {φ z} ⊆ {⟨z, hz⟩} := fun x hx ↦ Subtype.ext (φ.sourceRestrict_preimage hz hx)
  have hT : T ⁻¹' {0} ⊆ {φ z} := fun y hy ↦ sub_eq_zero.1 hy
  have hL : Lc ⁻¹' {0} ⊆ {0} := fun y hy ↦ by simpa [Lc] using hy
  have hcomp : localHomologyMap Z (Lc.comp (T.comp sR)) h (n + 1) =
      localHomologyMap Z sR hsR (n + 1) ≫
      localHomologyMap Z T hT (n + 1) ≫ localHomologyMap Z Lc hL (n + 1) := by
    rw [localHomologyMap_comp, localHomologyMap_comp,
      localHomologyMap_congr Z (ContinuousMap.comp_assoc Lc T sR).symm]
  -- The restricted chart carries `c` to the local orientation of `X` at `φ z` selected by `ν` in
  -- the identity chart.
  have hA := φ.localHomologyMap_sourceRestrict_localOrientationOfOrientedChart hz ν hX hsR
  -- The translation carries it to the local orientation at the origin, which `L` carries to the
  -- local orientation selected by `ν.map L`.
  have hB := localHomologyMap_translate_localOrientationOfOrientedChart_refl
    (OpenPartialHomeomorph.mem_refl_source (φ z)) (OpenPartialHomeomorph.mem_refl_source 0)
    (by simpa only [zero_add] using hT) ν hX
  simp only [zero_add] at hB
  have hC : localHomologyMap Z Lc hL (n + 1)
      ((OpenPartialHomeomorph.refl X).localOrientationOfOrientedChart
        (OpenPartialHomeomorph.mem_refl_source 0) ν hX).val =
      ((ν.map _ L.toLinearEquiv).localOrientation hF).val := by
    rw [Orientation.localOrientation_map L ν hX hF, LocalOrientation.coe_map,
      ← Orientation.localOrientation_eq_localOrientationOfOrientedChart_refl,
      ContinuousLinearEquiv.complZeroPairIso_hom, ← localHomologyMap_def]
  rw [hcomp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hA, hB, hC]

end Chart

end TauCeti

end
