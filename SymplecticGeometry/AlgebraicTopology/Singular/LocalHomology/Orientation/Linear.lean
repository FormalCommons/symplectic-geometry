/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Orientation.Chart
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Linear

/-!
# The local orientation of an orientation in the identity chart

In a real inner product space `X` of dimension `n + 1`, the local orientation at the origin
selected by an orientation `ν` (`Orientation.localOrientation`) is the one selected by `ν` in the
identity chart of `X` (`Orientation.localOrientation_eq_localOrientationOfOrientedChart_refl`).
The proof compares both with the Euclidean model through a linear isometry, which carries the
identity-chart local orientations at the origin to one another
(`LinearIsometryEquiv.localHomologyMap_localOrientationOfOrientedChart_refl`).

This file is a part of Tau Ceti's
`TauCeti/AlgebraicTopology/Singular/LocalHomology/Orientation/Linear.lean`, as of the commit
`55525ca744` (TauCetiProject/TauCeti#37381) of Tau Ceti's main branch, not yet in the pinned
release. The two theorems are stated here under their Tau Ceti names, so that moving Tau Ceti past
them deletes this file without renames. The statements and proofs are Tau Ceti's, with two
changes that the pinned release requires: the membership
`x ∈ (OpenPartialHomeomorph.refl X).source` is proved by rewriting with
`OpenPartialHomeomorph.refl_source`, as the pinned release does, since it lacks
`OpenPartialHomeomorph.mem_refl_source`; and the Euclidean model, a private abbreviation `Model n`
of Tau Ceti's file, is written out as `EuclideanSpace ℝ (ULift (Fin (n + 1)))`.

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
          (by rw [OpenPartialHomeomorph.refl_source]; exact Set.mem_univ _) ν hX).val =
      ((OpenPartialHomeomorph.refl Y).localOrientationOfOrientedChart
        (by rw [OpenPartialHomeomorph.refl_source]; exact Set.mem_univ _)
        (ν.map _ f.toLinearEquiv) hY).val := by
  set R := ModuleCat.of ℤ (ULift.{w} ℤ)
  let eX := singularHomologyComplSingletonIsoOfOrientation R (OpenPartialHomeomorph.refl X)
    (by rw [OpenPartialHomeomorph.refl_source]; exact Set.mem_univ 0) ν hX
  let eY := singularHomologyComplSingletonIsoOfOrientation R (OpenPartialHomeomorph.refl Y)
    (by rw [OpenPartialHomeomorph.refl_source]; exact Set.mem_univ 0)
    (ν.map _ f.toLinearEquiv) hY
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
      (by rw [OpenPartialHomeomorph.refl_source]; exact Set.mem_univ _) ν hX := by
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

end
