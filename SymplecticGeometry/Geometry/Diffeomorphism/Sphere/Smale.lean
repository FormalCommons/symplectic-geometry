/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Congr
public import TauCeti.Geometry.Diffeomorphism.Sphere
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Sphere
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.Topology.Homotopy.Equiv
public import SymplecticGeometry.Geometry.Diffeomorphism.Sphere.Trivialization
public import SymplecticGeometry.Geometry.Diffeomorphism.OrthogonalSphere
import SymplecticGeometry.Geometry.Diffeomorphism.Orientation
import SymplecticGeometry.Topology.FiberBundle.Basic
import SymplecticGeometry.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.AlgebraicTopology.FundamentalGroup.HomotopyEquiv
import TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph
import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.UniversalCover
import TauCeti.Topology.Homotopy.DeformationRetract
import TauCeti.Topology.Homotopy.HomotopyEquiv
import TauCeti.Topology.Algebra.Group.ClosedSubgroup

/-!
# Diffeomorphisms of the round 2-sphere and Smale's theorem

The group `Diff⁺(S²)` of `ComplexStructure.lean` is a group of diffeomorphisms of the Riemann
sphere `OnePoint ℂ`. This file deforms it onto its rotations, and carries it, its rotations and
the deformation to the unit sphere `S²` of `EuclideanSpace ℝ (Fin 3)`, by conjugation along a
fixed diffeomorphism. This proves Smale's theorem: `Diff⁺(S²)` retracts onto `SO(3)` by a
homotopy that keeps every rotation fixed.

## The round sphere and its rotations

* `SymplecticGeometry.roundSphereDiffeomorph`: Tau Ceti's diffeomorphism
  `OnePoint.diffeomorphSphere v ι` for the north pole `v = (0, 0, 1)` and the isometry
  `ι z = (Re z, -Im z, 0)` (`OnePoint.sphereCoordsIsometry`), as a smooth diffeomorphism. Its
  values are the round sphere coordinates `OnePoint.sphereCoords`
  (`SymplecticGeometry.coe_roundSphereDiffeomorph_apply`, from Tau Ceti's
  `OnePoint.diffeomorphSphere_sphereCoordsIsometry_apply`).
* `SymplecticGeometry.roundDiffPlus`: the diffeomorphisms of `S²` that preserve the outward-normal
  orientation `Orientation.sphereOrientation` of the standard orientation of `ℝ³` at every point.
* `SymplecticGeometry.map_diffPlus_diffCongr`: conjugation by `roundSphereDiffeomorph` maps
  `diffPlus` onto `roundDiffPlus`. The orientation of the complex manifold `OnePoint ℂ`, carried to
  `S²`, is the outward-normal orientation or its opposite, since the Riemann sphere is connected
  (`TauCeti.Manifold.Orientation.eq_or_eq_neg`), and a diffeomorphism preserves an orientation
  exactly when it preserves the opposite one.
* `SymplecticGeometry.diffCongr_mobiusHom_toPSL`: the conjugate of the Möbius transformation of an
  element `k` of `SU(2)` is the rotation `SU2.toSO3 k` of `S²`, by Tau Ceti's
  `Matrix.specialUnitaryGroup.sphereCoords_toPSL_smul`.
* `SymplecticGeometry.map_rotationSubgroup_diffCongr`: so conjugation maps `rotationSubgroup` onto
  the image of `SO(3)` under `TauCeti.specialOrthogonalToDiffSphere 2 ∞`, since `SU2.toSO3` is
  surjective (`TauCeti.SU2.toSO3_surjective`); and that image lies in `roundDiffPlus`
  (`SymplecticGeometry.range_specialOrthogonalToDiffSphere_le_roundDiffPlus`, a case of
  `TauCeti.range_specialOrthogonalToDiffSphere_le`).

## The deformation onto the rotations

* `SymplecticGeometry.diffPlusPolarHomotopy`: the deformation of `Diff⁺(S²)` onto the rotations
  of the Riemann sphere. At time `t` it sends `φ` to `m_t(φ σ(φ^* i)⁻¹) σ(J_t)`, where `m` is the
  polar homotopy `SymplecticGeometry.mobiusPolarHomotopy` of the Möbius group and `J_t` the Cayley
  path from `i` to `φ^* i` at time `1 - t`
  (`SymplecticGeometry.coe_diffPlusPolarHomotopy_apply`). Its end map is
  `SymplecticGeometry.diffPlusPolarRetraction`, `φ ↦ m₁(φ σ(φ^* i)⁻¹)`. It is continuous because,
  through the trivialization `Φ = SymplecticGeometry.diffPlusTrivialization` for the frame system
  of the trivializations of the endomorphism bundle of `TS²` at the points of the sphere, it is
  `(t, φ) ↦ Φ⁻¹ (c_t (Φ φ).1, m_t (Φ φ).2)`, with `c` the contraction
  `SymplecticGeometry.complexStructureContraction`. It fixes the rotations, since `Φ g = (i, g)`
  for a Möbius transformation `g`, and ends in them, since `σ(i) = 1`
  (`SymplecticGeometry.uniformizingDiffeomorph_ofComplexManifold`).
* `SymplecticGeometry.roundDiffPlusPolarHomotopy`: the same deformation, carried to the round
  sphere by the isomorphism of topological groups `SymplecticGeometry.diffPlusEquivRoundDiffPlus`,
  which restricts Tau Ceti's `Diffeomorph.diffCongrContinuousMulEquiv` by
  `ContinuousMulEquiv.subgroupMap`.
* `SymplecticGeometry.exists_homotopyRel_specialOrthogonal_roundDiffPlus`: Smale's theorem.
* `SymplecticGeometry.specialOrthogonalHomotopyEquivRoundDiffPlus`: the inclusion
  `SymplecticGeometry.specialOrthogonalToRoundDiffPlus` of `SO(3)` in `roundDiffPlus` is a homotopy
  equivalence, by Tau Ceti's `ContinuousMap.HomotopyEquiv.ofDeformationRetraction`. Its homotopy
  inverse is the retraction, read in `SO(3)` through the embedding
  `TauCeti.isEmbedding_specialOrthogonalToDiffSphere`.
* `SymplecticGeometry.pathConnectedSpace_roundDiffPlus` and
  `SymplecticGeometry.roundDiffPlusFundamentalGroupMulEquiv`: `roundDiffPlus` is path connected,
  and its fundamental group at the identity is `ℤ/2ℤ`, from Tau Ceti's
  `TauCeti.Matrix.instPathConnectedSpaceSpecialOrthogonalGroup`,
  `ContinuousMap.HomotopyEquiv.pathConnectedSpace`,
  `ContinuousMap.HomotopyEquiv.fundamentalGroupMulEquiv` and
  `TauCeti.specialOrthogonalGroupFundamentalGroupMulEquiv`.

## References

* [S. Smale, *Diffeomorphisms of the 2-sphere*][Smale1959], Theorems A and 6 (the statement).
* [C. J. Earle, J. Eells, *The diffeomorphism group of a compact Riemann
  surface*][EarleEells1967], Theorem 1 (a) (the route through complex structures).
-/

public section

open Metric Matrix
open scoped Manifold ContDiff MatrixGroups TauCeti.ComplexManifold
open TauCeti

attribute [local instance] finrank_euclideanSpace_fin_succ_fact

namespace SymplecticGeometry

/-- The smooth diffeomorphism from the Riemann sphere onto the unit sphere of `ℝ³` given by
inverse stereographic projection from the north pole `(0, 0, 1)`, read on the plane `x₃ = 0`
through `z ↦ (Re z, -Im z, 0)`: Tau Ceti's analytic diffeomorphism
`OnePoint.diffeomorphSphere`, for these choices, as a `C^∞` diffeomorphism. -/
noncomputable def roundSphereDiffeomorph :
    OnePoint ℂ ≃ₘ^∞⟮𝓘(ℝ, ℂ), 𝓡 2⟯ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  (OnePoint.diffeomorphSphere (OnePoint.homeomorphSphere OnePoint.infty)
    OnePoint.sphereCoordsIsometry).ofLE le_top

/-- `roundSphereDiffeomorph` is the homeomorphism `OnePoint.homeomorphSphere` given by the round
sphere coordinates. -/
@[simp]
theorem roundSphereDiffeomorph_apply (x : OnePoint ℂ) :
    roundSphereDiffeomorph x = OnePoint.homeomorphSphere x := by
  rw [roundSphereDiffeomorph, Diffeomorph.coe_ofLE,
    OnePoint.diffeomorphSphere_sphereCoordsIsometry_apply]

/-- The inverse of `roundSphereDiffeomorph` is the inverse of `OnePoint.homeomorphSphere`. -/
@[simp]
theorem roundSphereDiffeomorph_symm_apply (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    roundSphereDiffeomorph.symm p = OnePoint.homeomorphSphere.symm p := by
  rw [roundSphereDiffeomorph, Diffeomorph.ofLE_symm, Diffeomorph.coe_ofLE,
    OnePoint.diffeomorphSphere_sphereCoordsIsometry_symm_apply]

/-- The values of `roundSphereDiffeomorph`, read in `ℝ³`, are the round sphere coordinates
`OnePoint.sphereCoords`. -/
theorem coe_roundSphereDiffeomorph_apply (x : OnePoint ℂ) :
    (roundSphereDiffeomorph x : EuclideanSpace ℝ (Fin 3)) =
      WithLp.toLp 2 (OnePoint.sphereCoords x) := by
  rw [roundSphereDiffeomorph_apply, OnePoint.coe_homeomorphSphere]

/-- The group `Diff⁺(S²)` of the round sphere: the smooth diffeomorphisms of the unit sphere of
`ℝ³` that preserve, at every point, the outward-normal orientation of the standard orientation of
`ℝ³`. -/
noncomputable def roundDiffPlus :
    Subgroup (TauCeti.Diff (𝓡 2) (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞) :=
  Diffeomorph.orientationPreservingSubgroup (by simp)
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation.sphereOrientation

theorem roundDiffPlus_def : roundDiffPlus = Diffeomorph.orientationPreservingSubgroup (by simp)
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation.sphereOrientation :=
  (rfl)

/-- A diffeomorphism of the unit sphere of `ℝ³` lies in `roundDiffPlus` exactly when it preserves
the outward-normal orientation at every point. -/
theorem mem_roundDiffPlus_iff
    {φ : TauCeti.Diff (𝓡 2) (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞} :
    φ ∈ roundDiffPlus ↔ ∀ x, Manifold.Orientation.IsOrientationPreservingAt
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation.sphereOrientation
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation.sphereOrientation φ x := by
  rw [roundDiffPlus_def, Diffeomorph.mem_orientationPreservingSubgroup_iff]

/-- **`Diff⁺` of the Riemann sphere is `Diff⁺` of the round sphere.** Conjugation by
`roundSphereDiffeomorph`, `φ ↦ σ ∘ φ ∘ σ⁻¹`, maps `diffPlus` onto `roundDiffPlus`. -/
theorem map_diffPlus_diffCongr :
    diffPlus.map (Diffeomorph.diffCongr roundSphereDiffeomorph).toMonoidHom = roundDiffPlus := by
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have h2 : 2 * Module.finrank ℂ ℂ = 2 := by simp
  have hι : Fintype.card (Fin 2) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) := by simp
  set oS := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation.sphereOrientation
  set oC := (complexManifoldOrientation ℂ (OnePoint ℂ)).reindex (finCongr h2)
  rw [diffPlus_def, ← Diffeomorph.orientationPreservingSubgroup_reindex hn _ (finCongr h2),
    Diffeomorph.map_orientationPreservingSubgroup_diffCongr hn oC roundSphereDiffeomorph hι,
    roundDiffPlus_def]
  -- On the connected Riemann sphere, `oC` is the orientation carried back from `oS`, or its
  -- opposite.
  have hι' : Fintype.card (Fin 2) = Module.finrank ℝ ℂ := by simp
  rcases oC.eq_or_eq_neg (oS.map roundSphereDiffeomorph.symm hn hι') with h | h <;>
    simp only [h, Manifold.Orientation.map_neg, Manifold.Orientation.map_map_symm,
      Diffeomorph.orientationPreservingSubgroup_neg, oS]

/-- **Rotations of the Riemann sphere are rotations of the round sphere.** Conjugation by
`roundSphereDiffeomorph` sends the Möbius transformation of the class of `k ∈ SU(2)` to the
restriction to the unit sphere of the rotation `SU2.toSO3 k` of `ℝ³`. -/
theorem diffCongr_mobiusHom_toPSL (k : specialUnitaryGroup (Fin 2) ℂ) :
    Diffeomorph.diffCongr roundSphereDiffeomorph (mobiusHom (specialUnitaryGroup.toPSL k)) =
      specialOrthogonalToDiffSphere 2 ∞ (SU2.toSO3 k) := by
  ext p : 2
  rw [Diffeomorph.diffCongr_apply_apply, roundSphereDiffeomorph_symm_apply, mobiusHom_apply,
    coe_roundSphereDiffeomorph_apply, specialUnitaryGroup.sphereCoords_toPSL_smul,
    specialOrthogonalToDiffSphere_apply, orthogonalToDiffSphere_apply,
    LinearIsometryEquiv.unitSphereDiffHom_apply,
    LinearIsometryEquiv.coe_unitSphereDiffeomorph_apply,
    UnitaryGroup.toLinearIsometryEquiv_apply]
  -- The point `p` has round sphere coordinates those of its preimage.
  have hp : (p : EuclideanSpace ℝ (Fin 3)) =
      WithLp.toLp 2 (OnePoint.sphereCoords (OnePoint.homeomorphSphere.symm p)) := by
    rw [← OnePoint.coe_homeomorphSphere, Homeomorph.apply_symm_apply]
  rw [hp, WithLp.ofLp_toLp, specialOrthogonalGroup.coe_toOrthogonalGroup]

/-- **The rotations of the round sphere.** Conjugation by `roundSphereDiffeomorph` maps the
rotations of the Riemann sphere onto the restrictions to the unit sphere of the rotations
`SO(3)` of `ℝ³`. -/
theorem map_rotationSubgroup_diffCongr :
    rotationSubgroup.map (Diffeomorph.diffCongr roundSphereDiffeomorph).toMonoidHom =
      (specialOrthogonalToDiffSphere 2 ∞).range := by
  have h : ((Diffeomorph.diffCongr roundSphereDiffeomorph).toMonoidHom.comp mobiusHom).comp
      (specialUnitaryGroup.toPSL : specialUnitaryGroup (Fin 2) ℂ →* PSL(2, ℂ)) =
      (specialOrthogonalToDiffSphere 2 ∞).comp SU2.toSO3 :=
    MonoidHom.ext diffCongr_mobiusHom_toPSL
  rw [rotationSubgroup_def, Subgroup.map_map, MonoidHom.map_range, h, MonoidHom.range_comp,
    MonoidHom.range_eq_top.2 SU2.toSO3_surjective, ← MonoidHom.range_eq_map]

/-- The rotations `SO(3)` of `ℝ³` restrict to orientation-preserving diffeomorphisms of the unit
sphere. -/
theorem range_specialOrthogonalToDiffSphere_le_roundDiffPlus :
    (specialOrthogonalToDiffSphere 2 ∞).range ≤ roundDiffPlus :=
  range_specialOrthogonalToDiffSphere_le _ _

/-! ### The deformation of `Diff⁺` of the Riemann sphere onto the rotations -/

section DiffPlus

open scoped TauCeti.DiffeomorphWeakWhitney

/-- The trivializations of the endomorphism bundle of `TS²` at the points of the Riemann sphere, a
covering frame system for the `C^∞` topology on almost complex structures. -/
private noncomputable abbrev frameAt (x : OnePoint ℂ) :=
  trivializationAt (ℂ →L[ℝ] ℂ)
    (fun x : OnePoint ℂ ↦ TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) x) x

/-- The second component of `diffPlusTrivialization`, as an element of `mobiusSubgroup`. -/
private theorem diffPlusTrivialization_apply_snd (φ : diffPlus) :
    let _ := SmoothAlmostComplexStructure.frameTopology frameAt (frameAt · |>.baseSetOpens)
      fun x ↦ (frameAt x).coe_baseSetOpens.subset
    (diffPlusTrivialization frameAt (frameAt · |>.baseSetOpens)
      (fun x ↦ (frameAt x).coe_baseSetOpens.subset)
      (FiberBundle.exists_mem_baseSetOpens_trivializationAt _ _) φ).2 =
      ⟨φ * (uniformizingDiffeomorph (complexStructureMap φ))⁻¹,
        mul_inv_uniformizingDiffeomorph_mem_mobiusSubgroup φ⟩ :=
  Subtype.ext (coe_diffPlusTrivialization_apply_snd _ _ _ _ φ)

/-- The retraction of `Diff⁺(S²)` onto the rotations: `φ ↦ m₁(φ σ(φ^* i)⁻¹)`, where `m₁` is the
polar retraction of the Möbius group onto the rotations. It is continuous for the weak Whitney
topology. -/
noncomputable def diffPlusPolarRetraction : C(diffPlus, diffPlus) where
  toFun φ := Subgroup.inclusion mobiusSubgroup_le_diffPlus
    (mobiusPolarRetraction ⟨φ * (uniformizingDiffeomorph (complexStructureMap φ))⁻¹,
      mul_inv_uniformizingDiffeomorph_mem_mobiusSubgroup φ⟩)
  continuous_toFun := by
    let _ := SmoothAlmostComplexStructure.frameTopology frameAt (frameAt · |>.baseSetOpens)
      fun x ↦ (frameAt x).coe_baseSetOpens.subset
    refine ((continuous_inclusion mobiusSubgroup_le_diffPlus).comp
      (mobiusPolarRetraction.continuous.comp (continuous_snd.comp
        (diffPlusTrivialization frameAt (frameAt · |>.baseSetOpens)
          (fun x ↦ (frameAt x).coe_baseSetOpens.subset)
          (FiberBundle.exists_mem_baseSetOpens_trivializationAt _ _)).continuous))).congr
      fun φ ↦ ?_
    exact congrArg (fun g ↦ Subgroup.inclusion mobiusSubgroup_le_diffPlus (mobiusPolarRetraction g))
      (diffPlusTrivialization_apply_snd φ)

/-- The retraction of `Diff⁺(S²)` sends `φ` to the polar retraction of the Möbius
transformation `φ σ(φ^* i)⁻¹`. -/
@[simp]
theorem coe_diffPlusPolarRetraction_apply (φ : diffPlus) :
    (diffPlusPolarRetraction φ : TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ∞) =
      mobiusPolarRetraction ⟨φ * (uniformizingDiffeomorph (complexStructureMap φ))⁻¹,
        mul_inv_uniformizingDiffeomorph_mem_mobiusSubgroup φ⟩ :=
  (rfl)

/-- The retraction of `Diff⁺(S²)` takes its values in the rotations. -/
theorem coe_diffPlusPolarRetraction_mem_rotationSubgroup (φ : diffPlus) :
    (diffPlusPolarRetraction φ : TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ∞) ∈ rotationSubgroup :=
  coe_mobiusPolarRetraction_mem_rotationSubgroup _

/-- The values of the deformation of `Diff⁺(S²)`: at time `t`, `φ` goes to `m_t(φ σ(φ^* i)⁻¹)`
composed with the uniformizing diffeomorphism of the Cayley path from `i` to `φ^* i` at time
`1 - t`. -/
private noncomputable def diffPlusPolarHomotopyFun (x : unitInterval × diffPlus) : diffPlus :=
  Subgroup.inclusion mobiusSubgroup_le_diffPlus (mobiusPolarHomotopy (x.1,
      ⟨x.2 * (uniformizingDiffeomorph (complexStructureMap x.2))⁻¹,
        mul_inv_uniformizingDiffeomorph_mem_mobiusSubgroup x.2⟩)) *
    uniformizingDiffeomorph ⟨OnePoint.compatible_fubiniStudyForm.cayleyPath
      (complexStructureMap x.2).property (1 - x.1),
      OnePoint.compatible_fubiniStudyForm.tames_cayleyPath _ _⟩

/-- Through the trivialization `Φ`, the deformation of `Diff⁺(S²)` is
`(t, φ) ↦ Φ⁻¹ (c_t (Φ φ).1, m_t (Φ φ).2)`. -/
private theorem diffPlusPolarHomotopyFun_eq (x : unitInterval × diffPlus) :
    let _ := SmoothAlmostComplexStructure.frameTopology frameAt (frameAt · |>.baseSetOpens)
      fun x ↦ (frameAt x).coe_baseSetOpens.subset
    diffPlusPolarHomotopyFun x =
      (diffPlusTrivialization frameAt (frameAt · |>.baseSetOpens)
        (fun x ↦ (frameAt x).coe_baseSetOpens.subset)
        (FiberBundle.exists_mem_baseSetOpens_trivializationAt _ _)).symm
        (complexStructureContraction frameAt (frameAt · |>.baseSetOpens)
          (fun x ↦ (frameAt x).coe_baseSetOpens.subset)
          (FiberBundle.exists_mem_baseSetOpens_trivializationAt _ _)
          (x.1, (diffPlusTrivialization frameAt (frameAt · |>.baseSetOpens)
            (fun x ↦ (frameAt x).coe_baseSetOpens.subset)
            (FiberBundle.exists_mem_baseSetOpens_trivializationAt _ _) x.2).1),
        mobiusPolarHomotopy (x.1, (diffPlusTrivialization frameAt (frameAt · |>.baseSetOpens)
          (fun x ↦ (frameAt x).coe_baseSetOpens.subset)
          (FiberBundle.exists_mem_baseSetOpens_trivializationAt _ _) x.2).2)) := by
  let _ := SmoothAlmostComplexStructure.frameTopology frameAt (frameAt · |>.baseSetOpens)
    fun x ↦ (frameAt x).coe_baseSetOpens.subset
  have hc : complexStructureContraction frameAt (frameAt · |>.baseSetOpens)
      (fun x ↦ (frameAt x).coe_baseSetOpens.subset)
      (FiberBundle.exists_mem_baseSetOpens_trivializationAt _ _) (x.1, complexStructureMap x.2) =
        ⟨OnePoint.compatible_fubiniStudyForm.cayleyPath (complexStructureMap x.2).property
          (1 - x.1), OnePoint.compatible_fubiniStudyForm.tames_cayleyPath _ _⟩ :=
    Subtype.ext (complexStructureContraction_apply _ _ _ _ _ _)
  refine Subtype.ext ?_
  rw [coe_diffPlusTrivialization_symm_apply, diffPlusTrivialization_apply_fst,
    diffPlusTrivialization_apply_snd, hc, diffPlusPolarHomotopyFun, Subgroup.coe_mul,
    Subgroup.coe_inclusion]

/-- **`Diff⁺` of the Riemann sphere deformation retracts onto the rotations.** At time `t`, the
homotopy sends `φ` to `m_t(φ σ(φ^* i)⁻¹) σ(J_t)`, where `m` is the polar homotopy of the Möbius
group and `J_t` the Cayley path from `i` to `φ^* i` at time `1 - t`. It runs from the identity of
`Diff⁺(S²)` to `diffPlusPolarRetraction`, and fixes every rotation at all times. -/
noncomputable def diffPlusPolarHomotopy :
    (ContinuousMap.id diffPlus).HomotopyRel diffPlusPolarRetraction
      {φ | (φ : TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ∞) ∈ rotationSubgroup} where
  toFun := diffPlusPolarHomotopyFun
  continuous_toFun := by
    let _ := SmoothAlmostComplexStructure.frameTopology frameAt (frameAt · |>.baseSetOpens)
      fun x ↦ (frameAt x).coe_baseSetOpens.subset
    rw [show diffPlusPolarHomotopyFun = _ from funext diffPlusPolarHomotopyFun_eq]
    fun_prop
  map_zero_left φ := by
    rw [diffPlusPolarHomotopyFun_eq]
    simp only [ContinuousMap.HomotopyWith.apply_zero, ContinuousMap.id_apply, Prod.mk.eta,
      Homeomorph.symm_apply_apply]
  map_one_left φ := by
    refine (diffPlusPolarHomotopyFun_eq _).trans (Subtype.ext ?_)
    simp only [ContinuousMap.HomotopyWith.apply_one, ContinuousMap.const_apply,
      coe_diffPlusTrivialization_symm_apply, uniformizingDiffeomorph_ofComplexManifold,
      Subgroup.coe_one, mul_one, coe_diffPlusPolarRetraction_apply,
      diffPlusTrivialization_apply_snd]
  prop' t φ hφ := by
    let _ := SmoothAlmostComplexStructure.frameTopology frameAt (frameAt · |>.baseSetOpens)
      fun x ↦ (frameAt x).coe_baseSetOpens.subset
    obtain ⟨g, rfl⟩ : ∃ g : mobiusSubgroup,
        Subgroup.inclusion mobiusSubgroup_le_diffPlus g = φ :=
      ⟨⟨φ, rotationSubgroup_le_mobiusSubgroup hφ⟩, rfl⟩
    refine (diffPlusPolarHomotopyFun_eq (t, _)).trans ?_
    rw [diffPlusTrivialization_inclusion, ContinuousMap.id_apply,
      (complexStructureContraction frameAt (frameAt · |>.baseSetOpens)
        (fun x ↦ (frameAt x).coe_baseSetOpens.subset)
        (FiberBundle.exists_mem_baseSetOpens_trivializationAt _ _)).eq_fst t rfl,
      mobiusPolarHomotopy.eq_fst t hφ]
    exact (Homeomorph.symm_apply_eq _).2 (diffPlusTrivialization_inclusion frameAt
      (frameAt · |>.baseSetOpens) (fun x ↦ (frameAt x).coe_baseSetOpens.subset)
      (FiberBundle.exists_mem_baseSetOpens_trivializationAt _ _) g).symm

/-- At time `t`, the deformation of `Diff⁺(S²)` sends `φ` to `m_t(φ σ(φ^* i)⁻¹) σ(J_t)`, where `m`
is the polar homotopy of the Möbius group and `J_t` the Cayley path from `i` to `φ^* i` at time
`1 - t`. -/
@[simp]
theorem coe_diffPlusPolarHomotopy_apply (t : unitInterval) (φ : diffPlus) :
    (diffPlusPolarHomotopy (t, φ) : TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ∞) =
      mobiusPolarHomotopy (t, ⟨φ * (uniformizingDiffeomorph (complexStructureMap φ))⁻¹,
        mul_inv_uniformizingDiffeomorph_mem_mobiusSubgroup φ⟩) *
      uniformizingDiffeomorph ⟨OnePoint.compatible_fubiniStudyForm.cayleyPath
        (complexStructureMap φ).property (1 - t),
        OnePoint.compatible_fubiniStudyForm.tames_cayleyPath _ _⟩ :=
  (rfl)

end DiffPlus

/-! ### Smale's theorem on the round sphere -/

section Round

open scoped TauCeti.DiffeomorphWeakWhitney

/-- Conjugation by `roundSphereDiffeomorph`, as an isomorphism of topological groups from
`diffPlus` onto `roundDiffPlus`. -/
noncomputable def diffPlusEquivRoundDiffPlus : diffPlus ≃ₜ* roundDiffPlus :=
  ((Diffeomorph.diffCongrContinuousMulEquiv roundSphereDiffeomorph).subgroupMap diffPlus).trans
    { toMulEquiv := MulEquiv.subgroupCongr <| by
        -- The underlying homomorphism of `diffCongrContinuousMulEquiv` is `diffCongr`.
        rw [← map_diffPlus_diffCongr]
        exact congrArg (diffPlus.map ·)
          (MonoidHom.ext (Diffeomorph.diffCongrContinuousMulEquiv_apply _))
      continuous_toFun := continuous_subtypeVal.subtype_mk _
      continuous_invFun := continuous_subtypeVal.subtype_mk _ }

/-- `diffPlusEquivRoundDiffPlus` is conjugation by `roundSphereDiffeomorph`. -/
@[simp]
theorem coe_diffPlusEquivRoundDiffPlus_apply (φ : diffPlus) :
    (diffPlusEquivRoundDiffPlus φ :
        TauCeti.Diff (𝓡 2) (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞) =
      Diffeomorph.diffCongr roundSphereDiffeomorph φ := by
  rw [diffPlusEquivRoundDiffPlus, ContinuousMulEquiv.trans_apply]
  -- The second factor, built from `MulEquiv.subgroupCongr`, keeps the underlying diffeomorphism.
  exact (ContinuousMulEquiv.coe_subgroupMap_apply _ _ φ).trans
    (Diffeomorph.diffCongrContinuousMulEquiv_apply _ _)

/-- The inverse of `diffPlusEquivRoundDiffPlus` is conjugation by the inverse of
`roundSphereDiffeomorph`. -/
@[simp]
theorem coe_diffPlusEquivRoundDiffPlus_symm_apply (φ : roundDiffPlus) :
    (diffPlusEquivRoundDiffPlus.symm φ : TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ∞) =
      (Diffeomorph.diffCongr roundSphereDiffeomorph).symm φ := by
  rw [MulEquiv.eq_symm_apply, ← coe_diffPlusEquivRoundDiffPlus_apply,
    ContinuousMulEquiv.apply_symm_apply]

/-- The retraction of `roundDiffPlus` onto the rotations `SO(3)`: the retraction
`diffPlusPolarRetraction` of `diffPlus`, carried to the round sphere by
`diffPlusEquivRoundDiffPlus`. -/
noncomputable def roundDiffPlusPolarRetraction : C(roundDiffPlus, roundDiffPlus) :=
  (diffPlusEquivRoundDiffPlus : C(diffPlus, roundDiffPlus)).comp
    (diffPlusPolarRetraction.comp (diffPlusEquivRoundDiffPlus.symm : C(roundDiffPlus, diffPlus)))

/-- The retraction of `roundDiffPlus` is the conjugate, by `roundSphereDiffeomorph`, of the
retraction of `diffPlus` applied to the conjugate of `φ` on the Riemann sphere. -/
@[simp]
theorem coe_roundDiffPlusPolarRetraction_apply (φ : roundDiffPlus) :
    (roundDiffPlusPolarRetraction φ :
      TauCeti.Diff (𝓡 2) (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞) =
      Diffeomorph.diffCongr roundSphereDiffeomorph
        (diffPlusPolarRetraction (diffPlusEquivRoundDiffPlus.symm φ)) := by
  rw [roundDiffPlusPolarRetraction, ContinuousMap.comp_apply, ContinuousMap.comp_apply,
    ContinuousMap.coe_ofClass, ContinuousMap.coe_ofClass, coe_diffPlusEquivRoundDiffPlus_apply]

/-- The retraction of `roundDiffPlus` takes its values in the rotations `SO(3)`. -/
theorem coe_roundDiffPlusPolarRetraction_mem_range (φ : roundDiffPlus) :
    (roundDiffPlusPolarRetraction φ :
      TauCeti.Diff (𝓡 2) (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞) ∈
        (specialOrthogonalToDiffSphere 2 ∞).range := by
  rw [← map_rotationSubgroup_diffCongr, coe_roundDiffPlusPolarRetraction_apply]
  exact Subgroup.mem_map_of_mem _ (coe_diffPlusPolarRetraction_mem_rotationSubgroup _)

/-- An element of `roundDiffPlus` is a rotation of `SO(3)` exactly when its conjugate on the
Riemann sphere is a rotation. -/
theorem coe_mem_range_specialOrthogonalToDiffSphere_iff_symm_mem_rotationSubgroup
    (φ : roundDiffPlus) :
    (φ : TauCeti.Diff (𝓡 2) (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞) ∈
        (specialOrthogonalToDiffSphere 2 ∞).range ↔
      (diffPlusEquivRoundDiffPlus.symm φ : TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ∞) ∈
        rotationSubgroup := by
  rw [← map_rotationSubgroup_diffCongr, Subgroup.mem_map_equiv,
    coe_diffPlusEquivRoundDiffPlus_symm_apply]

/-- **`Diff⁺` of the round sphere deformation retracts onto `SO(3)`.** The deformation
`diffPlusPolarHomotopy` of `diffPlus`, carried to the round sphere by
`diffPlusEquivRoundDiffPlus`: a homotopy from the identity of `roundDiffPlus` to
`roundDiffPlusPolarRetraction` that fixes every rotation of `SO(3)` at all times. -/
noncomputable def roundDiffPlusPolarHomotopy :
    (ContinuousMap.id roundDiffPlus).HomotopyRel roundDiffPlusPolarRetraction
      {φ | (φ : TauCeti.Diff (𝓡 2) (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞) ∈
        (specialOrthogonalToDiffSphere 2 ∞).range} :=
  (((diffPlusPolarHomotopy.precomp
      (diffPlusEquivRoundDiffPlus.symm : C(roundDiffPlus, diffPlus))).compContinuousMap
        (diffPlusEquivRoundDiffPlus : C(diffPlus, roundDiffPlus))).mono
    fun φ hφ ↦
      (coe_mem_range_specialOrthogonalToDiffSphere_iff_symm_mem_rotationSubgroup φ).1 hφ).cast
    (ContinuousMap.ext fun φ ↦ diffPlusEquivRoundDiffPlus.apply_symm_apply φ)
    (by rw [roundDiffPlusPolarRetraction])

/-- **Smale's theorem.** Give the smooth diffeomorphisms of the unit sphere `S²` of `ℝ³` that
preserve its orientation, `Diff⁺(S²) = roundDiffPlus`, the weak Whitney `C^∞` topology. Then
`Diff⁺(S²)` deformation retracts, in the strong sense, onto its subgroup of rotations `SO(3)`
(restricted to `S²`): there are a continuous map
`r : Diff⁺(S²) → Diff⁺(S²)` with values in `SO(3)` and a homotopy from the identity to `r` that
fixes every element of `SO(3)` at all times.

Milestone: *Smale's theorem on the diffeomorphism group of the 2-sphere*. -/
theorem exists_homotopyRel_specialOrthogonal_roundDiffPlus :
    ∃ r : C(roundDiffPlus, roundDiffPlus),
      (∀ φ, (r φ : TauCeti.Diff (𝓡 2) (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞) ∈
        (specialOrthogonalToDiffSphere 2 ∞).range) ∧
      Nonempty ((ContinuousMap.id roundDiffPlus).HomotopyRel r
        {φ | (φ : TauCeti.Diff (𝓡 2) (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞) ∈
          (specialOrthogonalToDiffSphere 2 ∞).range}) :=
  ⟨_, coe_roundDiffPlusPolarRetraction_mem_range, ⟨roundDiffPlusPolarHomotopy⟩⟩

/-- The inclusion of `SO(3)` in `roundDiffPlus`, as a continuous group homomorphism. -/
noncomputable def specialOrthogonalToRoundDiffPlus :
    specialOrthogonalGroup (Fin 3) ℝ →ₜ* roundDiffPlus where
  toMonoidHom := (specialOrthogonalToDiffSphere 2 ∞).codRestrict roundDiffPlus fun k ↦
    range_specialOrthogonalToDiffSphere_le_roundDiffPlus ⟨k, rfl⟩
  continuous_toFun := (continuous_specialOrthogonalToDiffSphere 2 ∞).subtype_mk _

/-- The inclusion of `SO(3)` in `roundDiffPlus` sends a rotation to its restriction to the
unit sphere. -/
@[simp]
theorem coe_specialOrthogonalToRoundDiffPlus_apply (k : specialOrthogonalGroup (Fin 3) ℝ) :
    (specialOrthogonalToRoundDiffPlus k :
      TauCeti.Diff (𝓡 2) (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞) =
        specialOrthogonalToDiffSphere 2 ∞ k :=
  (rfl)

/-- The retraction of `roundDiffPlus` onto `SO(3)`, read in `SO(3)`. -/
noncomputable def roundDiffPlusToSpecialOrthogonal :
    C(roundDiffPlus, specialOrthogonalGroup (Fin 3) ℝ) where
  toFun φ := (isEmbedding_specialOrthogonalToDiffSphere 2 ∞).toHomeomorph.symm
    ⟨roundDiffPlusPolarRetraction φ, coe_roundDiffPlusPolarRetraction_mem_range φ⟩
  continuous_toFun :=
    (isEmbedding_specialOrthogonalToDiffSphere 2 ∞).toHomeomorph.symm.continuous.comp
      ((continuous_subtypeVal.comp roundDiffPlusPolarRetraction.continuous).subtype_mk _)

/-- The retraction of `roundDiffPlus`, read in `SO(3)` and included back, is
`roundDiffPlusPolarRetraction`. -/
theorem specialOrthogonalToRoundDiffPlus_roundDiffPlusToSpecialOrthogonal (φ : roundDiffPlus) :
    specialOrthogonalToRoundDiffPlus (roundDiffPlusToSpecialOrthogonal φ) =
      roundDiffPlusPolarRetraction φ := by
  refine Subtype.ext ?_
  rw [coe_specialOrthogonalToRoundDiffPlus_apply]
  exact congrArg Subtype.val
    ((isEmbedding_specialOrthogonalToDiffSphere 2 ∞).toHomeomorph.apply_symm_apply _)

/-- The retraction of `roundDiffPlus`, read in `SO(3)`, is a left inverse of the inclusion of
`SO(3)`. -/
theorem roundDiffPlusToSpecialOrthogonal_specialOrthogonalToRoundDiffPlus
    (k : specialOrthogonalGroup (Fin 3) ℝ) :
    roundDiffPlusToSpecialOrthogonal (specialOrthogonalToRoundDiffPlus k) = k := by
  have h : roundDiffPlusPolarRetraction (specialOrthogonalToRoundDiffPlus k) =
      specialOrthogonalToRoundDiffPlus k :=
    (roundDiffPlusPolarHomotopy.fst_eq_snd (x := specialOrthogonalToRoundDiffPlus k)
      ⟨k, rfl⟩).symm
  simp only [roundDiffPlusToSpecialOrthogonal, ContinuousMap.coe_mk, h,
    coe_specialOrthogonalToRoundDiffPlus_apply]
  exact (isEmbedding_specialOrthogonalToDiffSphere 2 ∞).toHomeomorph_symm_apply k

/-- **`SO(3)` is homotopy equivalent to `Diff⁺(S²)`.** The inclusion of the rotations `SO(3)` in
the orientation-preserving diffeomorphisms of the unit sphere of `ℝ³` is a homotopy
equivalence. -/
noncomputable def specialOrthogonalHomotopyEquivRoundDiffPlus :
    ContinuousMap.HomotopyEquiv (specialOrthogonalGroup (Fin 3) ℝ) roundDiffPlus :=
  .ofDeformationRetraction specialOrthogonalToRoundDiffPlus roundDiffPlusToSpecialOrthogonal
    roundDiffPlusToSpecialOrthogonal_specialOrthogonalToRoundDiffPlus <| by
      rw [show (specialOrthogonalToRoundDiffPlus :
          C(specialOrthogonalGroup (Fin 3) ℝ, roundDiffPlus)).comp
            roundDiffPlusToSpecialOrthogonal = roundDiffPlusPolarRetraction from
          ContinuousMap.ext specialOrthogonalToRoundDiffPlus_roundDiffPlusToSpecialOrthogonal]
      exact ⟨roundDiffPlusPolarHomotopy.toHomotopy.symm⟩

/-- The map of `specialOrthogonalHomotopyEquivRoundDiffPlus` is the inclusion of `SO(3)`. -/
theorem specialOrthogonalHomotopyEquivRoundDiffPlus_toFun :
    specialOrthogonalHomotopyEquivRoundDiffPlus.toFun = specialOrthogonalToRoundDiffPlus :=
  ContinuousMap.HomotopyEquiv.ofDeformationRetraction_toFun _ _ _ _

/-- `Diff⁺(S²)` of the round sphere is path connected: it is homotopy equivalent to the path
connected group `SO(3)`. -/
instance pathConnectedSpace_roundDiffPlus : PathConnectedSpace roundDiffPlus :=
  specialOrthogonalHomotopyEquivRoundDiffPlus.pathConnectedSpace

/-- **The fundamental group of `Diff⁺(S²)`.** At the identity, the fundamental group of
`roundDiffPlus`, the smooth diffeomorphisms of the unit sphere of `ℝ³` that preserve its
orientation, is `ℤ/2ℤ`, like that of `SO(3)`. -/
noncomputable def roundDiffPlusFundamentalGroupMulEquiv :
    FundamentalGroup roundDiffPlus 1 ≃* Multiplicative (ZMod 2) :=
  ((FundamentalGroup.homeomorphMulEquivOfEq (Homeomorph.refl _)
      (specialOrthogonalHomotopyEquivRoundDiffPlus_toFun ▸
        (map_one specialOrthogonalToRoundDiffPlus).symm)).trans
    (specialOrthogonalHomotopyEquivRoundDiffPlus.fundamentalGroupMulEquiv 1).symm).trans
    (specialOrthogonalGroupFundamentalGroupMulEquiv 3 le_rfl)

end Round

end SymplecticGeometry

end
