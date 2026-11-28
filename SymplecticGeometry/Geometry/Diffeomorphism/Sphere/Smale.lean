/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Congr
public import TauCeti.Geometry.Diffeomorphism.Sphere
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Sphere
public import SymplecticGeometry.Geometry.Diffeomorphism.Sphere.Trivialization
import SymplecticGeometry.Geometry.Diffeomorphism.Orientation
import SymplecticGeometry.Geometry.Manifold.Diffeomorph.Basic

/-!
# Diffeomorphisms of the round 2-sphere

The group `Diff⁺(S²)` of `ComplexStructure.lean` is a group of diffeomorphisms of the Riemann
sphere `OnePoint ℂ`. This file carries it, and its rotations, to the unit sphere `S²` of
`EuclideanSpace ℝ (Fin 3)`, by conjugation along a fixed diffeomorphism.

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
  the image of `SO(3)` under `TauCeti.orthogonalToDiffSphere 2 ∞`, since `SU2.toSO3` is surjective
  (`TauCeti.SU2.toSO3_surjective`); and that image lies in `roundDiffPlus`
  (`SymplecticGeometry.range_specialOrthogonalGroup_le_roundDiffPlus`, a case of
  `TauCeti.range_orthogonalToDiffSphere_specialOrthogonalGroup_le`).

## References

* [S. Smale, *Diffeomorphisms of the 2-sphere*][Smale1959] (the round sphere and its rotations).
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
      orthogonalToDiffSphere 2 ∞
        (Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup (SU2.toSO3 k)) := by
  ext p : 2
  rw [Diffeomorph.diffCongr_apply_apply, roundSphereDiffeomorph_symm_apply, mobiusHom_apply,
    coe_roundSphereDiffeomorph_apply, specialUnitaryGroup.sphereCoords_toPSL_smul,
    orthogonalToDiffSphere_apply, LinearIsometryEquiv.unitSphereDiffHom_apply,
    LinearIsometryEquiv.coe_unitSphereDiffeomorph_apply,
    UnitaryGroup.toLinearIsometryEquiv_apply]
  -- The point `p` has round sphere coordinates those of its preimage.
  have hp : (p : EuclideanSpace ℝ (Fin 3)) =
      WithLp.toLp 2 (OnePoint.sphereCoords (OnePoint.homeomorphSphere.symm p)) := by
    rw [← OnePoint.coe_homeomorphSphere, Homeomorph.apply_symm_apply]
  rw [hp, WithLp.ofLp_toLp, Submonoid.coe_inclusion]

/-- **The rotations of the round sphere.** Conjugation by `roundSphereDiffeomorph` maps the
rotations of the Riemann sphere onto the restrictions to the unit sphere of the rotations
`SO(3)` of `ℝ³`. -/
theorem map_rotationSubgroup_diffCongr :
    rotationSubgroup.map (Diffeomorph.diffCongr roundSphereDiffeomorph).toMonoidHom =
      ((orthogonalToDiffSphere 2 ∞).comp
        (Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup)).range := by
  have h : ((Diffeomorph.diffCongr roundSphereDiffeomorph).toMonoidHom.comp mobiusHom).comp
      (specialUnitaryGroup.toPSL : specialUnitaryGroup (Fin 2) ℂ →* PSL(2, ℂ)) =
      ((orthogonalToDiffSphere 2 ∞).comp
        (Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup)).comp SU2.toSO3 :=
    MonoidHom.ext diffCongr_mobiusHom_toPSL
  rw [rotationSubgroup_def, Subgroup.map_map, MonoidHom.map_range, h, MonoidHom.range_comp,
    MonoidHom.range_eq_top.2 SU2.toSO3_surjective, ← MonoidHom.range_eq_map]

/-- The rotations `SO(3)` of `ℝ³` restrict to orientation-preserving diffeomorphisms of the unit
sphere. -/
theorem range_specialOrthogonalGroup_le_roundDiffPlus :
    ((orthogonalToDiffSphere 2 ∞).comp
      (Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup)).range ≤ roundDiffPlus :=
  range_orthogonalToDiffSphere_specialOrthogonalGroup_le _ _

/-! ### The deformation of `Diff⁺` of the Riemann sphere onto the rotations -/

section DiffPlus

open scoped TauCeti.DiffeomorphWeakWhitney

variable {ι : Type*}
  (e : ι → Bundle.Trivialization (ℂ →L[ℝ] ℂ) (Bundle.TotalSpace.proj (F := ℂ →L[ℝ] ℂ)
    (E := fun x : OnePoint ℂ ↦ TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) x)))
  [∀ k, MemTrivializationAtlas (e k)] (U : ι → TopologicalSpace.Opens (OnePoint ℂ))
  (hU : ∀ k, (U k : Set (OnePoint ℂ)) ⊆ (e k).baseSet) (hcover : ∀ x, ∃ k, x ∈ U k)

/-- The retraction of `Diff⁺(S²)` onto the rotations: `φ ↦ m₁(φ σ(φ^* i)⁻¹)`, where `m₁` is the
polar retraction of the Möbius group onto the rotations. It is continuous for the weak Whitney
topology; the covering frame system only serves to prove that. -/
noncomputable def diffPlusPolarRetraction : C(diffPlus, diffPlus) :=
  letI := SmoothAlmostComplexStructure.frameTopology e U hU
  { toFun φ := Subgroup.inclusion mobiusSubgroup_le_diffPlus
      (mobiusPolarRetraction (diffPlusTrivialization e U hU hcover φ).2)
    continuous_toFun := (continuous_inclusion mobiusSubgroup_le_diffPlus).comp
      (mobiusPolarRetraction.continuous.comp
        (continuous_snd.comp (diffPlusTrivialization e U hU hcover).continuous)) }

/-- The retraction of `Diff⁺(S²)` sends `φ` to the polar retraction of the second component
`φ σ(φ^* i)⁻¹` of its image under the trivialization. -/
theorem coe_diffPlusPolarRetraction_apply (φ : diffPlus) :
    letI := SmoothAlmostComplexStructure.frameTopology e U hU
    (diffPlusPolarRetraction e U hU hcover φ : TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ∞) =
      mobiusPolarRetraction (diffPlusTrivialization e U hU hcover φ).2 :=
  (rfl)

/-- The retraction of `Diff⁺(S²)` takes its values in the rotations. -/
theorem coe_diffPlusPolarRetraction_mem_rotationSubgroup (φ : diffPlus) :
    (diffPlusPolarRetraction e U hU hcover φ : TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ∞) ∈
      rotationSubgroup :=
  coe_mobiusPolarRetraction_mem_rotationSubgroup _

/-- **`Diff⁺` of the Riemann sphere deformation retracts onto the rotations.** With `Φ` the
trivialization `Diff⁺(S²) ≃ₜ 𝒥 × mobiusSubgroup`, `c` the contraction of `𝒥` onto `i` and `m` the
polar homotopy of the Möbius group, the homotopy `(t, φ) ↦ Φ⁻¹ (c_t (Φ φ).1, m_t (Φ φ).2)` runs
from the identity of `Diff⁺(S²)` to `diffPlusPolarRetraction`, and fixes every rotation at all
times. -/
noncomputable def diffPlusPolarHomotopy :
    (ContinuousMap.id diffPlus).HomotopyRel (diffPlusPolarRetraction e U hU hcover)
      {φ | (φ : TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ∞) ∈ rotationSubgroup} :=
  letI := SmoothAlmostComplexStructure.frameTopology e U hU
  { toFun x := (diffPlusTrivialization e U hU hcover).symm
      (complexStructureContraction e U hU hcover
        (x.1, (diffPlusTrivialization e U hU hcover x.2).1),
        mobiusPolarHomotopy (x.1, (diffPlusTrivialization e U hU hcover x.2).2))
    continuous_toFun := by fun_prop
    map_zero_left φ := by
      simp only [ContinuousMap.HomotopyWith.apply_zero, ContinuousMap.id_apply, Prod.mk.eta,
        Homeomorph.symm_apply_apply]
    map_one_left φ := by
      refine Subtype.ext ?_
      simp only [ContinuousMap.HomotopyWith.apply_one, ContinuousMap.const_apply,
        coe_diffPlusTrivialization_symm_apply, uniformizingDiffeomorph_ofComplexManifold,
        Subgroup.coe_one, mul_one, coe_diffPlusPolarRetraction_apply]
    prop' t φ hφ := by
      obtain ⟨g, rfl⟩ : ∃ g : mobiusSubgroup,
          Subgroup.inclusion mobiusSubgroup_le_diffPlus g = φ :=
        ⟨⟨φ, rotationSubgroup_le_mobiusSubgroup hφ⟩, rfl⟩
      simp only [ContinuousMap.coe_mk, diffPlusTrivialization_inclusion, ContinuousMap.id_apply]
      rw [(complexStructureContraction e U hU hcover).eq_fst t rfl,
        mobiusPolarHomotopy.eq_fst t hφ]
      exact (Homeomorph.symm_apply_eq _).2 (diffPlusTrivialization_inclusion e U hU hcover g).symm }

/-- At time `t`, the deformation of `Diff⁺(S²)` sends `φ` to `Φ⁻¹ (c_t (φ^* i), m_t (Φ φ).2)`. -/
theorem diffPlusPolarHomotopy_apply (t : unitInterval) (φ : diffPlus) :
    letI := SmoothAlmostComplexStructure.frameTopology e U hU
    diffPlusPolarHomotopy e U hU hcover (t, φ) = (diffPlusTrivialization e U hU hcover).symm
      (complexStructureContraction e U hU hcover (t, complexStructureMap φ),
        mobiusPolarHomotopy (t, (diffPlusTrivialization e U hU hcover φ).2)) := by
  rw [← diffPlusTrivialization_apply_fst e U hU hcover]
  rfl

end DiffPlus

end SymplecticGeometry

end
