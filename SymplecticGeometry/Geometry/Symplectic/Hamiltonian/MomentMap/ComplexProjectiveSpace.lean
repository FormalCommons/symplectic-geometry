/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.ComplexProjectiveSpace
public import SymplecticGeometry.Geometry.Manifold.Projectivization.Hopf
public import SymplecticGeometry.Geometry.Lie.Subgroup.Unitary.Action
public import SymplecticGeometry.Geometry.Manifold.Instances.ComplexProjectiveSpace.Projectivization
public import SymplecticGeometry.Geometry.Manifold.Projectivization.Action
public import SymplecticGeometry.Geometry.Manifold.Projectivization.FubiniStudy.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Basic
import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.Basic
import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.Geometry.Manifold.Instances.ComplexProjectiveSpace.Hopf
import TauCeti.Geometry.Manifold.Instances.Sphere.SkewHermitian
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The unitary action on `ℙ ℂ (Fin (n + 1) → ℂ)`: generators and moment map

Tau Ceti's infinitesimal action `TauCeti.ComplexProjectiveSpace.unitaryAction n` of the unitary
Lie algebra `𝔲(n + 1)` on the sphere-quotient model `CPⁿ` is defined by the Hamiltonian vector
fields of the components of its moment map, and Tau Ceti computes it through the Hopf projection
`mk n` of the unit sphere: `X` generates at `[u]` the image of the tangent vector `X u` under the
differential of `mk n` (`TauCeti.ComplexProjectiveSpace.unitaryAction_apply_mk`).

This file reads those generators on the projectivization `ℙ ℂ (Fin (n + 1) → ℂ)` through the
library's diffeomorphism `TauCeti.ComplexProjectiveSpace.diffeomorphProjectivization n`: there
`X` generates at the line `[y]` through a nonzero vector `y` the image of `X y` under the
differential of the projection `Projectivization.mkNonzero ℂ n` at `y`. Informally this is the
derivative at `t = 0` of `t ↦ [exp(t X) y]`, the generator of the linear action of the unitary
group; the statement itself uses no group action.

The second half of the file uses this to transport Tau Ceti's moment map to a group-level moment
map of the matrix unitary Lie group `unitarySubgroup (GL (Fin (n + 1)) ℂ)`
(`TauCeti.Lie.matrixUnitaryLieGroup`), acting linearly on `ℙ ℂ (Fin (n + 1) → ℂ)`, for the
library's `SymplecticGeometry.fubiniStudyForm n`. Write `D = diffeomorphProjectivization n`, `τ`
for Tau Ceti's Fubini–Study form and `L = TauCeti.Lie.matrixUnitaryLieAlgebraEquiv` for the
identification of the Lie algebra of the group with `𝔲(n + 1)`. The fundamental vector field of
`ξ` at `[y]` is the image of `L ξ *ᵥ y` under the differential of `mkNonzero ℂ n`, so `D⁻¹` carries
it to `unitaryAction n (L ξ)`. Tau Ceti's `unitaryMomentMap n` is a moment map for `-(2π) τ`
(`TauCeti.ComplexProjectiveSpace.isMomentMap_unitaryMomentMap`), and
`fubiniStudyForm n = π (D⁻¹)^* τ`; pulling back along `D⁻¹`
(`TauCeti.SmoothTwoForm.IsMomentMap.mpullback`) and rescaling by `-1/2` shows that
`-μ` is a moment map for `fubiniStudyForm n`, where `μ x = ½ (unitaryMomentMap n (D⁻¹ x) ∘ L)`.
Coadjoint equivariance comes from `TauCeti.ComplexProjectiveSpace.unitaryMomentMap_smul`, the
equivariance of `D⁻¹`, and the compatibility of `L` with the coadjoint actions
(`TauCeti.Lie.coadjointRepresentation_comp_matrixUnitaryLieAlgebraEquiv`).

## Main results

* `TauCeti.ComplexProjectiveSpace.mfderiv_diffeomorphProjectivization_unitaryAction`: the
  differential of `diffeomorphProjectivization n` sends the generator of `X` at the preimage of
  `[y]` to the image of `X y` under the differential of `mkNonzero ℂ n` at `y`.
* `Projectivization.fundamentalVectorField_mk_unitarySubgroup`: the generator of `ξ` at `[y]` for
  the linear action of `unitarySubgroup (GL (Fin (n + 1)) ℂ)` is the image of `L ξ *ᵥ y` under
  the differential of `mkNonzero ℂ n` at `y`.
* `TauCeti.ComplexProjectiveSpace.mfderiv_diffeomorphProjectivization_symm_fundamentalVectorField`:
  the differential of `D⁻¹` sends that generator to `unitaryAction n (L ξ)`.
* `SymplecticGeometry.unitaryProjectivizationMoment n`: the map `x ↦ ½ (unitaryMomentMap n (D⁻¹ x)
  ∘ L)`, and `SymplecticGeometry.unitaryProjectivizationMoment_smul`, its coadjoint equivariance.
* `SymplecticGeometry.isEquivariantMomentMap_neg_unitaryProjectivizationMoment`: its negative is
  a group-level moment map for `fubiniStudyForm n`.

The proof of the first result takes `y = u` on the unit sphere, where the diffeomorphism after
`mk n` is `mkNonzero ℂ n` after the inclusion of the sphere, so that the chain rule applies; a
general `y` is a nonzero multiple of a unit vector, along which
`Projectivization.mfderivMk_smul_smul` transports the result.

## References

* [A. Cannas da Silva, *Lectures on Symplectic Geometry*][CannasdaSilva2001Lectures], Section 27.1
  (the unitary action on complex projective space).
-/

public section

open Metric Matrix Projectivization TauCeti
open scoped Manifold LinearAlgebra.Projectivization

namespace TauCeti.ComplexProjectiveSpace

variable {n : ℕ}

/-- A unit vector of `EuclideanSpace ℂ (Fin (n + 1))`, read as a nonzero vector of `ℂⁿ⁺¹`. -/
private def sphereToPunctured (u : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    puncturedSpace (Fin (n + 1) → ℂ) :=
  ⟨WithLp.ofLp (u : EuclideanSpace ℂ (Fin (n + 1))), mem_puncturedSpace.2
    ((WithLp.ofLp_eq_zero _).not.2 (ne_zero_of_mem_sphere one_ne_zero u))⟩

/-- The case of a unit vector: the generator of `X` at `mk n u` is sent to the image of `X u`
under the derivative of the projection `w ↦ [w]` at `u`. -/
private theorem mfderiv_diffeomorphProjectivization_unitaryAction_mk
    (X : unitaryLieAlgebra (Fin (n + 1))) (u : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) (diffeomorphProjectivization n) (mk n u)
        (unitaryAction n X (mk n u)) =
      mfderivMk (WithLp.ofLp (u : EuclideanSpace ℂ (Fin (n + 1))))
        ((X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) *ᵥ
          WithLp.ofLp (u : EuclideanSpace ℂ (Fin (n + 1)))) := by
  obtain ⟨v, hv⟩ := exists_mvfderiv_coe_sphere_eq_toEuclideanCLM_of_conjTranspose_eq_neg
    (n := 2 * n + 1) (conjTranspose_coe_unitaryLieAlgebra X) u
  have hcomp : diffeomorphProjectivization n ∘ mk n = mkNonzero ℂ n ∘ sphereToPunctured :=
    funext fun u ↦
      (diffeomorphProjectivization_mk n u).trans (mkNonzero_apply (sphereToPunctured u)).symm
  have hι : MDifferentiableAt (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin (n + 1) → ℂ) sphereToPunctured u := by
    refine ((TauCeti.ContMDiff.subtypeVal_comp_iff _ _).1 ?_ u).mdifferentiableAt
      (n := 1) one_ne_zero
    exact ((PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin (n + 1) ↦ ℂ) :
      EuclideanSpace ℂ (Fin (n + 1)) →L[ℝ] Fin (n + 1) → ℂ).contMDiff.comp contMDiff_coe_sphere
  rw [unitaryAction_apply_mk X u hv]
  refine (mfderiv_comp_apply u ((diffeomorphProjectivization n).mdifferentiable (by simp) _)
    ((contMDiff_mk 1 u).mdifferentiableAt one_ne_zero) v).symm.trans ?_
  rw [hcomp]
  refine (mfderiv_comp_apply u
    ((contMDiff_mkNonzero ℂ n 1 _).mdifferentiableAt one_ne_zero) hι v).trans ?_
  refine (mfderiv_mkNonzero_apply _ _).trans (congrArg _ ?_)
  rw [← TauCeti.Manifold.mfderiv_subtype_val_comp_apply, ← mvfderiv_apply_eq_mfderiv_apply]
  -- `Subtype.val ∘ sphereToPunctured` is, by definition, `WithLp.ofLp` after the inclusion of
  -- the sphere.
  refine ((PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin (n + 1) ↦ ℂ).mvfderiv_comp_apply
    ((↑) : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 → EuclideanSpace ℂ (Fin (n + 1))) u
    v).trans ?_
  rw [hv, PiLp.coe_continuousLinearEquiv, ofLp_toEuclideanCLM]

/-- **The generators of the unitary action, read on `ℙ ℂ (Fin (n + 1) → ℂ)`.** For
`X ∈ 𝔲(n + 1)` and a nonzero vector `y` of `ℂⁿ⁺¹`, the differential of the diffeomorphism
`diffeomorphProjectivization n : CPⁿ ≃ ℙ ℂ (Fin (n + 1) → ℂ)` sends the value of the vector field
`unitaryAction n X` at the point corresponding to the line `[y]` to the image of `X y` under the
differential of the projection `mkNonzero ℂ n` at `y`. -/
theorem mfderiv_diffeomorphProjectivization_unitaryAction (X : unitaryLieAlgebra (Fin (n + 1)))
    (y : puncturedSpace (Fin (n + 1) → ℂ)) :
    mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) (diffeomorphProjectivization n)
        ((diffeomorphProjectivization n).symm (mkNonzero ℂ n y))
        (unitaryAction n X ((diffeomorphProjectivization n).symm (mkNonzero ℂ n y))) =
      mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin n → ℂ) (mkNonzero ℂ n) y
        ((X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) *ᵥ (y : Fin (n + 1) → ℂ)) := by
  have hy : (y : Fin (n + 1) → ℂ) ≠ 0 := mem_puncturedSpace.1 y.property
  have hy' : WithLp.toLp 2 (y : Fin (n + 1) → ℂ) ≠ 0 := (WithLp.toLp_eq_zero _).not.2 hy
  set r := ‖WithLp.toLp 2 (y : Fin (n + 1) → ℂ)‖
  have hc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hy')
  -- The unit vector `y / ‖y‖` of `EuclideanSpace ℂ (Fin (n + 1))`, as Tau Ceti's
  -- `homeomorphProjectivization_symm_mk_eq_mk_inv_norm_smul` writes it.
  let u : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 :=
    ⟨(r⁻¹ : ℂ) • WithLp.toLp 2 (y : Fin (n + 1) → ℂ),
      mem_sphere_zero_iff_norm.2 (norm_smul_inv_norm hy')⟩
  have hu : WithLp.ofLp (u : EuclideanSpace ℂ (Fin (n + 1))) =
      (r⁻¹ : ℂ) • (y : Fin (n + 1) → ℂ) := by
    simp [u]
  have hp : (diffeomorphProjectivization n).symm (mkNonzero ℂ n y) = mk n u := by
    rw [coe_diffeomorphProjectivization_symm, mkNonzero_apply,
      homeomorphProjectivization_symm_mk_eq_mk_inv_norm_smul]
  rw [hp, mfderiv_diffeomorphProjectivization_unitaryAction_mk, mfderiv_mkNonzero_apply, hu,
    mulVec_smul, mfderivMk_smul_smul hy (inv_ne_zero hc)]

end TauCeti.ComplexProjectiveSpace

/-! ### The group-level moment map of the unitary group -/

open TauCeti.Lie
open scoped ContDiff Matrix.Norms.Operator

-- The topology and normed ring on matrices for which Tau Ceti builds `matrixUnitaryLieGroup`.
attribute [local instance] NormedAddCommGroup.toSeminormedAddCommGroup
attribute [local instance] Matrix.linftyOpTopologicalSpace Matrix.linftyOpContinuousStar
attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- The model vector space of the matrix unitary Lie group `unitarySubgroup (GL (Fin (n + 1)) ℂ)`:
its Lie algebra inside the Lie algebra of `GL (Fin (n + 1)) ℂ`. -/
local notation "𝔨[" n "]" => LieSubalgebra.toSubmodule
  (lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))
    (unitarySubgroup (GL (Fin (n + 1)) ℂ)))

/-- The Lie algebra of the matrix unitary Lie group `unitarySubgroup (GL (Fin (n + 1)) ℂ)`. -/
local notation "𝔤[" n "]" =>
  GroupLieAlgebra 𝓘(ℝ, 𝔨[n]) (unitarySubgroup (GL (Fin (n + 1)) ℂ))

namespace Projectivization

variable {n : ℕ}

/-- An element `g` of `unitarySubgroup (GL (Fin (n + 1)) ℂ)` acts on `ℙ ℂ (Fin (n + 1) → ℂ)` as
the unitary matrix `unitarySubgroupUnitsEquiv g`. -/
theorem unitarySubgroup_smul_eq (g : unitarySubgroup (GL (Fin (n + 1)) ℂ))
    (x : ℙ ℂ (Fin (n + 1) → ℂ)) : g • x = unitarySubgroupUnitsEquiv g • x := by
  induction x using Projectivization.ind with
  | h y hy =>
    rw [Subgroup.smul_def, smul_mk, smul_mk]
    congr 1

/-- **Generators of the unitary action on `ℙ ℂ (Fin (n + 1) → ℂ)`.** The fundamental vector field
of `ξ` at the line `[y]` is the image of `X *ᵥ y` under the differential of `mkNonzero ℂ n` at `y`,
where `X` is the skew-Hermitian matrix `matrixUnitaryLieAlgebraEquiv ξ`. -/
theorem fundamentalVectorField_mk_unitarySubgroup (ξ : 𝔤[n]) {y : Fin (n + 1) → ℂ}
    (hy : y ≠ 0) :
    fundamentalVectorField 𝓘(ℝ, Fin n → ℂ) ξ (mk ℂ y hy) =
      mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin n → ℂ) (mkNonzero ℂ n) ⟨y, mem_puncturedSpace.2 hy⟩
        ((matrixUnitaryLieAlgebraEquiv ξ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) *ᵥ y) :=
  (fundamentalVectorField_mk ξ hy ((ContMDiffSMul.contMDiff_smul_const (I := 𝓘(ℝ, 𝔨[n]))
    (n := ∞) y).mdifferentiableAt (by simp))).trans
      (by rw [fundamentalVectorField_unitarySubgroup])

end Projectivization

namespace TauCeti.ComplexProjectiveSpace

variable {n : ℕ}

/-- **The unitary generators on `CPⁿ` and on `ℙ ℂ (Fin (n + 1) → ℂ)` correspond.** The inverse
of `diffeomorphProjectivization n` sends the fundamental vector field of `ξ` for the linear action
on `ℙ ℂ (Fin (n + 1) → ℂ)` to Tau Ceti's generator `unitaryAction n` of the skew-Hermitian matrix
`matrixUnitaryLieAlgebraEquiv ξ`. -/
theorem mfderiv_diffeomorphProjectivization_symm_fundamentalVectorField (ξ : 𝔤[n])
    (x : ℙ ℂ (Fin (n + 1) → ℂ)) :
    mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) (diffeomorphProjectivization n).symm x
        (fundamentalVectorField 𝓘(ℝ, Fin n → ℂ) ξ x) =
      unitaryAction n (matrixUnitaryLieAlgebraEquiv ξ)
        ((diffeomorphProjectivization n).symm x) := by
  induction x using Projectivization.ind with
  | h y hy =>
    set y' : puncturedSpace (Fin (n + 1) → ℂ) := ⟨y, mem_puncturedSpace.2 hy⟩
    have hx : Projectivization.mk ℂ y hy = mkNonzero ℂ n y' := (mkNonzero_apply y').symm
    rw [fundamentalVectorField_mk_unitarySubgroup,
      ← mfderiv_diffeomorphProjectivization_unitaryAction,
      hx]
    -- The differential of `D⁻¹` undoes that of `D = diffeomorphProjectivization n`.
    set p := (diffeomorphProjectivization n).symm (mkNonzero ℂ n y')
    have hD := (diffeomorphProjectivization n).mfderiv_symm_apply_mfderiv_apply (by simp) p
      (unitaryAction n (matrixUnitaryLieAlgebraEquiv ξ) p)
    rwa [(diffeomorphProjectivization n).apply_symm_apply] at hD

end TauCeti.ComplexProjectiveSpace

namespace SymplecticGeometry

variable (n : ℕ)

/-- **The moment map of the unitary group on `ℙ ℂ (Fin (n + 1) → ℂ)`.** The line `x` goes to half
of Tau Ceti's `unitaryMomentMap n` at the corresponding point of `CPⁿ`, read on the Lie algebra of
`unitarySubgroup (GL (Fin (n + 1)) ℂ)` through `matrixUnitaryLieAlgebraEquiv`. Its negative is a
group-level moment map for `fubiniStudyForm n`
(`SymplecticGeometry.isEquivariantMomentMap_neg_unitaryProjectivizationMoment`). -/
noncomputable def unitaryProjectivizationMoment (x : ℙ ℂ (Fin (n + 1) → ℂ)) :
    Module.Dual ℝ 𝔤[n] :=
  (2⁻¹ : ℝ) • (ComplexProjectiveSpace.unitaryMomentMap n
    ((ComplexProjectiveSpace.diffeomorphProjectivization n).symm x)).comp
      ((matrixUnitaryLieAlgebraEquiv : 𝔤[n] ≃ₗ⁅ℝ⁆ unitaryLieAlgebra (Fin (n + 1))).toLinearEquiv :
        𝔤[n] →ₗ[ℝ] unitaryLieAlgebra (Fin (n + 1)))

theorem unitaryProjectivizationMoment_def (x : ℙ ℂ (Fin (n + 1) → ℂ)) :
    unitaryProjectivizationMoment n x =
      (2⁻¹ : ℝ) • (ComplexProjectiveSpace.unitaryMomentMap n
        ((ComplexProjectiveSpace.diffeomorphProjectivization n).symm x)).comp
          ((matrixUnitaryLieAlgebraEquiv :
              𝔤[n] ≃ₗ⁅ℝ⁆ unitaryLieAlgebra (Fin (n + 1))).toLinearEquiv :
            𝔤[n] →ₗ[ℝ] unitaryLieAlgebra (Fin (n + 1))) :=
  (rfl)

variable {n}

/-- `unitaryProjectivizationMoment n` is equivariant for the coadjoint representation of the
matrix unitary Lie group. -/
theorem unitaryProjectivizationMoment_smul (g : unitarySubgroup (GL (Fin (n + 1)) ℂ))
    (x : ℙ ℂ (Fin (n + 1) → ℂ)) :
    unitaryProjectivizationMoment n (g • x) =
      Lie.coadjointRepresentation ℝ 𝓘(ℝ, 𝔨[n]) _ g (unitaryProjectivizationMoment n x) := by
  rw [unitaryProjectivizationMoment_def, unitaryProjectivizationMoment_def,
    Projectivization.unitarySubgroup_smul_eq,
    ComplexProjectiveSpace.diffeomorphProjectivization_symm_smul,
    ComplexProjectiveSpace.unitaryMomentMap_smul, map_smul,
    coadjointRepresentation_comp_matrixUnitaryLieAlgebraEquiv]

variable (n) in
/-- **The unitary group acts on `ℙ ℂ (Fin (n + 1) → ℂ)` with a group-level moment map.** For the
linear action of `unitarySubgroup (GL (Fin (n + 1)) ℂ)` on `ℙ ℂ (Fin (n + 1) → ℂ)` and the
Fubini–Study form `fubiniStudyForm n`, the map `x ↦ -unitaryProjectivizationMoment n x` is a
coadjoint-equivariant moment map: `d⟨-μ, ξ⟩ = ι_{ξ_M} ω_FS`. -/
theorem isEquivariantMomentMap_neg_unitaryProjectivizationMoment :
    (fubiniStudyForm n).IsEquivariantMomentMap fun x ↦ -unitaryProjectivizationMoment n x where
  toIsMomentMap := by
    -- Tau Ceti's moment map for `-(2π) τ`, read on `𝔤[n]` and pulled back along `D⁻¹`, is a
    -- moment map for `-2 ω_FS`, since `ω_FS = π (D⁻¹)^* τ`; rescale by `-1/2`.
    have h := (((ComplexProjectiveSpace.isMomentMap_unitaryMomentMap (n := n)).comp
      (matrixUnitaryLieAlgebraEquiv :
        𝔤[n] ≃ₗ⁅ℝ⁆ unitaryLieAlgebra (Fin (n + 1))).toLieHom).mpullback
      (a' := InfinitesimalAction.fundamental 𝓘(ℝ, 𝔨[n]) _ 𝓘(ℝ, Fin n → ℂ) _)
      ((ComplexProjectiveSpace.diffeomorphProjectivization n).symm.contMDiff.of_le le_top)
      fun ξ x ↦ by
        rw [InfinitesimalAction.fundamental_apply, InfinitesimalAction.comp_apply,
          ComplexProjectiveSpace.mfderiv_diffeomorphProjectivization_symm_fundamentalVectorField,
          LieEquiv.coe_toLieHom]).const_smul (-2⁻¹)
    rw [SmoothForm.mpullback_smul, smul_smul,
      show (-2⁻¹ : ℝ) * -(2 * Real.pi) = Real.pi by ring, ← fubiniStudyForm_def] at h
    convert h using 2 with x
    ext ξ
    simp [unitaryProjectivizationMoment_def]
  apply_smul g x := by
    rw [unitaryProjectivizationMoment_smul, map_neg]

end SymplecticGeometry

end
