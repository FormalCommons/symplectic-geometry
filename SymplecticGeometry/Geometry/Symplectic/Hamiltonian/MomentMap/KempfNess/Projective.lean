/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.KempfNess.Basic
public import SymplecticGeometry.Geometry.Manifold.Projectivization.Action
public import SymplecticGeometry.Geometry.Manifold.Projectivization.FubiniStudy.Kahler
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.ComplexProjectiveSpace
import SymplecticGeometry.Geometry.Manifold.Projectivization.Pseudoholomorphic
import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Restrict

/-!
# Complexified linear actions on complex projective space

Let `C : LieComplexification I G IC Gc` be a complexification, and let `G` and `Gc` act
`ℂ`-linearly on `V = ℂⁿ⁺¹`, so that both act on `ℙ ℂ V` by `g • [v] = [g • v]`
(`Projectivization.smul_mk`). This file shows that if the action of `Gc` on `V` is smooth and a
complexified action of that of `G` for multiplication by `i`, then so is the induced action on
`ℂPⁿ = ℙ ℂ V`, for its complex structure `J`. For an action through a representation
`ρ : Gc →* GL(n + 1, ℂ)` and `G` acting through `ρ ∘ C.toHom`, the first condition of a
complexified action on `V` holds by definition, and since the generator `X_Z v` is `dρ₁(Z) v`
(`TauCeti.fundamentalVectorField_eq_mfderiv_apply`), the second is the identity
`dρ₁ (C.cplx Z) = i • dρ₁ Z` on the directions `Z = C.lieMap ξ`. The library's Fubini–Study form
is invariant under the elements that act by unitary matrices, and `J` under every element
(`TauCeti.isPseudoholomorphic_const_smul`, which applies by Tau Ceti's
`Projectivization.instContMDiffConstSMul`).

## Main results

* `SymplecticGeometry.mpullback_smul_fubiniStudyForm`: the pull-back of the Fubini–Study form
  `SymplecticGeometry.fubiniStudyForm n` along `[v] ↦ [g • v]`, for `g` acting on `ℂⁿ⁺¹` by a
  unitary matrix, is the Fubini–Study form. This is
  `SymplecticGeometry.mpullback_unitary_fubiniStudyForm`, since `g • ·` is Tau Ceti's
  `Projectivization.mapDiffeomorph` of that matrix.
* `SymplecticGeometry.isComplexifiedAction_projectivization`: the complexified action. The
  fundamental vector field of `ζ` at `[y]` is the image of `X_ζ y` under the differential of the
  projection `Projectivization.mkNonzero` (`Projectivization.fundamentalVectorField_mk`), and
  that differential carries multiplication by `i` to `J`
  (`Projectivization.mfderiv_mkNonzero_I_smul`), as in the proof of
  `SymplecticGeometry.isComplexifiedAction_circle`.
* `SymplecticGeometry.projectivizationMoment I φ`: for `G` acting on `ℂⁿ⁺¹` through a
  homomorphism `φ` into the matrix unitary Lie group `unitarySubgroup (GL (Fin (n + 1)) ℂ)`, the
  map `x ↦ μ x ∘ dφ`, where `μ = SymplecticGeometry.unitaryProjectivizationMoment n` is half of
  Tau Ceti's `TauCeti.ComplexProjectiveSpace.unitaryMomentMap` read on `ℙ ℂ (Fin (n + 1) → ℂ)`,
  and `dφ` is the differential of `φ` at the identity. For a representation
  `ρ : Gc →* GL(n + 1, ℂ)` that is unitary on `G`, `φ` is `ρ ∘ C.toHom` with its values
  restricted to the unitary group.
* `SymplecticGeometry.isEquivariantMomentMap_neg_projectivizationMoment`: if `φ` is
  differentiable at the identity, `x ↦ -projectivizationMoment I φ x` is a coadjoint-equivariant
  moment map for `fubiniStudyForm n`, so `projectivizationMoment I φ` is a moment map with the
  sign convention of the stability theory. It is not derived again: it is the restriction of
  `SymplecticGeometry.isEquivariantMomentMap_neg_unitaryProjectivizationMoment` along `φ`, by
  Tau Ceti's `TauCeti.SmoothTwoForm.IsEquivariantMomentMap.comp_monoidHom`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §5.7.
* [V. Georgoulas, J. W. Robbin, D. A. Salamon, *The moment-weight inequality and the
  Hilbert–Mumford criterion*][GeorgoulasRobbinSalamon2021], Theorem 12.4.
* [A. Cannas da Silva, *Lectures on Symplectic Geometry*][CannasdaSilva2001Lectures], Section 27.1
  (the unitary action on complex projective space and its moment map).
-/

public section

open Matrix TauCeti Projectivization SmoothAlmostComplexStructure
open scoped Manifold ContDiff LinearAlgebra.Projectivization

namespace SymplecticGeometry

variable {n : ℕ}

/-- **Unitary symmetries of the Fubini–Study form.** If `g` acts on `ℂⁿ⁺¹` by the unitary matrix
`U`, the pull-back of the Fubini–Study form along `[v] ↦ [g • v]` is the Fubini–Study form. -/
theorem mpullback_smul_fubiniStudyForm {K : Type*} [Group K]
    [DistribMulAction K (Fin (n + 1) → ℂ)] [SMulCommClass K ℂ (Fin (n + 1) → ℂ)] (g : K)
    (U : unitaryGroup (Fin (n + 1)) ℂ)
    (hU : ∀ v : Fin (n + 1) → ℂ, g • v = (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) *ᵥ v) :
    SmoothForm.mpullback (fun x : ℙ ℂ (Fin (n + 1) → ℂ) ↦ g • x) (contMDiff_const_smul g)
      (fubiniStudyForm n) = fubiniStudyForm n := by
  have h : (fun x : ℙ ℂ (Fin (n + 1) → ℂ) ↦ g • x) =
      ⇑(mapDiffeomorph (UnitaryGroup.toLinearEquiv U) ∞) := by
    funext x
    induction x using ind with
    | h v hv => simp [smul_mk, map_mk, UnitaryGroup.toLinearEquiv, hU]
  simp only [h]
  exact mpullback_unitary_fubiniStudyForm U

section Moment

open TauCeti.Lie
open scoped Matrix.Norms.Operator

-- The topology and normed ring on matrices for which Tau Ceti builds `matrixUnitaryLieGroup`.
attribute [local instance] NormedAddCommGroup.toSeminormedAddCommGroup
attribute [local instance] Matrix.linftyOpTopologicalSpace Matrix.linftyOpContinuousStar
attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]

/-- The model vector space of the matrix unitary Lie group `unitarySubgroup (GL (Fin (n + 1)) ℂ)`:
its Lie algebra inside the Lie algebra of `GL (Fin (n + 1)) ℂ`. -/
local notation "𝔨[" n "]" => LieSubalgebra.toSubmodule
  (lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))
    (unitarySubgroup (GL (Fin (n + 1)) ℂ)))

/-- **The moment map of a unitary representation on `ℂPⁿ`.** For a homomorphism
`φ : G →* U(n + 1)` into the matrix unitary Lie group, the line `x` goes to the moment
`SymplecticGeometry.unitaryProjectivizationMoment n x` of the unitary group, read on the Lie
algebra of `G` through the differential `dφ` of `φ` at the identity. Its negative is a group-level
moment map for `fubiniStudyForm n` when `G` acts on `ℂⁿ⁺¹` through `φ`
(`SymplecticGeometry.isEquivariantMomentMap_neg_projectivizationMoment`). -/
noncomputable def projectivizationMoment (φ : G →* unitarySubgroup (GL (Fin (n + 1)) ℂ))
    (x : ℙ ℂ (Fin (n + 1) → ℂ)) : Module.Dual ℝ (GroupLieAlgebra I G) :=
  (unitaryProjectivizationMoment n x).comp (φ.groupLieAlgebraMap I 𝓘(ℝ, 𝔨[n])).toLinearMap

theorem projectivizationMoment_def (φ : G →* unitarySubgroup (GL (Fin (n + 1)) ℂ))
    (x : ℙ ℂ (Fin (n + 1) → ℂ)) :
    projectivizationMoment I φ x =
      (unitaryProjectivizationMoment n x).comp (φ.groupLieAlgebraMap I 𝓘(ℝ, 𝔨[n])).toLinearMap :=
  (rfl)

/-- The component of `projectivizationMoment I φ x` along `ξ` is that of the moment of the unitary
group along `dφ ξ`. -/
theorem projectivizationMoment_apply (φ : G →* unitarySubgroup (GL (Fin (n + 1)) ℂ))
    (x : ℙ ℂ (Fin (n + 1) → ℂ)) (ξ : GroupLieAlgebra I G) :
    projectivizationMoment I φ x ξ =
      unitaryProjectivizationMoment n x (φ.groupLieAlgebraMap I 𝓘(ℝ, 𝔨[n]) ξ) :=
  (rfl)

variable {I} [CompleteSpace E] [LieGroup I ∞ G]
  [DistribMulAction G (Fin (n + 1) → ℂ)] [SMulCommClass G ℂ (Fin (n + 1) → ℂ)]
  [ContMDiffSMul I 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ G (Fin (n + 1) → ℂ)]

/-- **The moment map of a unitary representation on `ℂPⁿ`.** Let `G` act on `ℂⁿ⁺¹` smoothly
through a homomorphism `φ : G →* U(n + 1)` that is differentiable at the identity. Then
`x ↦ -projectivizationMoment I φ x` is a coadjoint-equivariant moment map for the induced action on
`ℂPⁿ` and the Fubini–Study form `fubiniStudyForm n`. -/
theorem isEquivariantMomentMap_neg_projectivizationMoment
    (φ : G →* unitarySubgroup (GL (Fin (n + 1)) ℂ)) (hφ : MDifferentiableAt I 𝓘(ℝ, 𝔨[n]) (⇑φ) 1)
    (hsmul : ∀ (g : G) (v : Fin (n + 1) → ℂ), g • v = φ g • v) :
    (fubiniStudyForm n).IsEquivariantMomentMap fun x ↦ -projectivizationMoment I φ x := by
  have h := (isEquivariantMomentMap_neg_unitaryProjectivizationMoment n).comp_monoidHom φ hφ
    fun g x ↦ by
      induction x using ind with
      | h v hv => simp only [Subgroup.smul_def, smul_mk, hsmul]
  simpa only [projectivizationMoment_def, LinearMap.neg_comp] using h

end Moment

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {EC : Type*} [NormedAddCommGroup EC] [NormedSpace ℝ EC] [CompleteSpace EC]
  {HC : Type*} [TopologicalSpace HC] {IC : ModelWithCorners ℝ EC HC}
  {Gc : Type*} [TopologicalSpace Gc] [ChartedSpace HC Gc] [Group Gc] [LieGroup IC ∞ Gc]
  [T2Space Gc] [BoundarylessManifold IC Gc]
  [DistribMulAction G (Fin (n + 1) → ℂ)] [SMulCommClass G ℂ (Fin (n + 1) → ℂ)]
  [DistribMulAction Gc (Fin (n + 1) → ℂ)] [SMulCommClass Gc ℂ (Fin (n + 1) → ℂ)]
  [ContMDiffSMul IC 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ Gc (Fin (n + 1) → ℂ)]

/-- **Linear complexified actions on `ℂPⁿ`.** Let `G` and `Gc` act `ℂ`-linearly on `ℂⁿ⁺¹`, the
action of `Gc` smoothly. If the action of `Gc` on `ℂⁿ⁺¹` is a complexified action of that of `G`
for multiplication by `i`, then so is the induced action of `Gc` on `ℂPⁿ`, for the complex
structure of `ℂPⁿ`. -/
theorem isComplexifiedAction_projectivization {C : LieComplexification I G IC Gc}
    (h : IsComplexifiedAction C (ofComplexManifold (Fin (n + 1) → ℂ) (Fin (n + 1) → ℂ))) :
    IsComplexifiedAction C (ofComplexManifold (Fin n → ℂ) (ℙ ℂ (Fin (n + 1) → ℂ))) where
  toHom_smul u x := by
    induction x using ind with
    | h v hv => simp only [smul_mk, h.toHom_smul]
  fundamentalVectorField_cplx ξ x := by
    induction x using ind with
    | h y hy =>
      have hX := fun Z ↦ fundamentalVectorField_mk (I := IC) Z hy
        ((ContMDiffSMul.contMDiff_smul_const (I := IC) (I' := 𝓘(ℝ, Fin (n + 1) → ℂ)) (n := 1)
          (G := Gc) y).mdifferentiableAt one_ne_zero)
      rw [hX, hX, h.fundamentalVectorField_cplx]
      exact (congrArg _ (ofComplexManifold_apply _ _)).trans
        ((mfderiv_mkNonzero_I_smul _ _).trans (by rw [mkNonzero_apply]))

end SymplecticGeometry

end
