/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Algebra.Lie.Unitary
public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Basic
public import TauCeti.Geometry.Lie.Subgroup.Differential
public import TauCeti.Geometry.Lie.Subgroup.Unitary.Basic
import TauCeti.Geometry.Manifold.Instances.UnitsOfNormedAlgebra

/-!
# The Lie algebra of the matrix unitary Lie group

Tau Ceti makes the unitary subgroup `unitarySubgroup (GL n ℂ)` a real Lie group through the
closed-subgroup theorem (`TauCeti.Lie.matrixUnitaryLieGroup`), with charts modelled on its Lie
algebra inside the Lie algebra of `GL n ℂ`. It also has the concrete unitary Lie algebra
`unitaryLieAlgebra n` of skew-Hermitian matrices, with the adjoint action `X ↦ U X Uᴴ` of
`Matrix.unitaryGroup n ℂ` (`unitaryAdjointRepresentation`) and its dual
(`unitaryCoadjointRepresentation`). This file identifies the two pictures.

The identification `TauCeti.Lie.matrixUnitaryLieAlgebraEquiv` is a real Lie algebra equivalence
from the tangent Lie algebra `GroupLieAlgebra` of `unitarySubgroup (GL n ℂ)` onto
`unitaryLieAlgebra n`. It sends `ξ` to the derivative at `1` of the inclusion of the group in
`Matrix n n ℂ`, applied to `ξ` (`TauCeti.Lie.coe_matrixUnitaryLieAlgebraEquiv_apply`). It carries
the adjoint action of `g` to conjugation by the unitary matrix of `g`
(`TauCeti.Lie.matrixUnitaryLieAlgebraEquiv_adjointRepresentation`), and hence the coadjoint
representation of the Lie group to `unitaryCoadjointRepresentation`
(`TauCeti.Lie.coadjointRepresentation_comp_matrixUnitaryLieAlgebraEquiv`). The unitary matrix of
`g` is its image under Mathlib's `unitarySubgroupUnitsEquiv`.

The equivalence is assembled from Tau Ceti's: the identification of tangent vectors at `1` with
left-invariant derivations (`TauCeti.leftInvariantDerivationLieEquivGroupLieAlgebra`), the
differential of the inclusion of an embedded Lie subgroup as an equivalence onto its Lie algebra
in the ambient group (`TauCeti.Lie.EmbeddedLieSubgroupData.lieEquivLieSubalgebraOfSubgroup`), and
the algebra coordinates `TauCeti.Lie.unitsLieAlgebraLieEquiv` on the Lie algebra of `GL n ℂ`,
in which the Lie algebra of the unitary group is the skew-Hermitian matrices
(`TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_conjTranspose_eq_neg`).
The adjoint actions match by Tau Ceti's `MonoidHom.mvfderiv_adjointContinuousLinearMap`: for a
homomorphism of a Lie group into the units of a normed algebra, its derivative at `1` carries
`Ad_g` to conjugation by the image of `g`. Here it is applied to the inclusion of the unitary
group in `Matrix n n ℂ`.

Two declarations adapt Tau Ceti's versions for the special linear group:
`TauCeti.Lie.unitsLieAlgebraLieEquiv_map_lieSubalgebraOfSubgroup_unitarySubgroup` follows the
statement and proof of `TauCeti.Lie.unitsLieAlgebraLieEquiv_map_lieSubalgebraOfSubgroup_range_toGL`,
and `TauCeti.Lie.matrixUnitaryLieAlgebraEquiv` is assembled as
`Matrix.SpecialLinearGroup.lieAlgebraLieEquiv` is, with `slCoordinateEquiv`.

## Main definitions and results

* `TauCeti.Lie.unitsLieAlgebraLieEquiv_map_lieSubalgebraOfSubgroup_unitarySubgroup`: in algebra
  coordinates, the Lie algebra of `unitarySubgroup (GL n ℂ)` is `unitaryLieAlgebra n`.
* `TauCeti.Lie.matrixUnitaryLieAlgebraEquiv`: the Lie algebra of the matrix unitary Lie group is
  `unitaryLieAlgebra n`.
* `TauCeti.Lie.coe_matrixUnitaryLieAlgebraEquiv_apply`: the equivalence is the derivative at `1`
  of the inclusion into the matrices.
* `TauCeti.Lie.matrixUnitaryLieAlgebraEquiv_tangentAd`,
  `TauCeti.Lie.matrixUnitaryLieAlgebraEquiv_adjointRepresentation`: it carries the adjoint
  action to `unitaryAdjointRepresentation`.
* `TauCeti.Lie.coadjointRepresentation_comp_matrixUnitaryLieAlgebraEquiv`: it carries
  `unitaryCoadjointRepresentation` to the coadjoint representation.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Chapters 8 and 20.
-/

public section

noncomputable section

open Manifold
open scoped ContDiff Manifold Matrix Matrix.Norms.Operator

namespace TauCeti.Lie

-- The topology and normed ring on matrices for which Tau Ceti builds `matrixUnitaryLieGroup`.
attribute [local instance] NormedAddCommGroup.toSeminormedAddCommGroup
attribute [local instance] Matrix.linftyOpTopologicalSpace Matrix.linftyOpContinuousStar
attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance 100] LieRing.ofAssociativeRing

/-- The model vector space of the matrix unitary Lie group: its Lie algebra inside the Lie
algebra of `GL n ℂ`. -/
local notation "𝔨[" n "]" => LieSubalgebra.toSubmodule
  (lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n ℂ)) (unitarySubgroup (GL n ℂ)))

/-- Tau Ceti's closed-subgroup data of the matrix unitary group, whose charts and Lie group
structure are `matrixUnitaryChartedSpace` and `matrixUnitaryLieGroup`. -/
local notation "𝔡[" n "]" => matrixUnitaryEmbeddedLieSubgroupData (n := n) (𝕜 := ℂ)

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- In the algebra coordinates of the Lie algebra of `GL n ℂ`, the Lie algebra of the unitary
subgroup is `unitaryLieAlgebra n`, the skew-Hermitian matrices. -/
@[simp]
theorem unitsLieAlgebraLieEquiv_map_lieSubalgebraOfSubgroup_unitarySubgroup :
    (lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n ℂ)) (unitarySubgroup (GL n ℂ))).map
      (unitsLieAlgebraLieEquiv (R := Matrix n n ℂ)).toLieHom = unitaryLieAlgebra n := by
  ext A
  rw [mem_unitaryLieAlgebra_iff,
    ← unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_conjTranspose_eq_neg]
  constructor
  · rintro ⟨X, hX, rfl⟩
    simpa only [LieHom.coe_toLinearMap, LieEquiv.coe_toLieHom, LieEquiv.symm_apply_apply,
      LieSubalgebra.coe_toSubmodule, LieSubalgebra.mem_coe] using hX
  · intro hA
    exact ⟨_, hA, by simp⟩

/-- **The Lie algebra of the matrix unitary Lie group is the unitary Lie algebra.** The tangent
Lie algebra at `1` of `unitarySubgroup (GL n ℂ)`, with Tau Ceti's closed-subgroup Lie group
structure, is isomorphic as a real Lie algebra to `unitaryLieAlgebra n`, by the derivative at `1`
of the inclusion into the matrices (`coe_matrixUnitaryLieAlgebraEquiv_apply`). -/
def matrixUnitaryLieAlgebraEquiv :
    GroupLieAlgebra 𝓘(ℝ, 𝔨[n]) (unitarySubgroup (GL n ℂ)) ≃ₗ⁅ℝ⁆
      unitaryLieAlgebra n :=
  (leftInvariantDerivationLieEquivGroupLieAlgebra
      (ContMDiffMul.isInteriorPoint (I := 𝓘(ℝ, 𝔨[n])) (n := ∞) (by simp)
        (1 : unitarySubgroup (GL n ℂ)))).symm.trans <|
    𝔡[n].lieEquivLieSubalgebraOfSubgroup.trans <|
      LieEquiv.ofSubalgebras _ _ unitsLieAlgebraLieEquiv
        unitsLieAlgebraLieEquiv_map_lieSubalgebraOfSubgroup_unitarySubgroup

/-- The matrix of `matrixUnitaryLieAlgebraEquiv ξ` is the image of `ξ` under the Lie algebra map
of the inclusion of the unitary group in `GL n ℂ`. -/
theorem coe_matrixUnitaryLieAlgebraEquiv_apply_eq_groupLieAlgebraLieHom
    (ξ : GroupLieAlgebra 𝓘(ℝ, 𝔨[n]) (unitarySubgroup (GL n ℂ))) :
    (matrixUnitaryLieAlgebraEquiv ξ : Matrix n n ℂ) =
      𝔡[n].subtypeVal.groupLieAlgebraLieHom ξ := by
  let e := leftInvariantDerivationLieEquivGroupLieAlgebra
      (ContMDiffMul.isInteriorPoint (I := 𝓘(ℝ, 𝔨[n])) (n := ∞) (by simp)
        (1 : unitarySubgroup (GL n ℂ)))
  have h : (matrixUnitaryLieAlgebraEquiv ξ : Matrix n n ℂ) =
      leftInvariantDerivationLieEquivGroupLieAlgebra
          (ContMDiffMul.isInteriorPoint (I := 𝓘(ℝ, Matrix n n ℂ)) (n := ∞) (by simp)
            (1 : GL n ℂ)) (lieMap 𝔡[n].subtypeVal (e.symm ξ)) := by
    simp only [matrixUnitaryLieAlgebraEquiv, LieEquiv.trans_apply, LieEquiv.ofSubalgebras_apply,
      EmbeddedLieSubgroupData.lieEquivLieSubalgebraOfSubgroup_apply,
      EmbeddedLieSubgroupData.lieMapSubtypeVal_apply, unitsLieAlgebraLieEquiv_apply,
      unitsLieAlgebraEquiv_apply, leftInvariantDerivationLieEquivGroupLieAlgebra_apply, e]
    -- The two sides differ only in the proofs that `1` is an interior point.
    rfl
  rw [h, leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap, e.apply_symm_apply,
    ContMDiffMonoidMorphism.coe_groupLieAlgebraLieHom, MonoidHom.groupLieAlgebraMap_apply,
    ContMDiffMonoidMorphism.coe_toMonoidHom]

/-- **The identification is the derivative of the inclusion.** The matrix of
`matrixUnitaryLieAlgebraEquiv ξ` is the derivative at `1` of the inclusion
`unitarySubgroup (GL n ℂ) → Matrix n n ℂ`, applied to `ξ`. -/
theorem coe_matrixUnitaryLieAlgebraEquiv_apply
    (ξ : GroupLieAlgebra 𝓘(ℝ, 𝔨[n]) (unitarySubgroup (GL n ℂ))) :
    (matrixUnitaryLieAlgebraEquiv ξ : Matrix n n ℂ) =
      mfderiv 𝓘(ℝ, 𝔨[n]) 𝓘(ℝ, Matrix n n ℂ)
        (fun k : unitarySubgroup (GL n ℂ) ↦ ((k : GL n ℂ) : Matrix n n ℂ)) 1 ξ := by
  have hφ : HasMFDerivAt 𝓘(ℝ, 𝔨[n]) 𝓘(ℝ, Matrix n n ℂ) 𝔡[n].subtypeVal 1
      (mfderiv 𝓘(ℝ, 𝔨[n]) 𝓘(ℝ, Matrix n n ℂ) 𝔡[n].subtypeVal 1) :=
    (𝔡[n].subtypeVal.contMDiff_toFun.mdifferentiableAt (by simp)).hasMFDerivAt
  have hf : Units.val ∘ ⇑𝔡[n].subtypeVal =
      fun k : unitarySubgroup (GL n ℂ) ↦ ((k : GL n ℂ) : Matrix n n ℂ) :=
    funext fun k ↦ congrArg Units.val (𝔡[n].subtypeVal_apply k)
  have hcomp := (Units.hasMFDerivAt_val (𝕜 := ℝ) (𝔡[n].subtypeVal 1)).comp 1 hφ
  rw [hf] at hcomp
  rw [(hcomp.congr_mfderiv (ContinuousLinearMap.id_comp _)).mfderiv,
    coe_matrixUnitaryLieAlgebraEquiv_apply_eq_groupLieAlgebraLieHom,
    ContMDiffMonoidMorphism.coe_groupLieAlgebraLieHom, MonoidHom.groupLieAlgebraMap_apply,
    ContMDiffMonoidMorphism.coe_toMonoidHom]
  -- The two sides agree up to the definitional identification of the tangent spaces of `GL n ℂ`
  -- with `Matrix n n ℂ`.
  rfl

/-- **The identification intertwines the adjoint actions.** `matrixUnitaryLieAlgebraEquiv`
carries the adjoint automorphism `Ad_g` of the matrix unitary Lie group to conjugation
`X ↦ U X Uᴴ` by the unitary matrix `U` of `g`. -/
theorem matrixUnitaryLieAlgebraEquiv_tangentAd (g : unitarySubgroup (GL n ℂ))
    (ξ : GroupLieAlgebra 𝓘(ℝ, 𝔨[n]) (unitarySubgroup (GL n ℂ))) :
    matrixUnitaryLieAlgebraEquiv (tangentAd (I := 𝓘(ℝ, 𝔨[n])) g ξ) =
      unitaryAdjointRepresentation n (unitarySubgroupUnitsEquiv g)
        (matrixUnitaryLieAlgebraEquiv ξ) := by
  have h := ((Units.coeHom (Matrix n n ℂ)).comp (unitarySubgroup (GL n ℂ)).subtype
    ).mvfderiv_adjointContinuousLinearMap (I := 𝓘(ℝ, 𝔨[n])) g ξ
  have hg : star ((g : GL n ℂ) : Matrix n n ℂ) = ((g⁻¹ : GL n ℂ) : Matrix n n ℂ) := by
    simpa only [unitarySubgroupUnitsEquiv_apply_coe] using
      Units.mem_unitary_iff_star_eq_inv.1 (unitarySubgroupUnitsEquiv g).prop
  apply Subtype.ext
  rw [coe_unitaryAdjointRepresentation_apply, coe_matrixUnitaryLieAlgebraEquiv_apply,
    tangentAd_apply, coe_matrixUnitaryLieAlgebraEquiv_apply, unitarySubgroupUnitsEquiv_apply_coe,
    hg]
  simpa only [mvfderiv_apply_eq_mfderiv_apply, MonoidHom.coe_comp, Units.coeHom_apply,
    Subgroup.coe_subtype, Function.comp_def, Subgroup.coe_inv] using h

/-- **The identification intertwines the adjoint representations.**
`matrixUnitaryLieAlgebraEquiv`
carries the adjoint representation of the matrix unitary Lie group to
`unitaryAdjointRepresentation n`, along `unitarySubgroupUnitsEquiv`. -/
theorem matrixUnitaryLieAlgebraEquiv_adjointRepresentation (g : unitarySubgroup (GL n ℂ))
    (ξ : GroupLieAlgebra 𝓘(ℝ, 𝔨[n]) (unitarySubgroup (GL n ℂ))) :
    matrixUnitaryLieAlgebraEquiv
        (adjointRepresentation ℝ 𝓘(ℝ, 𝔨[n]) (unitarySubgroup (GL n ℂ)) g ξ) =
      unitaryAdjointRepresentation n (unitarySubgroupUnitsEquiv g)
        (matrixUnitaryLieAlgebraEquiv ξ) := by
  rw [adjointRepresentation_apply, ← tangentAd_apply, matrixUnitaryLieAlgebraEquiv_tangentAd]

/-- **The identification intertwines the coadjoint representations.** Pulling a linear form on
`unitaryLieAlgebra n` back along `matrixUnitaryLieAlgebraEquiv` carries
`unitaryCoadjointRepresentation n` to the coadjoint representation of the matrix unitary Lie
group, along `unitarySubgroupUnitsEquiv`. -/
theorem coadjointRepresentation_comp_matrixUnitaryLieAlgebraEquiv (g : unitarySubgroup (GL n ℂ))
    (ν : Module.Dual ℝ (unitaryLieAlgebra n)) :
    coadjointRepresentation ℝ 𝓘(ℝ, 𝔨[n]) (unitarySubgroup (GL n ℂ)) g
        (ν ∘ₗ (matrixUnitaryLieAlgebraEquiv (n := n)).toLinearEquiv.toLinearMap) =
      unitaryCoadjointRepresentation n (unitarySubgroupUnitsEquiv g) ν ∘ₗ
        (matrixUnitaryLieAlgebraEquiv (n := n)).toLinearEquiv.toLinearMap := by
  ext ξ
  simp only [coadjointRepresentation_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LieEquiv.coe_toLinearEquiv, unitaryCoadjointRepresentation_apply_apply, ← tangentAd_apply,
    matrixUnitaryLieAlgebraEquiv_tangentAd, map_inv]

end TauCeti.Lie
