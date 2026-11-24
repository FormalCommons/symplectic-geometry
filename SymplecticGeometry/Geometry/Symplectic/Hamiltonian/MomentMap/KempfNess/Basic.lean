/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Lie.Complexification
public import TauCeti.Geometry.Lie.FundamentalVectorField
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure

/-!
# Complexified actions

Let `C : LieComplexification I G IC Gc` be a complexification of a real Lie group `G`, and suppose
that `G` and `Gc` both act on `M`, which carries the almost complex structure `J`. The action of
`Gc` is a *complexified action* of that of `G` if it extends it along the inclusion `C.toHom`, and
if, for every `ξ` in the Lie algebra of `G`, the fundamental vector field of the imaginary
direction `C.cplx (C.lieMap ξ)` is `J` applied to that of `ξ`: `X_{iξ} = J X_ξ`. This is the
infinitesimal form of the holomorphicity of the action of `Gc`, the only form in which the
Kempf–Ness theory uses it.

## Main definitions

* `SymplecticGeometry.IsComplexifiedAction C J`: the action of `Gc` on `M` is a complexified
  action of that of `G`, for `C` and `J`.

## Main results

* `SymplecticGeometry.IsComplexifiedAction.fundamentalVectorField_lieMap`: the fundamental vector
  field of `C.lieMap ξ` for the action of `Gc` is that of `ξ` for the action of `G`.
* `SymplecticGeometry.IsComplexifiedAction.isMIntegralCurve_expI_smul`: the curve
  `t ↦ C.expI (t • ξ) • p` is an integral curve of `x ↦ J x (X_ξ x)`.
* `SymplecticGeometry.isComplexifiedAction_circle`: the action of `ℂˣ` on `ℂ` by multiplication,
  with `J` multiplication by `i`, is a complexified action of the rotation action of `Circle`, for
  the complexification `LieComplexification.circle`.

The integral curve is Tau Ceti's `TauCeti.isMIntegralCurve_mulInvariantExp_smul_smul` for the
action of `Gc` and the direction `C.cplx (C.lieMap ξ)`. In the example, the orbit maps of `ℂˣ` are
holomorphic, so their real differentials commute with multiplication by `i`
(`MDifferentiableAt.mfderiv_ofComplexManifold_apply`).

## References

* [V. Georgoulas, J. W. Robbin and D. A. Salamon, *The Moment-Weight Inequality and the
  Hilbert–Mumford Criterion*][GeorgoulasRobbinSalamon2021], §2.
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §5.7.
-/

public section

noncomputable section

open Function Manifold TauCeti
open scoped Manifold ContDiff

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {EC : Type*} [NormedAddCommGroup EC] [NormedSpace ℝ EC] [CompleteSpace EC]
  {HC : Type*} [TopologicalSpace HC] {IC : ModelWithCorners ℝ EC HC}
  {Gc : Type*} [TopologicalSpace Gc] [ChartedSpace HC Gc] [Group Gc] [LieGroup IC ∞ Gc]
  [T2Space Gc] [BoundarylessManifold IC Gc]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  [MulAction G M] [MulAction Gc M]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- The action of the complexification `Gc` on `M` is a *complexified action* of that of `G`,
for the complexification `C` and the almost complex structure `J` of `M`: it extends the action of
`G` along `C.toHom`, and for every `ξ` in the Lie algebra of `G` the fundamental vector field of
`C.cplx (C.lieMap ξ)` is `J` applied to that of `C.lieMap ξ`, at every point. -/
structure IsComplexifiedAction (C : LieComplexification I G IC Gc)
    (J : SmoothAlmostComplexStructure I' M) : Prop where
  /-- The action of `Gc` extends that of `G` along `C.toHom`. -/
  toHom_smul (u : G) (x : M) : C.toHom u • x = u • x
  /-- The fundamental vector field of an imaginary direction is `J` applied to that of the real
  direction: `X_{iξ} = J X_ξ`. -/
  fundamentalVectorField_cplx (ξ : GroupLieAlgebra I G) (x : M) :
    fundamentalVectorField I' (C.cplx (C.lieMap ξ)) x =
      J x (fundamentalVectorField I' (C.lieMap ξ) x)

namespace IsComplexifiedAction

variable [ContMDiffSMul IC I' ∞ Gc M] {C : LieComplexification I G IC Gc}
  {J : SmoothAlmostComplexStructure I' M}

/-- For a complexified action, the fundamental vector field of `C.lieMap ξ` for the action of
`Gc` is that of `ξ` for the action of `G`. -/
theorem fundamentalVectorField_lieMap (h : IsComplexifiedAction C J) (ξ : GroupLieAlgebra I G) :
    fundamentalVectorField I' (C.lieMap ξ) =
      (fundamentalVectorField I' ξ : ∀ x : M, TangentSpace I' x) := by
  rw [LieComplexification.lieMap_def, ContMDiffMonoidMorphism.coe_groupLieAlgebraLieHom]
  exact C.toHom.toMonoidHom.fundamentalVectorField_groupLieAlgebraMap
    (C.toHom.contMDiff_toFun.mdifferentiableAt (by simp)) (fun u x ↦ (h.toHom_smul u x).symm) ξ

/-- **The imaginary one-parameter subgroups move points along `J X_ξ`.** For a complexified
action, the curve `t ↦ C.expI (t • ξ) • p` is an integral curve of the vector field
`x ↦ J x (X_ξ x)`, where `X_ξ` is the fundamental vector field of `ξ` for the action of `G`. -/
theorem isMIntegralCurve_expI_smul (h : IsComplexifiedAction C J) (ξ : GroupLieAlgebra I G)
    (p : M) :
    IsMIntegralCurve (fun t : ℝ ↦ C.expI (t • ξ) • p)
      (fun x ↦ J x (fundamentalVectorField I' ξ x)) := by
  have hγ : (fun t : ℝ ↦ C.expI (t • ξ) • p) =
      fun t : ℝ ↦ mulInvariantExp (t • C.cplx (C.lieMap ξ)) • p := by
    funext t
    rw [LieComplexification.expI_def, map_smul, AlmostComplexStructure.apply_smul]
  have hv : fundamentalVectorField I' (C.cplx (C.lieMap ξ)) =
      fun x ↦ J x (fundamentalVectorField I' ξ x) :=
    funext fun x ↦ by rw [h.fundamentalVectorField_cplx, h.fundamentalVectorField_lieMap]
  rw [hγ, ← hv]
  exact isMIntegralCurve_mulInvariantExp_smul_smul (I' := I') (C.cplx (C.lieMap ξ)) p

end IsComplexifiedAction

/-! ### The example: `ℂˣ` acting on `ℂ` -/

section Circle

open Complex

/-- The action of `ℂˣ` on `ℂ` by multiplication is smooth, for the real manifold structures. -/
instance _root_.Complex.instContMDiffSMulUnitsReal :
    ContMDiffSMul 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ ℂˣ ℂ where
  contMDiff_smul :=
    ((contDiff_mul (𝕜 := ℝ)).contMDiff.comp
      ((Units.contMDiff_val.comp contMDiff_fst).prodMk_space contMDiff_snd)).congr
      fun p ↦ Units.smul_def p.1 p.2

/-- **`ℂˣ` acting on `ℂ` is a complexified action.** The action of `ℂˣ` on `ℂ` by multiplication,
with the almost complex structure of `ℂ` given by multiplication by `i`
(`SmoothAlmostComplexStructure.ofComplexManifold`), is a complexified action of the rotation
action of `Circle`, for the complexification `LieComplexification.circle`. -/
theorem isComplexifiedAction_circle :
    IsComplexifiedAction LieComplexification.circle
      (SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ) where
  toHom_smul u z := by
    rw [Units.smul_def, LieComplexification.circle_toHom, Circle.coe_contMDiffToUnits_apply,
      Circle.smul_def]
  fundamentalVectorField_cplx ξ z := by
    -- The orbit map of `z` is holomorphic, so its real differential commutes with `i`.
    have hf : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (fun g : ℂˣ ↦ g • z) 1 :=
      (ContMDiffSMul.contMDiff_smul_const (I := 𝓘(ℂ, ℂ)) (I' := 𝓘(ℂ, ℂ)) (n := 1)
        z).mdifferentiableAt one_ne_zero
    rw [fundamentalVectorField_apply, fundamentalVectorField_apply,
      LieComplexification.circle_cplx, SmoothAlmostComplexStructure.almostComplexStructureAt_apply]
    -- The two sides are `i` times the same vector, at the points `1 • z` and `z`.
    exact (hf.mfderiv_ofComplexManifold_apply _).trans
      ((SmoothAlmostComplexStructure.ofComplexManifold_apply _ _).trans
        (SmoothAlmostComplexStructure.ofComplexManifold_apply _ _).symm)

end Circle

end SymplecticGeometry
