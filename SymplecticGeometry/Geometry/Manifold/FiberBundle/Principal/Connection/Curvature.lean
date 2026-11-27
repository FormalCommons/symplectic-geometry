/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.FiberBundle.Principal.Connection.Basic
public import TauCeti.Geometry.Lie.Adjoint.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.MapCoeff
import TauCeti.Geometry.Manifold.DifferentialForm.VectorField
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
public import TauCeti.Topology.Algebra.Lie.Bracket
public import TauCeti.Geometry.Manifold.DifferentialForm.Gauge.Curvature
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.GaugeCurvature
import SymplecticGeometry.Geometry.Manifold.FiberBundle.Principal.BasicForm
import SymplecticGeometry.LinearAlgebra.Alternating.Conormal

/-!
# The curvature of a connection form

For a Lie group `G`, write `𝔤 = GroupLieAlgebra IG G`. The **curvature** of a smooth
`𝔤`-valued one-form `A` on a manifold `M` is the `𝔤`-valued two-form
`F_A = d A + ½ [A ∧ A]`, where `[A ∧ A]` is the wedge of `A` with itself paired by the bracket
of `𝔤` (`TauCeti.lieL`). This is Tau Ceti's `TauCeti.gaugeCurvature` for the bracket
`lieL ℝ 𝔤 𝔤`, and on a pair of tangent vectors it is `F_A(v, w) = d A(v, w) + [A v, A w]`
(`TauCeti.gaugeCurvature_val`). The definition needs no principal bundle, and its naturality
and the structure equation hold for any bracket
(`SymplecticGeometry/Geometry/Manifold/DifferentialForm/GaugeCurvature.lean`). This file proves
the properties of the curvature of a connection form on the total space of a principal bundle.

## Main results

* `SymplecticGeometry.IsConnectionForm.mpullback_op_smul_gaugeCurvature`: the curvature of a
  connection form is equivariant, `R_g^* F_A = Ad(g⁻¹) ∘ F_A`.
* `SymplecticGeometry.IsConnectionForm.isSemibasic_gaugeCurvature`,
  `SymplecticGeometry.IsConnectionForm.isTensorialForm_gaugeCurvature`: the curvature of a
  connection form vanishes as soon as one of its arguments is vertical, so it is a tensorial form
  of type `Ad`. On a fundamental vector field `ξ^♯`, Cartan's formula and the Lie derivative
  `L_{ξ^♯} A = -[ξ, A]` of `Principal/BasicForm.lean`
  (`TauCeti.PrincipalBundle.mlieDerivForm_rightFundamentalVectorField_apply_eq_neg_lie`) give
  `ι_{ξ^♯} d A = -[ξ, A]`, which the bracket term cancels.

## Implementation notes

The norm on `𝔤` is the scoped one of `SymplecticGeometry.Geometry.Lie.GroupLieAlgebra.Normed`,
and the bracket of `𝔤` needs the local instance `LieGroup.minSmoothness_of_isRCLikeNormedField`;
statements of this file need `open scoped GroupLieAlgebra` and that instance.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §6.3
  (connection forms on principal bundles and their curvature).
* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience, 1963,
  Chapter II, §5 (the curvature form).
-/

public section

noncomputable section

open Bundle Manifold MulOpposite TauCeti TauCeti.Lie VectorField
open scoped Manifold ContDiff GroupLieAlgebra

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

namespace SymplecticGeometry

variable {EG HG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG} [TopologicalSpace G] [ChartedSpace HG G]
  [Group G] [LieGroup IG ∞ G]

/-- **The curvature of a connection form is equivariant**: its pull-back by the action of `g` is
its image under `Ad(g⁻¹)`. -/
theorem IsConnectionForm.mpullback_op_smul_gaugeCurvature {EB HB B : Type*}
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
    {IB : ModelWithCorners ℝ EB HB}
    [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
    {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
    [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
    [ContMDiffFiberBundle ∞ G P IB IG]
    {A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) (GroupLieAlgebra IG G) 1}
    (hA : IsConnectionForm A) (g : G) :
    SmoothForm.mpullback (fun x : ManifoldTotalSpace G P ↦ op g • x)
        (contMDiff_const_smul (op g))
        (gaugeCurvature (lieL ℝ (GroupLieAlgebra IG G) (GroupLieAlgebra IG G)) A) =
      SmoothForm.mapCoeff (adjointContinuousLinearMap g⁻¹)
        (gaugeCurvature (lieL ℝ (GroupLieAlgebra IG G) (GroupLieAlgebra IG G)) A) := by
  rw [mpullback_gaugeCurvature, hA.mpullback_op_smul,
    gaugeCurvature_mapCoeff _ _ _ fun a b ↦ by
      rw [lieL_apply, lieL_apply, adjointContinuousLinearMap_lie]]

section Tensorial

variable {EB HB B : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  [IB.Boundaryless] [IG.Boundaryless]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  [ContMDiffFiberBundle ∞ G P IB IG]
  {A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) (GroupLieAlgebra IG G) 1}

/-- The curvature of a connection form vanishes when its first argument is the value of a
fundamental vector field: by Cartan's formula, `ι_{ξ^♯} d A = -[ξ, A]`, which the bracket
`[A(ξ^♯), A] = [ξ, A]` cancels. -/
theorem IsConnectionForm.gaugeCurvature_apply_rightFundamentalVectorField
    (hA : IsConnectionForm A) (ξ : GroupLieAlgebra IG G) (x : ManifoldTotalSpace G P)
    (w : TangentSpace (IB.prod IG) x) :
    (gaugeCurvature (lieL ℝ (GroupLieAlgebra IG G) (GroupLieAlgebra IG G)) A).val x
      ![rightFundamentalVectorField (IB.prod IG) ξ x, w] = 0 := by
  have hV := (PrincipalBundle.contMDiff_rightFundamentalVectorField (P := P) (IB := IB)
    (m := 1) (n := ∞) (by simp) ξ x).mdifferentiableAt one_ne_zero
  have h := mlieDerivForm_apply_eq_mextDeriv_add (f := fun _ ↦ ξ)
    (fun y ↦ hA.apply_rightFundamentalVectorField y ξ) (A.mdifferentiable x) hV w
  rw [PrincipalBundle.mlieDerivForm_rightFundamentalVectorField_apply_eq_neg_lie
    hA.mpullback_op_smul, mvfderiv_const, zero_apply, add_zero] at h
  rw [gaugeCurvature_val _ (fun a b ↦ by rw [lieL_apply, lieL_apply, lie_skew]), lieL_apply,
    hA.apply_rightFundamentalVectorField, ← h, neg_add_cancel]

/-- **The curvature of a connection form is horizontal**: it is semibasic for the projection,
that is, it vanishes as soon as one of its arguments is vertical. -/
theorem IsConnectionForm.isSemibasic_gaugeCurvature {n : ℕ∞ω} (hA : IsConnectionForm A) :
    RoughForm.IsSemibasic (F := GroupLieAlgebra IG G) IB
      (ManifoldTotalSpace.projContMDiffMap n G P IB IG)
      (gaugeCurvature (lieL ℝ (GroupLieAlgebra IG G) (GroupLieAlgebra IG G)) A).val := by
  refine RoughForm.isSemibasic_def.mpr fun x ↦ RoughForm.isSemibasicAt_def.mpr ?_
  rw [Submodule.mem_conormalForms_fin_two_iff_le_ker, ManifoldTotalSpace.coe_projContMDiffMap,
    ← PrincipalBundle.range_rightFundamentalLinearMap_eq_ker_mfderiv_proj]
  rintro _ ⟨ξ, rfl⟩
  refine LinearMap.mem_ker.mpr (LinearMap.ext fun w ↦ ?_)
  simpa [PrincipalBundle.rightFundamentalLinearMap_apply] using
    hA.gaugeCurvature_apply_rightFundamentalVectorField ξ x w

/-- **The curvature of a connection form is tensorial**: it is an equivariant two-form of type
`Ad` that vanishes as soon as one of its arguments is vertical. -/
theorem IsConnectionForm.isTensorialForm_gaugeCurvature (hA : IsConnectionForm A) :
    IsTensorialForm (gaugeCurvature (lieL ℝ (GroupLieAlgebra IG G) (GroupLieAlgebra IG G)) A) where
  mpullback_op_smul := hA.mpullback_op_smul_gaugeCurvature
  isSemibasic := hA.isSemibasic_gaugeCurvature

end Tensorial

end SymplecticGeometry

end
