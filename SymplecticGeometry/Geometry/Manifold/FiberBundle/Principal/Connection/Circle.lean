/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.MapCoeff
public import SymplecticGeometry.Geometry.Manifold.FiberBundle.Principal.CircleConnection
public import SymplecticGeometry.Geometry.Manifold.FiberBundle.Principal.Connection.Curvature
public import SymplecticGeometry.Geometry.Manifold.FiberBundle.Principal.Connection.Existence
public import SymplecticGeometry.Topology.VectorBundle.Complex.RestrictScalars
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Hermitian.CircleBundle

/-!
# Circle connection forms as Lie-algebra-valued connection forms

For `G = Circle`, the Lie algebra `𝔤` of `Circle` is the line spanned by
`SymplecticGeometry.circleLieGenerator`, and the adjoint action is trivial. A real one-form `α` on
the total space of a principal `Circle`-bundle gives the `𝔤`-valued one-form `α ξ₀`, for
`ξ₀ = circleLieGenerator`: its image under `SmoothForm.mapCoeff` along
`ContinuousLinearMap.toSpanSingleton ℝ ξ₀ : ℝ →L[ℝ] 𝔤`. This file shows that the real circle
connection forms of `CircleConnection.lean` (`SymplecticGeometry.IsCircleConnectionForm`) are the
connection forms of `Principal/Connection/Basic.lean` (`SymplecticGeometry.IsConnectionForm`)
under this identification, and that their curvatures agree: the curvature
`SymplecticGeometry.connectionCurvature` of `α ξ₀` is the pull-back to the total space of the
curvature `hα.curvature` on the base, times `ξ₀`. In particular, the existence of circle
connection forms follows from that of connection forms.

## Main results

* `SymplecticGeometry.isConnectionForm_mapCoeff_iff`: `α ξ₀` is a connection form exactly when
  `α` is a circle connection form.
* `SymplecticGeometry.IsConnectionForm.existsUnique_eq_mapCoeff`: every `𝔤`-valued connection form
  is `α ξ₀` for a unique real form `α`, and this `α` is a circle connection form.
* `SymplecticGeometry.connectionCurvature_mapCoeff_toSpanSingleton_circleLieGenerator`: for every
  real one-form `α` on a manifold, the curvature of `α ξ₀` is `(dα) ξ₀`; the bracket term of the
  curvature vanishes since `𝔤` is a line.
* `SymplecticGeometry.IsCircleConnectionForm.connectionCurvature_mapCoeff`: for a circle
  connection form `α`, the curvature of `α ξ₀` is the pull-back of `hα.curvature` along the
  projection, times `ξ₀`.
* `SymplecticGeometry.exists_isCircleConnectionForm`: every principal `Circle`-bundle over a
  Hausdorff, σ-compact, finite-dimensional base has a circle connection form, the case
  `G = Circle` of `SymplecticGeometry.exists_isConnectionForm`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.7 and §6.3
  (connection forms on circle bundles and on principal bundles).
-/

public section

noncomputable section

open Bundle Manifold MulOpposite TauCeti TauCeti.Lie
open scoped Manifold ContDiff GroupLieAlgebra

namespace SymplecticGeometry

variable {EB HB B : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  {P : B → Type*} [TopologicalSpace (TotalSpace Circle P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle Circle P] [∀ b, MulAction Circleᵐᵒᵖ (P b)] [PrincipalBundle Circle P]
  [ContMDiffFiberBundle ∞ Circle P IB (𝓡 1)]

/-- **Circle connection forms are connection forms.** For a real one-form `α` on the total space
of a principal `Circle`-bundle, the `𝔤`-valued form `α ξ₀`, with `ξ₀ = circleLieGenerator`, is a
connection form exactly when `α` is a circle connection form. -/
theorem isConnectionForm_mapCoeff_iff
    {α : SmoothForm (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1} :
    IsConnectionForm
        (SmoothForm.mapCoeff (ContinuousLinearMap.toSpanSingleton ℝ circleLieGenerator) α) ↔
      IsCircleConnectionForm α := by
  have hinj := SmoothForm.mapCoeff_injective (I := IB.prod (𝓡 1))
    (M := ManifoldTotalSpace Circle P) (k := 1)
    (L := ContinuousLinearMap.toSpanSingleton ℝ circleLieGenerator) fun a b h ↦
      smul_left_injective ℝ circleLieGenerator_ne_zero <| by
        simpa only [ContinuousLinearMap.toSpanSingleton_apply] using h
  have hpull (z : Circle) :
      (SmoothForm.mpullback (fun x : ManifoldTotalSpace Circle P ↦ op z • x)
        (contMDiff_const_smul (op z))
        (SmoothForm.mapCoeff (ContinuousLinearMap.toSpanSingleton ℝ circleLieGenerator) α) =
        SmoothForm.mapCoeff (adjointContinuousLinearMap z⁻¹)
          (SmoothForm.mapCoeff (ContinuousLinearMap.toSpanSingleton ℝ circleLieGenerator) α)) ↔
      SmoothForm.mpullback (fun x : ManifoldTotalSpace Circle P ↦ op z • x)
        (contMDiff_const_smul (op z)) α = α := by
    rw [SmoothForm.mpullback_mapCoeff, adjointContinuousLinearMap_eq_id, SmoothForm.mapCoeff_id,
      LinearMap.id_apply, hinj.eq_iff]
  have hval (x : ManifoldTotalSpace Circle P) (ξ : GroupLieAlgebra (𝓡 1) Circle) :
      (SmoothForm.mapCoeff (ContinuousLinearMap.toSpanSingleton ℝ circleLieGenerator) α).val x
        ![rightFundamentalVectorField (IB.prod (𝓡 1)) ξ x] =
        α.val x ![rightFundamentalVectorField (IB.prod (𝓡 1)) ξ x] • circleLieGenerator := by
    rw [SmoothForm.coe_mapCoeff, RoughForm.mapCoeff_apply,
      ContinuousLinearMap.toSpanSingleton_apply]
  refine ⟨fun hA ↦ ⟨fun z ↦ (hpull z).mp (hA.mpullback_op_smul z), fun x ↦ ?_⟩,
    fun hα ↦ ⟨fun g ↦ (hpull g).mpr (hα.mpullback_op_smul g), fun x ξ ↦ ?_⟩⟩
  · refine smul_left_injective ℝ circleLieGenerator_ne_zero ?_
    simp only [one_smul]
    rw [← hval, hA.apply_rightFundamentalVectorField]
  · obtain ⟨c, rfl⟩ := exists_smul_circleLieGenerator_eq ξ
    rw [hval, rightFundamentalVectorField_smul, Pi.smul_apply,
      ContinuousAlternatingMap.vecCons_smul, hα.apply_rightFundamentalVectorField, smul_eq_mul,
      mul_one]

/-- Every `𝔤`-valued connection form `A` on a principal `Circle`-bundle is `α ξ₀`, for
`ξ₀ = circleLieGenerator`, for a unique real one-form `α`, and `α` is a circle connection form. -/
theorem IsConnectionForm.existsUnique_eq_mapCoeff
    {A : SmoothForm (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) (GroupLieAlgebra (𝓡 1) Circle)
      1} (hA : IsConnectionForm A) :
    ∃! α : SmoothForm (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1,
      IsCircleConnectionForm α ∧
        A = SmoothForm.mapCoeff (ContinuousLinearMap.toSpanSingleton ℝ circleLieGenerator) α := by
  obtain ⟨f, hf⟩ := SeparatingDual.exists_eq_one (R := ℝ) circleLieGenerator_ne_zero
  have hLf : (ContinuousLinearMap.toSpanSingleton ℝ circleLieGenerator).comp f =
      ContinuousLinearMap.id ℝ (GroupLieAlgebra (𝓡 1) Circle) := by
    ext ξ
    obtain ⟨c, rfl⟩ := exists_smul_circleLieGenerator_eq ξ
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, map_smul, hf,
      smul_eq_mul, mul_one, ContinuousLinearMap.id_apply]
  have hfL : f.comp (ContinuousLinearMap.toSpanSingleton ℝ circleLieGenerator) =
      ContinuousLinearMap.id ℝ ℝ := by
    ext
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, map_smul, hf,
      smul_eq_mul, mul_one, ContinuousLinearMap.id_apply]
  have hA' : A = SmoothForm.mapCoeff (ContinuousLinearMap.toSpanSingleton ℝ circleLieGenerator)
      (SmoothForm.mapCoeff f A) := by
    rw [← LinearMap.comp_apply, ← SmoothForm.mapCoeff_comp, hLf, SmoothForm.mapCoeff_id,
      LinearMap.id_apply]
  refine ⟨SmoothForm.mapCoeff f A, ⟨isConnectionForm_mapCoeff_iff.mp (hA' ▸ hA), hA'⟩,
    fun α hα ↦ ?_⟩
  rw [hα.2, ← LinearMap.comp_apply, ← SmoothForm.mapCoeff_comp, hfL, SmoothForm.mapCoeff_id,
    LinearMap.id_apply]

/-- The curvature of the `𝔤`-valued form `α ξ₀`, for a real one-form `α` on any manifold and
`ξ₀ = circleLieGenerator`, is `(dα) ξ₀`: the bracket term `½ [A ∧ A]` vanishes since `𝔤` is
spanned by `ξ₀`. -/
theorem connectionCurvature_mapCoeff_toSpanSingleton_circleLieGenerator
    {EM HM M : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
    {IM : ModelWithCorners ℝ EM HM} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ∞ M]
    (α : SmoothForm IM M ℝ 1) :
    connectionCurvature
        (SmoothForm.mapCoeff (ContinuousLinearMap.toSpanSingleton ℝ circleLieGenerator) α) =
      SmoothForm.mapCoeff (ContinuousLinearMap.toSpanSingleton ℝ circleLieGenerator)
        (mextDerivₗ IM 1 α) := by
  have hwedge : SmoothForm.wedgeWith
      (lieL ℝ (GroupLieAlgebra (𝓡 1) Circle) (GroupLieAlgebra (𝓡 1) Circle))
      (SmoothForm.mapCoeff (ContinuousLinearMap.toSpanSingleton ℝ circleLieGenerator) α)
      (SmoothForm.mapCoeff (ContinuousLinearMap.toSpanSingleton ℝ circleLieGenerator) α) = 0 := by
    rw [← SmoothForm.mapCoeff_wedgeWith (ContinuousLinearMap.mul ℝ ℝ) _ _ _ 0
      fun a b ↦ by simp]
    ext x v
    simp [SmoothForm.coe_mapCoeff, RoughForm.mapCoeff_apply]
  rw [connectionCurvature_def, hwedge, smul_zero, add_zero, SmoothForm.mextDerivₗ_mapCoeff]

/-- **The curvature of a circle connection form.** For a circle connection form `α` on a
principal `Circle`-bundle over a boundaryless base, the curvature of the `𝔤`-valued form `α ξ₀`,
with `ξ₀ = circleLieGenerator`, is `(π^* hα.curvature) ξ₀`, where `π` is the projection to the
base: the bracket term `½ [A ∧ A]` vanishes since `𝔤` is spanned by `ξ₀`. -/
theorem IsCircleConnectionForm.connectionCurvature_mapCoeff [IB.Boundaryless]
    {α : SmoothForm (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1}
    (hα : IsCircleConnectionForm α) :
    connectionCurvature
        (SmoothForm.mapCoeff (ContinuousLinearMap.toSpanSingleton ℝ circleLieGenerator) α) =
      SmoothForm.mapCoeff (ContinuousLinearMap.toSpanSingleton ℝ circleLieGenerator)
        (SmoothForm.mpullback (fun y : ManifoldTotalSpace Circle P ↦
            ((ManifoldTotalSpace.homeomorph Circle P).symm y).proj)
          (ManifoldTotalSpace.contMDiff_proj ∞ Circle P IB (𝓡 1)) hα.curvature) := by
  rw [connectionCurvature_mapCoeff_toSpanSingleton_circleLieGenerator, hα.mpullback_curvature]

/-! ### Existence -/

/-- **Existence of connection forms.** Every smooth principal `Circle`-bundle over a Hausdorff,
σ-compact, finite-dimensional base has a circle connection form. -/
theorem exists_isCircleConnectionForm [FiniteDimensional ℝ EB] [T2Space B]
    [SigmaCompactSpace B] :
    ∃ α : SmoothForm (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1,
      IsCircleConnectionForm α :=
  let ⟨_, hA⟩ := exists_isConnectionForm (IB := IB) (IG := 𝓡 1) (G := Circle) (P := P)
  hA.existsUnique_eq_mapCoeff.exists.imp fun _ h ↦ h.1

/-! ### The circle bundle of a Hermitian line bundle -/

section CircleBundle

open Module TauCeti.OrthonormalFrameBundle

attribute [local instance] finrank_real_complex_fact'

variable {E' H' M F : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I : ModelWithCorners ℝ E' H'} [TopologicalSpace M] [ChartedSpace H' M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [Fact (finrank ℂ F = 1)]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℂ F V]

open scoped VectorBundle.ComplexToReal

/-- The unit circle bundle of a smooth Hermitian line bundle over a Hausdorff, σ-compact,
finite-dimensional manifold has a connection form. -/
example [ContMDiffVectorBundle ∞ F V I] (g : ContMDiffRiemannianMetric I ∞ F V)
    (hI : ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w) :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
    letI : IsContinuousRiemannianBundle F V :=
      instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
    haveI : ContMDiffFiberBundle ∞ Circle (Fiber ℂ F V ℂ) I (𝓡 1) :=
      Bundle.contMDiffFiberBundle_circleFiber g hI
    ∃ α : SmoothForm (I.prod (𝓡 1)) (ManifoldTotalSpace Circle (Fiber ℂ F V ℂ)) ℝ 1,
      IsCircleConnectionForm α := by
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
  let : IsContinuousRiemannianBundle F V :=
    instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  have : ContMDiffFiberBundle ∞ Circle (Fiber ℂ F V ℂ) I (𝓡 1) :=
    Bundle.contMDiffFiberBundle_circleFiber g hI
  exact exists_isCircleConnectionForm

end CircleBundle

end SymplecticGeometry

end
