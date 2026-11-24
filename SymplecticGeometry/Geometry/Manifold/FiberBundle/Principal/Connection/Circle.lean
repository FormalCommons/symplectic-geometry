/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.FiberBundle.Principal.CircleConnection
public import SymplecticGeometry.Geometry.Manifold.FiberBundle.Principal.Connection.Basic

/-!
# Circle connection forms as Lie-algebra-valued connection forms

For `G = Circle`, the Lie algebra `𝔤` of `Circle` is the line spanned by
`SymplecticGeometry.circleLieGenerator`, and the adjoint action is trivial. A real one-form `α` on
the total space of a principal `Circle`-bundle gives the `𝔤`-valued one-form `α ξ₀`, for
`ξ₀ = circleLieGenerator`: its image under `SmoothForm.mapCoeff` along
`ContinuousLinearMap.toSpanSingleton ℝ ξ₀ : ℝ →L[ℝ] 𝔤`. This file shows that the real circle
connection forms of `CircleConnection.lean` (`SymplecticGeometry.IsCircleConnectionForm`) are the
connection forms of `Principal/Connection/Basic.lean` (`SymplecticGeometry.IsConnectionForm`)
under this identification.

## Main results

* `TauCeti.SmoothForm.mapCoeff_injective`: changing the values of forms along an injective
  continuous linear map is injective.
* `SymplecticGeometry.isConnectionForm_mapCoeff_iff`: `α ξ₀` is a connection form exactly when
  `α` is a circle connection form.
* `SymplecticGeometry.IsConnectionForm.existsUnique_eq_mapCoeff`: every `𝔤`-valued connection form
  is `α ξ₀` for a unique real form `α`, and this `α` is a circle connection form.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.7 and §6.3
  (connection forms on circle bundles and on principal bundles).
-/

public section

noncomputable section

open Bundle Manifold MulOpposite TauCeti TauCeti.Lie
open scoped Manifold ContDiff GroupLieAlgebra

namespace TauCeti.SmoothForm

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  {F F' : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F']
  [NormedSpace ℝ F'] {k : ℕ}

/-- Changing the values of smooth forms along an injective continuous linear map is injective. -/
theorem mapCoeff_injective {L : F →L[ℝ] F'} (hL : Function.Injective L) :
    Function.Injective (mapCoeff (I := I) (M := M) (k := k) L) := fun φ ψ h ↦
  SmoothBundleForm.ext fun x v ↦ hL <| by
    simpa only [coe_mapCoeff, RoughForm.mapCoeff_apply] using
      DFunLike.congr_fun (congrFun (congrArg Subtype.val h) x) v

end TauCeti.SmoothForm

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

end SymplecticGeometry

end
