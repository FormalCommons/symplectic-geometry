/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import TauCeti.Geometry.Manifold.Instances.SymplecticGroup
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra

/-!
# Smooth maps into the symplectic group

Tau Ceti makes Mathlib's group `Matrix.symplecticGroup κ ℝ` of real symplectic matrices a Lie
group, with charts modelled on its Lie algebra (`Geometry/Manifold/Instances/SymplecticGroup.lean`).
This file says when a map into it is smooth: exactly when the endomorphisms of
`EuclideanSpace ℝ (κ ⊕ κ)` that its matrices define (`Matrix.toEuclideanCLM`) depend smoothly on
the point. So smoothness of maps into the group can be checked, and used, through the linear maps
of the matrices, without the norm on matrices that the charts are built with.

## Main results

* `Matrix.SymplecticGroup.contMDiff_toEuclideanCLM`: the linear map of a symplectic matrix depends
  smoothly on the point of the group.
* `Matrix.SymplecticGroup.contMDiffAt_iff_toEuclideanCLM`: a map into the group is smooth at a
  point if and only if the linear maps of its values are.
* `Matrix.SymplecticGroup.contMDiff_coe`, `Matrix.SymplecticGroup.contMDiffAt_iff_coe`: the same
  for the matrices themselves, with the operator norm on matrices.

## Implementation notes

The group is smoothly embedded in `GL (κ ⊕ κ) ℝ` (Tau Ceti's
`TauCeti.Lie.isSmoothEmbedding_ofSymplecticGroup`), so a map into it is smooth if and only if it is
continuous and its composite with the embedding is smooth (Mathlib's
`ContMDiffAt.iff_comp_isImmersionAt`). The charts of the open set `GL (κ ⊕ κ) ℝ` of the matrices
are restrictions of the identity (`Units.chartAt_apply`), and a matrix and its linear map
determine each other linearly (`Matrix.toEuclideanCLM`).

Tau Ceti states its charts for the topology of the operator norm on matrices
(`Matrix.linftyOpTopologicalSpace`), which is the product topology
(`Matrix.linftyOpTopologicalSpace_eq`) but not reducibly so. This file does the same, so a proof
that uses its results makes that topology a local instance first.
-/

public section

open scoped Manifold ContDiff Matrix.Norms.Operator

attribute [local instance] Matrix.linftyOpTopologicalSpace

namespace Matrix.SymplecticGroup

variable {κ : Type*} [Fintype κ] [DecidableEq κ]
  {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X]

/-- The inclusion of the symplectic group into the matrices is smooth. -/
theorem contMDiff_coe :
    ContMDiff 𝓘(ℝ, TauCeti.Lie.SymplecticGroupModel κ ℝ) 𝓘(ℝ, Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ) ∞
      (fun A : symplecticGroup κ ℝ ↦ (A : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ)) := by
  refine ((Units.contMDiff_val (𝕜 := ℝ) (R := Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ) (n := ∞)).comp
    (TauCeti.Lie.symplecticGroupToGLSmoothHom κ ℝ).contMDiff_toFun).congr fun A ↦ ?_
  have h := congrArg Units.val (TauCeti.Lie.symplecticGroupToGLSmoothHom_apply κ ℝ A)
  rw [TauCeti.GLSymplectic.coe_ofSymplecticGroup] at h
  exact h.symm

/-- A map into the symplectic group is smooth at `x` if and only if its matrices are. -/
theorem contMDiffAt_iff_coe {f : X → symplecticGroup κ ℝ} {x : X} :
    ContMDiffAt I 𝓘(ℝ, TauCeti.Lie.SymplecticGroupModel κ ℝ) ∞ f x ↔
      ContMDiffAt I 𝓘(ℝ, Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ) ∞
        (fun y ↦ (f y : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ)) x := by
  refine ⟨fun hf ↦ (contMDiff_coe (κ := κ)).contMDiffAt.comp x hf, fun hf ↦ ?_⟩
  have hc : ContinuousAt f x :=
    Topology.IsInducing.subtypeVal.continuousAt_iff.2 hf.continuousAt
  rw [ContMDiffAt.iff_comp_isImmersionAt
    ((TauCeti.Lie.isSmoothEmbedding_ofSymplecticGroup κ ℝ).isImmersion.isImmersionAt (f x))]
  refine ⟨hc, ?_⟩
  rw [contMDiffAt_iff_target]
  refine ⟨(TauCeti.GLSymplectic.continuous_ofSymplecticGroup κ ℝ).continuousAt.comp hc, ?_⟩
  simpa [Function.comp_def, Units.chartAt_apply] using hf

/-- The linear map `Matrix.toEuclideanCLM A` of a symplectic matrix `A` depends smoothly on the
point `A` of the symplectic group. -/
theorem contMDiff_toEuclideanCLM :
    ContMDiff 𝓘(ℝ, TauCeti.Lie.SymplecticGroupModel κ ℝ)
      𝓘(ℝ, EuclideanSpace ℝ (κ ⊕ κ) →L[ℝ] EuclideanSpace ℝ (κ ⊕ κ)) ∞
      (fun A : symplecticGroup κ ℝ ↦ toEuclideanCLM (𝕜 := ℝ) (A : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ)) :=
  (LinearMap.toContinuousLinearMap
    (toEuclideanCLM (n := κ ⊕ κ) (𝕜 := ℝ)).toAlgEquiv.toLinearMap).contDiff.contMDiff.comp
    contMDiff_coe

/-- **Smooth maps into the symplectic group.** A map `f` into `Matrix.symplecticGroup κ ℝ` is
smooth at `x` if and only if the endomorphisms `Matrix.toEuclideanCLM (f y)` of
`EuclideanSpace ℝ (κ ⊕ κ)` depend smoothly on `y` at `x`. -/
theorem contMDiffAt_iff_toEuclideanCLM {f : X → symplecticGroup κ ℝ} {x : X} :
    ContMDiffAt I 𝓘(ℝ, TauCeti.Lie.SymplecticGroupModel κ ℝ) ∞ f x ↔
      ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (κ ⊕ κ) →L[ℝ] EuclideanSpace ℝ (κ ⊕ κ)) ∞
        (fun y ↦ toEuclideanCLM (𝕜 := ℝ) (f y : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ)) x := by
  refine ⟨fun hf ↦ (contMDiff_toEuclideanCLM (κ := κ)).contMDiffAt.comp x hf, fun hf ↦ ?_⟩
  refine contMDiffAt_iff_coe.2 ?_
  refine ((LinearMap.toContinuousLinearMap
    (toEuclideanCLM (n := κ ⊕ κ) (𝕜 := ℝ)).symm.toAlgEquiv.toLinearMap).contDiff.contMDiff
    |>.contMDiffAt.comp x hf).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ ?_)
  exact ((toEuclideanCLM (n := κ ⊕ κ) (𝕜 := ℝ)).symm_apply_apply _).symm

end Matrix.SymplecticGroup

end
