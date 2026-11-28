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
  point if and only if the linear maps of its values are; `contMDiffOn_iff_toEuclideanCLM` is the
  same on an open set.
* `Matrix.SymplecticGroup.exists_contMDiffOn_toEuclideanCLM_eq`: a family of linear maps that is
  smooth on an open set and symplectic there comes from a map into the group, smooth there.
* `Matrix.SymplecticGroup.contMDiffAt_iff_coe`: the same for the matrices themselves, with the
  operator norm on matrices. That the inclusion into the matrices is smooth is Tau Ceti's
  `TauCeti.Lie.contMDiff_val_symplecticGroup`.

## Implementation notes

The group is smoothly embedded in `GL (κ ⊕ κ) ℝ` (Tau Ceti's
`TauCeti.Lie.isSmoothEmbedding_ofSymplecticGroup`), so a map into it is smooth if and only if it is
continuous and its composite with the embedding is smooth (Mathlib's
`ContMDiffAt.iff_comp_isImmersionAt`). The charts of the open set `GL (κ ⊕ κ) ℝ` of the matrices
are restrictions of the identity (`Units.chartAt_apply`), and a matrix and its linear map
determine each other linearly (`Matrix.toEuclideanCLM`).

Only that embedding is used, so `contMDiffAt_iff_coe`, `contMDiffAt_iff_toEuclideanCLM` and
`contMDiffOn_iff_toEuclideanCLM` are cases of a general fact about smooth embeddings. Tau Ceti
has its global form, `Manifold.IsSmoothEmbedding.contMDiff_iff_comp`, but not its forms at a point
and on a set, which are what this file needs. Those belong upstream, next to it in Tau Ceti's
`Geometry/Manifold/SmoothEmbedding/Basic.lean` or in `Geometry/Lie/Subgroup/Embedded.lean`.

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

/-- A map into the symplectic group is smooth at `x` if and only if its matrices are. -/
theorem contMDiffAt_iff_coe {f : X → symplecticGroup κ ℝ} {x : X} :
    ContMDiffAt I 𝓘(ℝ, TauCeti.Lie.SymplecticGroupModel κ ℝ) ∞ f x ↔
      ContMDiffAt I 𝓘(ℝ, Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ) ∞
        (fun y ↦ (f y : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ)) x := by
  refine ⟨fun hf ↦ (TauCeti.Lie.contMDiff_val_symplecticGroup κ ℝ).contMDiffAt.comp x hf,
    fun hf ↦ ?_⟩
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
    (TauCeti.Lie.contMDiff_val_symplecticGroup κ ℝ)

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

/-- On an open set `s`, a map `f` into `Matrix.symplecticGroup κ ℝ` is smooth if and only if the
endomorphisms `Matrix.toEuclideanCLM (f y)` of `EuclideanSpace ℝ (κ ⊕ κ)` depend smoothly on
`y ∈ s`. -/
theorem contMDiffOn_iff_toEuclideanCLM {f : X → symplecticGroup κ ℝ} {s : Set X}
    (hs : IsOpen s) :
    ContMDiffOn I 𝓘(ℝ, TauCeti.Lie.SymplecticGroupModel κ ℝ) ∞ f s ↔
      ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (κ ⊕ κ) →L[ℝ] EuclideanSpace ℝ (κ ⊕ κ)) ∞
        (fun y ↦ toEuclideanCLM (𝕜 := ℝ) (f y : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ)) s :=
  ⟨fun hf _ hx ↦ (contMDiffAt_iff_toEuclideanCLM.1 (hf.contMDiffAt (hs.mem_nhds hx)))
      |>.contMDiffWithinAt,
    fun hf _ hx ↦ (contMDiffAt_iff_toEuclideanCLM.2 (hf.contMDiffAt (hs.mem_nhds hx)))
      |>.contMDiffWithinAt⟩

/-- A family `D` of endomorphisms of `EuclideanSpace ℝ (κ ⊕ κ)` that is smooth on an open set `s`
and whose matrices are symplectic on `s` is, on `s`, the family of linear maps of a map `C` into
the symplectic group that is smooth on `s`. -/
theorem exists_contMDiffOn_toEuclideanCLM_eq {s : Set X} (hs : IsOpen s)
    {D : X → EuclideanSpace ℝ (κ ⊕ κ) →L[ℝ] EuclideanSpace ℝ (κ ⊕ κ)}
    (hD : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (κ ⊕ κ) →L[ℝ] EuclideanSpace ℝ (κ ⊕ κ)) ∞ D s)
    (hDs : ∀ x ∈ s, (toEuclideanCLM (n := κ ⊕ κ) (𝕜 := ℝ)).symm (D x) ∈ symplecticGroup κ ℝ) :
    ∃ C : X → symplecticGroup κ ℝ,
      ContMDiffOn I 𝓘(ℝ, TauCeti.Lie.SymplecticGroupModel κ ℝ) ∞ C s ∧
        ∀ x ∈ s, toEuclideanCLM (𝕜 := ℝ) (C x : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ) = D x := by
  classical
  let C (x : X) : symplecticGroup κ ℝ := if hx : x ∈ s then ⟨_, hDs x hx⟩ else 1
  have hC (x : X) (hx : x ∈ s) :
      toEuclideanCLM (𝕜 := ℝ) (C x : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ) = D x := by
    simp only [C, hx, dite_true, StarAlgEquiv.apply_symm_apply]
  exact ⟨C, (contMDiffOn_iff_toEuclideanCLM hs).2 (hD.congr hC), hC⟩

end Matrix.SymplecticGroup

end
