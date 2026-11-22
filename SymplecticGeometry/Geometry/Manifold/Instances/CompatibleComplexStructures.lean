/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.Immersion
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import SymplecticGeometry.Analysis.Calculus.FDeriv.Cayley
public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.Basic.FromTauCeti
public import SymplecticGeometry.LinearAlgebra.Symplectic.CompatibleTangent.Finrank
public import SymplecticGeometry.Topology.ComplexStructure.Basic
public import SymplecticGeometry.Topology.ComplexStructure.Compatible.Cayley
public import TauCeti.Geometry.Manifold.Immersion.Differential
public import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
public import TauCeti.Geometry.Symplectic.Cayley.Tangent

/-!
# The manifold of compatible complex structures

Let `ω` be a symplectic form on a finite-dimensional real normed space `V`, and write `𝒥 ω` for
Tau Ceti's space `{J : AlmostComplexStructure V // ω.Compatible J}` of `ω`-compatible complex
structures, with the operator-norm topology. This file makes `𝒥 ω` a smooth manifold, modelled on
`ω.compatibleModel`, the compatible tangent space at the base point `ω.compatibleBase`. Tau Ceti's
compatible Cayley transform at the base point is a bijection of all of `𝒥 ω` onto an open subset
of the model, so it is the one chart of an atlas (`TauCeti.SymplecticForm.cayleyChart`).

The inclusion `ω.compatibleCLM` into the continuous endomorphisms `V →L[ℝ] V` reads, in the chart,
`C ↦ J₀ (1 + C) (1 - C)⁻¹`, whose derivative at `C` is `Ċ ↦ 2 J₀ (1 - C)⁻¹ Ċ (1 - C)⁻¹`. This
derivative is injective, and its image is Tau Ceti's compatible tangent space at the point:
it lies there because derivatives of families of compatible structures do
(`TauCeti.SymplecticForm.mem_compatibleTangentSpace_of_hasFDerivAt`), and both spaces have
dimension `n (n + 1)` when `V` has dimension `2 n`. So `𝒥 ω` is a smooth submanifold of
`V →L[ℝ] V` with these tangent spaces. A linear symplectomorphism `Ψ` acts on `𝒥 ω` by
`J ↦ Ψ J Ψ⁻¹`, through Tau Ceti's `AlmostComplexStructure.transport`; read in `V →L[ℝ] V` this is a
continuous linear map, so the action is by diffeomorphisms, and it is transitive.

The layout follows `SymplecticGeometry/Geometry/Manifold/Instances/LagrangianGrassmannian.lean`.

## Main definitions and results

* `TauCeti.SymplecticForm.compatibleCLM`: the inclusion of `𝒥 ω` into `V →L[ℝ] V`.
* `TauCeti.SymplecticForm.cayleyChart`: the global Cayley chart, with values in
  `ω.compatibleModel`.
* The `ChartedSpace ω.compatibleModel (𝒥 ω)` instance, whose chart is `cayleyChart`
  (`chartAt_eq`), and the `IsManifold 𝓘(ℝ, ω.compatibleModel) n (𝒥 ω)` instance.
* `TauCeti.SymplecticForm.hasMFDerivAt_compatibleCLM_chartAt_symm`: the derivative of the
  inclusion in the chart.
* `TauCeti.SymplecticForm.range_mfderiv_compatibleCLM`: the tangent spaces are Tau Ceti's
  compatible tangent spaces, and `TauCeti.SymplecticForm.compatibleTangentEquiv` is the
  differential of the inclusion onto them.
* `TauCeti.SymplecticForm.isSmoothEmbedding_compatibleCLM`: the inclusion is a smooth embedding,
  so a map into `𝒥 ω` is smooth exactly when its composite with it is
  (`contMDiff_compatibleCLM_comp_iff`, `contMDiffAt_compatibleCLM_comp_iff`).
* `TauCeti.SymplecticForm.finrank_compatibleModel`: `𝒥 ω` has dimension `n (n + 1)` when `V` has
  dimension `2 n`.
* `TauCeti.SymplecticForm.compatibleTransport`: the diffeomorphism `J ↦ Ψ J Ψ⁻¹` of a linear
  symplectomorphism `Ψ`, with `mfderiv_compatibleCLM_compatibleTransport` and the transitivity
  `exists_compatibleTransport_eq`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third
  edition][McDuffSalamon2017], §2.5 (the Cayley transform) and Example 4.3.6.
-/

public section

open scoped Manifold
open Topology

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V}

local notation "𝒥" => {J : AlmostComplexStructure V // ω.Compatible J}

/- Smoothness of every finite order. The scope `ContDiff` would give this notation, but also the
notation `ω` for the analytic order, which clashes with the symplectic form. -/
local notation "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-! ### The inclusion into the continuous endomorphisms -/

variable (ω) in
/-- The inclusion of the `ω`-compatible complex structures into the continuous endomorphisms
`V →L[ℝ] V`. -/
noncomputable def compatibleCLM (J : 𝒥) : V →L[ℝ] V :=
  LinearMap.toContinuousLinearMap J.val.toLinearMap

theorem compatibleCLM_def (J : 𝒥) :
    ω.compatibleCLM J = LinearMap.toContinuousLinearMap J.val.toLinearMap :=
  (rfl)

@[simp]
theorem compatibleCLM_apply (J : 𝒥) (v : V) : ω.compatibleCLM J v = J.val v :=
  (rfl)

@[simp]
theorem toLinearMap_compatibleCLM (J : 𝒥) :
    (ω.compatibleCLM J).toLinearMap = J.val.toLinearMap :=
  (rfl)

/-- The inclusion into the continuous endomorphisms is a topological embedding. -/
theorem isEmbedding_compatibleCLM : IsEmbedding ω.compatibleCLM :=
  AlmostComplexStructure.isEmbedding_toContinuousLinearMap.comp IsEmbedding.subtypeVal

/-- A complex structure is invertible in the continuous endomorphisms, with inverse `-J`. -/
theorem isUnit_compatibleCLM (J : 𝒥) : IsUnit (ω.compatibleCLM J) := by
  rw [compatibleCLM_def]
  exact J.val.isUnit_toContinuousLinearMap

/-- A complex structure squares to `-1` in the continuous endomorphisms. -/
@[simp]
theorem compatibleCLM_mul_self (J : 𝒥) : ω.compatibleCLM J * ω.compatibleCLM J = -1 := by
  rw [compatibleCLM_def]
  exact J.val.toContinuousLinearMap_mul_self

/-! ### The global Cayley chart -/

variable (ω) in
/-- The global Cayley chart: the Cayley coordinates at the base point `ω.compatibleBase`, with
values in the model space `ω.compatibleModel`. -/
noncomputable def cayleyChart (J : 𝒥) : ω.compatibleModel :=
  Homeomorph.setCongr (congrArg SetLike.coe ω.compatibleModel_def.symm)
    (ω.compatibleBase.property.cayleyCoord J)

@[simp]
theorem coe_cayleyChart (J : 𝒥) :
    (ω.cayleyChart J : V →L[ℝ] V) = ω.compatibleBase.property.cayleyCoord J :=
  (rfl)

/-- The global Cayley chart is an open embedding into the model space. -/
theorem isOpenEmbedding_cayleyChart : IsOpenEmbedding ω.cayleyChart :=
  (Homeomorph.setCongr (congrArg SetLike.coe ω.compatibleModel_def.symm)).isOpenEmbedding.comp
    ω.compatibleBase.property.isOpenEmbedding_cayleyCoord

/-! ### The manifold structure -/

instance : Nonempty 𝒥 :=
  ⟨ω.compatibleBase⟩

/-- The `ω`-compatible complex structures form a topological manifold modelled on
`ω.compatibleModel`, with the global Cayley chart as its one chart. -/
noncomputable instance : ChartedSpace ω.compatibleModel 𝒥 :=
  ω.isOpenEmbedding_cayleyChart.singletonChartedSpace

/-- The chart at any point is the global Cayley chart. -/
theorem chartAt_eq (J : 𝒥) : ⇑(chartAt ω.compatibleModel J) = ω.cayleyChart :=
  ω.isOpenEmbedding_cayleyChart.singletonChartedSpace_chartAt_eq

/-- The chart is defined on all of the space. -/
theorem chartAt_source (J : 𝒥) : (chartAt ω.compatibleModel J).source = Set.univ :=
  ω.isOpenEmbedding_cayleyChart.toOpenPartialHomeomorph_source

/-- The target of the chart is the range of the global Cayley chart. -/
theorem chartAt_target (J : 𝒥) :
    (chartAt ω.compatibleModel J).target = Set.range ω.cayleyChart :=
  ω.isOpenEmbedding_cayleyChart.toOpenPartialHomeomorph_target

/-- On the target of the chart, the inverse of the chart is the inverse Cayley transform
`C ↦ J₀ (1 + C) (1 - C)⁻¹`, `J₀` being the base point. -/
theorem compatibleCLM_chartAt_symm_apply {J : 𝒥} {C : ω.compatibleModel}
    (hC : C ∈ (chartAt ω.compatibleModel J).target) :
    ω.compatibleCLM ((chartAt ω.compatibleModel J).symm C) =
      ω.compatibleCLM ω.compatibleBase * (1 + (C : V →L[ℝ] V)) *
        Ring.inverse (1 - (C : V →L[ℝ] V)) := by
  rw [compatibleCLM_def, compatibleCLM_def]
  refine ω.compatibleBase.property.toContinuousLinearMap_eq_of_cayleyCoord_eq ?_
  rw [← coe_cayleyChart, ← chartAt_eq J, (chartAt ω.compatibleModel J).right_inv hC]

/-- In Cayley coordinates, `J` is `J₀ (1 + C) (1 - C)⁻¹` for its coordinate `C`, `J₀` being the
base point. -/
theorem compatibleCLM_eq_cayleyChart (J : 𝒥) :
    ω.compatibleCLM J = ω.compatibleCLM ω.compatibleBase * (1 + (ω.cayleyChart J : V →L[ℝ] V)) *
      Ring.inverse (1 - (ω.cayleyChart J : V →L[ℝ] V)) := by
  rw [compatibleCLM_def, compatibleCLM_def]
  exact ω.compatibleBase.property.toContinuousLinearMap_eq_of_cayleyCoord_eq
    (coe_cayleyChart J).symm

/-- **The compatible complex structures form a smooth manifold**, modelled on
`ω.compatibleModel` through the global Cayley chart. -/
instance {n : WithTop ℕ∞} : IsManifold 𝓘(ℝ, ω.compatibleModel) n 𝒥 :=
  ω.isOpenEmbedding_cayleyChart.isManifold_singleton

/-- The global Cayley chart is smooth. -/
theorem contMDiff_cayleyChart {n : WithTop ℕ∞} :
    ContMDiff 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, ω.compatibleModel) n ω.cayleyChart := by
  have h := contMDiffOn_chart (I := 𝓘(ℝ, ω.compatibleModel)) (n := n) (x := ω.compatibleBase)
  rwa [chartAt_source, contMDiffOn_univ, chartAt_eq] at h

/-- The inclusion into the continuous endomorphisms is smooth. -/
theorem contMDiff_compatibleCLM {n : WithTop ℕ∞} :
    ContMDiff 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) n ω.compatibleCLM := by
  rw [show ω.compatibleCLM = fun J : 𝒥 => LinearMap.toContinuousLinearMap J.val.toLinearMap from
    funext compatibleCLM_def]
  refine ω.compatibleBase.property.contMDiff_of_contMDiff_cayley (J := Subtype.val)
    (fun J => J.property.tames)
    ((ω.compatibleModel.subtypeL.contMDiff.comp contMDiff_cayleyChart).congr fun J => ?_)
  simp

/-! ### The differential of the inclusion -/

/-- A point of the chart's target has `1 - C` invertible. -/
theorem isUnit_one_sub_of_mem_chartAt_target {J : 𝒥} {C : ω.compatibleModel}
    (hC : C ∈ (chartAt ω.compatibleModel J).target) : IsUnit (1 - (C : V →L[ℝ] V)) := by
  rw [chartAt_target] at hC
  obtain ⟨J', rfl⟩ := hC
  rw [coe_cayleyChart]
  exact isUnit_one_sub_of_toLinearMap_mem_cayleyBall (compatibleCayleyBall_subset_cayleyBall
    (ω.compatibleBase.property.cayleyCoord_mem_compatibleCayleyBall J'))

/-- At a point `C` of the chart's target, the inclusion into the continuous endomorphisms, read
in the global Cayley chart, has derivative `Ċ ↦ 2 J₀ (1 - C)⁻¹ Ċ (1 - C)⁻¹`, `J₀` being the base
point. See `hasMFDerivAt_compatibleCLM_chartAt_symm` for the same statement with manifold
derivatives. -/
theorem hasFDerivAt_compatibleCLM_chartAt_symm {J : 𝒥} {C : ω.compatibleModel}
    (hC : C ∈ (chartAt ω.compatibleModel J).target) :
    HasFDerivAt (ω.compatibleCLM ∘ (chartAt ω.compatibleModel J).symm)
      ((2 : ℝ) • (ContinuousLinearMap.mulLeftRight ℝ (V →L[ℝ] V)
        (ω.compatibleCLM ω.compatibleBase * Ring.inverse (1 - (C : V →L[ℝ] V)))
        (Ring.inverse (1 - (C : V →L[ℝ] V)))).comp ω.compatibleModel.subtypeL) C := by
  have hG := SymplecticGeometry.hasFDerivAt_mul_one_add_ringInverse (𝕜 := ℝ)
    (ω.compatibleCLM ω.compatibleBase) (isUnit_one_sub_of_mem_chartAt_target hC)
  refine (hG.comp (f := ω.compatibleModel.subtypeL) C
    ω.compatibleModel.subtypeL.hasFDerivAt).congr_of_eventuallyEq ?_
  filter_upwards [(chartAt ω.compatibleModel J).open_target.mem_nhds hC] with C' hC'
  exact compatibleCLM_chartAt_symm_apply hC'

/-- **The differential in the chart.** At a point `C` of the chart's target, the inclusion into
the continuous endomorphisms, read in the global Cayley chart, has derivative
`Ċ ↦ 2 J₀ (1 - C)⁻¹ Ċ (1 - C)⁻¹`, `J₀` being the base point. -/
theorem hasMFDerivAt_compatibleCLM_chartAt_symm {J : 𝒥} {C : ω.compatibleModel}
    (hC : C ∈ (chartAt ω.compatibleModel J).target) :
    HasMFDerivAt 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V)
      (ω.compatibleCLM ∘ (chartAt ω.compatibleModel J).symm) C
      ((2 : ℝ) • (ContinuousLinearMap.mulLeftRight ℝ (V →L[ℝ] V)
        (ω.compatibleCLM ω.compatibleBase * Ring.inverse (1 - (C : V →L[ℝ] V)))
        (Ring.inverse (1 - (C : V →L[ℝ] V)))).comp ω.compatibleModel.subtypeL) :=
  hasMFDerivAt_iff_hasFDerivAt.2 (hasFDerivAt_compatibleCLM_chartAt_symm hC)

/-- Every point of the global Cayley chart lies in the target of the chart. -/
theorem cayleyChart_mem_chartAt_target (J J' : 𝒥) :
    ω.cayleyChart J' ∈ (chartAt ω.compatibleModel J).target := by
  rw [chartAt_target]
  exact Set.mem_range_self J'

/-- **The differential of the inclusion.** At `J`, with Cayley coordinate `C`, the differential of
the inclusion into the continuous endomorphisms is `Ċ ↦ 2 J₀ (1 - C)⁻¹ Ċ (1 - C)⁻¹`, `J₀` being
the base point. -/
theorem hasMFDerivAt_compatibleCLM (J : 𝒥) :
    HasMFDerivAt 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J
      ((2 : ℝ) • (ContinuousLinearMap.mulLeftRight ℝ (V →L[ℝ] V)
        (ω.compatibleCLM ω.compatibleBase * Ring.inverse (1 - (ω.cayleyChart J : V →L[ℝ] V)))
        (Ring.inverse (1 - (ω.cayleyChart J : V →L[ℝ] V)))).comp ω.compatibleModel.subtypeL) :=
  TauCeti.Manifold.hasMFDerivAt_of_hasFDerivWithinAt_extChartAt_target (by simp)
    ω.isEmbedding_compatibleCLM.continuous.continuousAt
    (hasFDerivAt_compatibleCLM_chartAt_symm
      (cayleyChart_mem_chartAt_target J J)).hasFDerivWithinAt
    (fun C _ => by simp [writtenInExtChartAt])

/-- The differential of the inclusion at `J`, with Cayley coordinate `C`, sends `Ċ` to
`2 J₀ (1 - C)⁻¹ Ċ (1 - C)⁻¹`, `J₀` being the base point. -/
theorem mfderiv_compatibleCLM_apply (J : 𝒥) (a : ω.compatibleModel) :
    mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J a =
      (2 : ℝ) • (ω.compatibleCLM ω.compatibleBase *
        Ring.inverse (1 - (ω.cayleyChart J : V →L[ℝ] V)) * (a : V →L[ℝ] V) *
          Ring.inverse (1 - (ω.cayleyChart J : V →L[ℝ] V))) := by
  rw [(hasMFDerivAt_compatibleCLM J).mfderiv]
  -- `a` is now read as a tangent vector, so the computation is made for a vector of the model.
  have h (b : ω.compatibleModel) : ((2 : ℝ) • (ContinuousLinearMap.mulLeftRight ℝ (V →L[ℝ] V)
      (ω.compatibleCLM ω.compatibleBase * Ring.inverse (1 - (ω.cayleyChart J : V →L[ℝ] V)))
      (Ring.inverse (1 - (ω.cayleyChart J : V →L[ℝ] V)))).comp ω.compatibleModel.subtypeL) b =
      (2 : ℝ) • (ω.compatibleCLM ω.compatibleBase *
        Ring.inverse (1 - (ω.cayleyChart J : V →L[ℝ] V)) * (b : V →L[ℝ] V) *
          Ring.inverse (1 - (ω.cayleyChart J : V →L[ℝ] V))) := by
    simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.mulLeftRight_apply, Submodule.subtypeL_apply]
  exact h a

/-- The differential of the inclusion into the continuous endomorphisms is injective. -/
theorem injective_mfderiv_compatibleCLM (J : 𝒥) :
    Function.Injective (mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J) := by
  refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
  have hR :=
    (isUnit_one_sub_of_mem_chartAt_target (cayleyChart_mem_chartAt_target J J)).ringInverse
  have h : (2 : ℝ) • (_ : V →L[ℝ] V) = 0 := (mfderiv_compatibleCLM_apply J a).symm.trans ha
  rw [smul_eq_zero, hR.mul_left_eq_zero,
    ((isUnit_compatibleCLM _).mul hR).mul_right_eq_zero] at h
  exact Subtype.ext (h.resolve_left two_ne_zero)

/-- The differential of the inclusion at `J` takes values in Tau Ceti's compatible tangent space
at `J`, read in the continuous endomorphisms. -/
theorem mfderiv_compatibleCLM_mem (J : 𝒥) (a : ω.compatibleModel) :
    mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J a ∈
      ω.compatibleTangentSpaceCLM J.val := by
  let e := chartAt ω.compatibleModel J
  -- The inclusion read in the chart is a differentiable family of compatible structures, so its
  -- derivatives are compatible tangent vectors.
  have h := hasFDerivAt_compatibleCLM_chartAt_symm (cayleyChart_mem_chartAt_target J J)
  have hmem := mem_compatibleTangentSpace_of_hasFDerivAt (J := fun C => (e.symm C).val)
    (Filter.Eventually.of_forall fun C => (e.symm C).property.invariant)
    (by simpa only [Function.comp_def, compatibleCLM_def] using h) a
  rw [← chartAt_eq J, e.left_inv (by simp [e])] at hmem
  -- The goal is stated in the tangent space of `V →L[ℝ] V`, so the formula for the differential
  -- is substituted through `congrArg` rather than rewritten.
  refine (congrArg (· ∈ ω.compatibleTangentSpaceCLM J.val)
    (mfderiv_compatibleCLM_apply J a)).mpr ?_
  rw [chartAt_eq] at hmem
  rw [mem_compatibleTangentSpaceCLM]
  convert hmem using 2
  simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mulLeftRight_apply, Submodule.subtypeL_apply, compatibleCLM_def]

/-- The ambient reading of a tangent vector at `J` is in Tau Ceti's compatible tangent space at
`J`. -/
theorem mfderiv_compatibleCLM_mem_compatibleTangentSpace (J : 𝒥)
    (a : TangentSpace 𝓘(ℝ, ω.compatibleModel) J) :
    ContinuousLinearMap.toLinearMap
      (mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J a) ∈
        ω.compatibleTangentSpace J.val :=
  mem_compatibleTangentSpaceCLM.1 (mfderiv_compatibleCLM_mem J a)

/-- The ambient reading of a tangent vector at `J` is in the tangent space at `J` of the
almost complex structures: it anticommutes with `J`. -/
theorem mfderiv_compatibleCLM_mem_tangentSpace (J : 𝒥)
    (a : TangentSpace 𝓘(ℝ, ω.compatibleModel) J) :
    ContinuousLinearMap.toLinearMap
      (mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J a) ∈
        J.val.tangentSpace :=
  compatibleTangentSpace_le_tangentSpace (mfderiv_compatibleCLM_mem_compatibleTangentSpace J a)

/-- An endomorphism in the tangent space at `J` anticommutes with `J`. -/
theorem compatibleCLM_comp_add_comp_compatibleCLM (J : 𝒥) {X : V →L[ℝ] V}
    (hX : (X : Module.End ℝ V) ∈ J.val.tangentSpace) :
    ω.compatibleCLM J ∘L X + X ∘L ω.compatibleCLM J = 0 := by
  rw [AlmostComplexStructure.mem_tangentSpace] at hX
  apply ContinuousLinearMap.coe_injective
  rw [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def,
    ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_mul,
    ContinuousLinearMap.toLinearMap_mul, toLinearMap_compatibleCLM, add_comm, hX,
    ContinuousLinearMap.toLinearMap_zero]

/-- The ambient reading `X` of a tangent vector at `J` anticommutes with `J`:
`J ∘ X + X ∘ J = 0`. -/
theorem compatibleCLM_comp_mfderiv_add_mfderiv_comp_compatibleCLM (J : 𝒥)
    (a : TangentSpace 𝓘(ℝ, ω.compatibleModel) J) :
    ω.compatibleCLM J ∘L
        mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J a +
      mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J a ∘L
        ω.compatibleCLM J = 0 :=
  compatibleCLM_comp_add_comp_compatibleCLM J (mfderiv_compatibleCLM_mem_tangentSpace J a)

/-- The model space has dimension `n (n + 1)` when `V` has dimension `2 n`. -/
theorem finrank_compatibleModel {n : ℕ} (hn : Module.finrank ℝ V = 2 * n) :
    Module.finrank ℝ ω.compatibleModel = n * (n + 1) := by
  rw [compatibleModel_def, finrank_compatibleTangentSpaceCLM,
    ω.compatibleBase.property.finrank_compatibleTangentSpace hn]

/-- The model space and the compatible tangent space at any `J` have the same dimension. -/
theorem finrank_compatibleModel_eq (J : 𝒥) :
    Module.finrank ℝ ω.compatibleModel =
      Module.finrank ℝ (ω.compatibleTangentSpaceCLM J.val) := by
  obtain ⟨n, hn⟩ := ω.even_finrank
  rw [finrank_compatibleModel (n := n) (by omega), finrank_compatibleTangentSpaceCLM,
    J.property.finrank_compatibleTangentSpace (n := n) (by omega)]

variable (ω) in
/-- The differential of the inclusion at `J`, as an isomorphism of the tangent space at `J` onto
Tau Ceti's compatible tangent space at `J`, read in the continuous endomorphisms. -/
noncomputable def compatibleTangentEquiv (J : 𝒥) :
    TangentSpace 𝓘(ℝ, ω.compatibleModel) J ≃L[ℝ] ω.compatibleTangentSpaceCLM J.val :=
  let f := LinearMap.codRestrict (ω.compatibleTangentSpaceCLM J.val)
    (mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J).toLinearMap
    (mfderiv_compatibleCLM_mem J)
  have hf : Function.Injective f := fun _ _ h =>
    injective_mfderiv_compatibleCLM J (congrArg Subtype.val h)
  (LinearEquiv.ofBijective f ⟨hf, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (finrank_compatibleModel_eq J)).1 hf⟩).toContinuousLinearEquiv

@[simp]
theorem coe_compatibleTangentEquiv_apply (J : 𝒥) (a : TangentSpace 𝓘(ℝ, ω.compatibleModel) J) :
    (ω.compatibleTangentEquiv J a : V →L[ℝ] V) =
      mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J a :=
  (rfl)

/-- **The tangent spaces.** The differential of the inclusion at `J` has image Tau Ceti's
compatible tangent space at `J`, read in the continuous endomorphisms. -/
theorem range_mfderiv_compatibleCLM (J : 𝒥) :
    LinearMap.range
      (mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J).toLinearMap =
      ω.compatibleTangentSpaceCLM J.val := by
  ext X
  refine ⟨fun ⟨a, ha⟩ => ha ▸ mfderiv_compatibleCLM_mem J a,
    fun hX => ⟨(ω.compatibleTangentEquiv J).symm ⟨X, hX⟩, ?_⟩⟩
  have h := congrArg Subtype.val ((ω.compatibleTangentEquiv J).apply_symm_apply ⟨X, hX⟩)
  rwa [coe_compatibleTangentEquiv_apply] at h

/-! ### The smooth embedding -/

/-- **The compatible complex structures form a submanifold** of the continuous endomorphisms:
the inclusion is a `C^n` embedding for every `n`. -/
theorem isSmoothEmbedding_compatibleCLM {n : WithTop ℕ∞} :
    Manifold.IsSmoothEmbedding 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) n ω.compatibleCLM :=
  (⟨contMDiff_compatibleCLM.isImmersion_of_injective_mfderiv le_top
    injective_mfderiv_compatibleCLM, ω.isEmbedding_compatibleCLM⟩ :
    Manifold.IsSmoothEmbedding _ _ ⊤ _).of_le le_top

section Comp

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- A map into the compatible complex structures is `C^n` exactly when it is `C^n` as a map into
the continuous endomorphisms. -/
theorem contMDiff_compatibleCLM_comp_iff {n : WithTop ℕ∞} {f : M → 𝒥} :
    ContMDiff I 𝓘(ℝ, ω.compatibleModel) n f ↔
      ContMDiff I 𝓘(ℝ, V →L[ℝ] V) n (ω.compatibleCLM ∘ f) :=
  isSmoothEmbedding_compatibleCLM.contMDiff_iff_comp

/-- A map into the compatible complex structures is `C^n` at `x` exactly when it is `C^n` at `x`
as a map into the continuous endomorphisms. -/
theorem contMDiffAt_compatibleCLM_comp_iff {n : WithTop ℕ∞} {f : M → 𝒥} {x : M} :
    ContMDiffAt I 𝓘(ℝ, ω.compatibleModel) n f x ↔
      ContMDiffAt I 𝓘(ℝ, V →L[ℝ] V) n (ω.compatibleCLM ∘ f) x :=
  isSmoothEmbedding_compatibleCLM.contMDiffAt_iff_comp

end Comp

/-! ### Transport by linear symplectomorphisms -/

section Transport

variable {Ψ : V ≃L[ℝ] V}

variable (ω) in
/-- A linear symplectomorphism `Ψ` of `(V, ω)` acts on the `ω`-compatible complex structures by
`J ↦ Ψ J Ψ⁻¹` (Tau Ceti's `AlmostComplexStructure.transport`), and this action is a
diffeomorphism. -/
noncomputable def compatibleTransport (hΨ : ω.IsSymplectomorphism ω Ψ.toLinearEquiv) :
    Diffeomorph 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, ω.compatibleModel) 𝒥 𝒥 ∞ where
  toFun J := ⟨J.val.transport Ψ.toLinearEquiv, (hΨ.compatible_transport_iff J.val).2 J.property⟩
  invFun J := ⟨J.val.transport Ψ.toLinearEquiv.symm,
    (hΨ.symm.compatible_transport_iff J.val).2 J.property⟩
  left_inv J := Subtype.ext (J.val.transport_symm_transport _)
  right_inv J := Subtype.ext (J.val.transport_transport_symm _)
  contMDiff_toFun := contMDiff_compatibleCLM_comp_iff.2 <|
    (((Ψ.arrowCongr Ψ : (V →L[ℝ] V) →L[ℝ] V →L[ℝ] V)).contMDiff.comp
      contMDiff_compatibleCLM).congr fun J => by
      ext v
      simp [compatibleCLM_def]
  contMDiff_invFun := contMDiff_compatibleCLM_comp_iff.2 <|
    (((Ψ.symm.arrowCongr Ψ.symm : (V →L[ℝ] V) →L[ℝ] V →L[ℝ] V)).contMDiff.comp
      contMDiff_compatibleCLM).congr fun J => by
      ext v
      simp [compatibleCLM_def]

variable (hΨ : ω.IsSymplectomorphism ω Ψ.toLinearEquiv)

@[simp]
theorem compatibleTransport_apply_coe (J : 𝒥) :
    (ω.compatibleTransport hΨ J).val = J.val.transport Ψ.toLinearEquiv :=
  (rfl)

@[simp]
theorem compatibleTransport_symm_apply_coe (J : 𝒥) :
    ((ω.compatibleTransport hΨ).symm J).val = J.val.transport Ψ.toLinearEquiv.symm :=
  (rfl)

/-- Read in the continuous endomorphisms, the transport by `Ψ` is the conjugation
`A ↦ Ψ A Ψ⁻¹`. -/
theorem compatibleCLM_compatibleTransport (J : 𝒥) :
    ω.compatibleCLM (ω.compatibleTransport hΨ J) = Ψ.arrowCongr Ψ (ω.compatibleCLM J) := by
  ext v
  simp

/-- The differential of the transport by `Ψ`, read in the continuous endomorphisms, is the
conjugation `Ĵ ↦ Ψ Ĵ Ψ⁻¹`. -/
theorem mfderiv_compatibleCLM_compatibleTransport (J : 𝒥)
    (a : TangentSpace 𝓘(ℝ, ω.compatibleModel) J) :
    mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM (ω.compatibleTransport hΨ J)
        (mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, ω.compatibleModel) (ω.compatibleTransport hΨ) J a) =
      Ψ.arrowCongr Ψ (mfderiv 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J a) := by
  have hcomp : ω.compatibleCLM ∘ ω.compatibleTransport hΨ = Ψ.arrowCongr Ψ ∘ ω.compatibleCLM :=
    funext (compatibleCLM_compatibleTransport hΨ)
  have h1 := mfderiv_comp J ((contMDiff_compatibleCLM (n := 1)).mdifferentiableAt one_ne_zero)
    ((ω.compatibleTransport hΨ).mdifferentiable (by simp) J)
  have h2 := mfderiv_comp J (Ψ.arrowCongr Ψ).mdifferentiableAt
    ((contMDiff_compatibleCLM (n := 1)).mdifferentiableAt one_ne_zero (x := J))
  rw [hcomp, h2, ContinuousLinearEquiv.mfderiv_eq] at h1
  exact (congrArg (fun L => L a) h1).symm

/-- **Transitivity.** The linear symplectomorphisms act transitively on the `ω`-compatible
complex structures. -/
theorem exists_compatibleTransport_eq (J J' : 𝒥) :
    ∃ (Ψ : V ≃L[ℝ] V) (hΨ : ω.IsSymplectomorphism ω Ψ.toLinearEquiv),
      ω.compatibleTransport hΨ J = J' := by
  obtain ⟨Ψ, hΨ, hΨJ⟩ := J.property.exists_isSymplectomorphism_transport_eq J'.property
  refine ⟨Ψ.toContinuousLinearEquiv, by rwa [LinearEquiv.toLinearEquiv_toContinuousLinearEquiv],
    Subtype.ext ?_⟩
  rw [compatibleTransport_apply_coe, LinearEquiv.toLinearEquiv_toContinuousLinearEquiv, hΨJ]

end Transport

end TauCeti.SymplecticForm

end
