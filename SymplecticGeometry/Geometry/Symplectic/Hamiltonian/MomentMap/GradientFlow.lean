/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.IntegralCurve.Maximal
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.MorseBott
import TauCeti.Geometry.Manifold.Morse.Bott.ExponentialConvergence
import TauCeti.Geometry.Manifold.Morse.ExponentialConvergence
import TauCeti.Geometry.Manifold.Riemannian.Basic

/-!
# Gradient flow of a component of a moment map

Let a compact Lie group `G` act on a σ-compact manifold `M`, modelled on `𝓘(ℝ, E')`, with moment
map `μ` for a nondegenerate two-form `σ`, and fix `ξ` in the Lie algebra of `G`. For any
continuous Riemannian metric on `M`, the component `x ↦ μ x ξ` satisfies Łojasiewicz's gradient
inequality with exponent `1 / 2` near each of its critical points. When `M` is
compact and the metric is `C¹`, every negative gradient trajectory of `x ↦ μ x ξ` therefore
converges to a critical point.

The inequality comes from Tau Ceti: every critical point lies in a set `M^{T_ξ}_d` of fixed points
(`TauCeti.SmoothTwoForm.IsMomentMap.criticalPoints_eq_iUnion_fixedPointsOfFinrank`), which is a
nondegenerate critical submanifold (theorem
`exists_isNondegenerateCriticalSubmanifold_fixedPointsOfFinrank_of_compactSpace` in the same
namespace), near which Morse–Bott functions satisfy the inequality (theorem
`exists_mul_abs_sub_le_norm_mgradient_sq` in the namespace
`TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`). The convergence is then Tau Ceti's
`exists_tendsto_and_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient_of_lojasiewicz`,
in the namespace `TauCeti`.

## Main results

* `TauCeti.SmoothTwoForm.IsMomentMap.exists_mul_abs_sub_le_norm_mgradient_sq`: Łojasiewicz's
  inequality with exponent `1 / 2` for `x ↦ μ x ξ` near each of its critical points.
* `TauCeti.SmoothTwoForm.IsMomentMap.exists_tendsto_maximalIntegralCurve_neg_mgradient`: on a
  compact manifold, the negative gradient trajectories of `x ↦ μ x ξ` converge to critical points.

## References

* [V. Georgoulas, J. W. Robbin and D. A. Salamon, *The Moment-Weight Inequality and the
  Hilbert–Mumford Criterion*][GeorgoulasRobbinSalamon2021].
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §5.7.
-/

public section

namespace TauCeti.SmoothTwoForm.IsMomentMap

open _root_.Bundle _root_.Manifold TauCeti.Manifold Filter Topology
open scoped _root_.Manifold ContDiff

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [T2Space G]
  [IsTopologicalGroup G] [CompactSpace G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {M : Type*} [TopologicalSpace M] [ChartedSpace E' M] [IsManifold 𝓘(ℝ, E') ∞ M] [T2Space M]
  [MulAction G M] [ContMDiffSMul I 𝓘(ℝ, E') ∞ G M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E') x)]
  {σ : SmoothTwoForm 𝓘(ℝ, E') M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}
  {ξ : GroupLieAlgebra I G}

/-- **Łojasiewicz's inequality for a component of a moment map.** For a compact group `G` acting
on a σ-compact manifold with moment map `μ` for a nondegenerate `σ`, and any continuous
Riemannian metric, near each critical point `y` of `x ↦ μ x ξ` there is `lam > 0` with
`lam * |μ z ξ - μ y ξ| ≤ ‖grad ⟨μ, ξ⟩ z‖ ^ 2`. -/
theorem exists_mul_abs_sub_le_norm_mgradient_sq [SigmaCompactSpace M]
    [IsContinuousRiemannianBundle E' (fun x : M ↦ TangentSpace 𝓘(ℝ, E') x)]
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G 𝓘(ℝ, E') M) μ)
    (hσ : σ.IsNondegenerate) {y : M} (hy : y ∈ criticalPoints 𝓘(ℝ, E') fun x ↦ μ x ξ) :
    ∃ lam > 0, ∀ᶠ z in 𝓝 y,
      lam * |μ z ξ - μ y ξ| ≤ ‖mgradient 𝓘(ℝ, E') (fun x ↦ μ x ξ) z‖ ^ 2 := by
  rw [h.criticalPoints_eq_iUnion_fixedPointsOfFinrank hσ ξ, Set.mem_iUnion] at hy
  obtain ⟨d, hd⟩ := hy
  -- The fixed tangent subspace at `y` is a subspace of the model, of dimension `d`.
  obtain ⟨L, hL⟩ : ∃ L : Submodule ℝ E', Module.finrank ℝ L = d :=
    ⟨fixedTangentSubspace 𝓘(ℝ, E') (Lie.closedOneParameterSubgroup ξ) y,
      (mem_fixedPointsOfFinrank.1 hd).2⟩
  obtain ⟨S, -, hi, hnd, -⟩ :=
    h.exists_isNondegenerateCriticalSubmanifold_fixedPointsOfFinrank_of_compactSpace hσ hL
  let := S
  simpa only [SmoothEmbedding.coe_ofIsSmoothEmbedding] using
    hnd.exists_mul_abs_sub_le_norm_mgradient_sq (by simp) ⟨y, hd⟩

/-- **The gradient flow of a component of a moment map converges.** For a compact group `G`
acting on a compact manifold with moment map `μ` for a nondegenerate `σ`, and any `C¹`
Riemannian metric, the maximal integral curve of `-grad ⟨μ, ξ⟩` through `x` converges, as
`t → ∞`, to a critical point of `y ↦ μ y ξ`. -/
theorem exists_tendsto_maximalIntegralCurve_neg_mgradient [CompactSpace M]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, E') 1 E' (fun x : M ↦ TangentSpace 𝓘(ℝ, E') x)]
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G 𝓘(ℝ, E') M) μ)
    (hσ : σ.IsNondegenerate) (ξ : GroupLieAlgebra I G) (x : M) :
    ∃ q ∈ criticalPoints 𝓘(ℝ, E') (fun y ↦ μ y ξ),
      Tendsto (maximalIntegralCurve (-mgradient 𝓘(ℝ, E') fun y ↦ μ y ξ) x) atTop (𝓝 q) := by
  have : IsContinuousRiemannianBundle E' (fun x : M ↦ TangentSpace 𝓘(ℝ, E') x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := 𝓘(ℝ, E')) (n := 1)
  obtain ⟨q, hq, hlim, -⟩ :=
    exists_tendsto_and_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient_of_lojasiewicz
      (x := x) ((h.contMDiff ξ).of_le (by simp)) isCompact_univ (Set.mapsTo_univ _ _)
      fun y hy ↦ h.exists_mul_abs_sub_le_norm_mgradient_sq hσ hy.1
  exact ⟨q, hq.1, hlim⟩

end TauCeti.SmoothTwoForm.IsMomentMap

end
