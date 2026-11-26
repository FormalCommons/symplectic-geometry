/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.IntegralCurve.Maximal
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.MorseBott
import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.MorseBottFamily
import TauCeti.Geometry.Manifold.Morse.Bott.ExponentialConvergence

/-!
# Gradient flow of a component of a moment map

Let a compact Lie group `G` act on a compact manifold `M`, modelled on `𝓘(ℝ, E')`, with moment
map `μ` for a nondegenerate two-form `σ`, and fix `ξ` in the Lie algebra of `G`. For any `C¹`
Riemannian metric on `M`, every negative gradient trajectory of `x ↦ μ x ξ` converges to a
critical point.

The connected components of the critical set of `x ↦ μ x ξ` form a Morse–Bott family
(`TauCeti.SmoothTwoForm.IsMomentMap.exists_isMorseBottFamily`), and on a compact manifold the
function is proper and bounded below, so this is the theorem
`exists_tendsto_and_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient` of Tau Ceti,
in the namespace `TauCeti.IsMorseBottFamily`. That theorem also gives an exponential rate of
convergence, and the family gives Łojasiewicz's inequality near each critical point
(`TauCeti.IsMorseBottFamily.exists_mul_abs_sub_le_norm_mgradient_sq`).

## Main results

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
  obtain ⟨L, C, -, i, -, -, hi⟩ := h.exists_isMorseBottFamily hσ ξ
  let := C
  have hcont : Continuous fun y ↦ μ y ξ := (h.contMDiff ξ).continuous
  obtain ⟨c, s, hlim, -⟩ :=
    hi.exists_tendsto_and_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient (by simp)
      hcont.isProperMap (isCompact_range hcont).bddBelow x
  exact ⟨i c s, hi.range_subset_criticalPoints c (Set.mem_range_self s), hlim⟩

end TauCeti.SmoothTwoForm.IsMomentMap

end
