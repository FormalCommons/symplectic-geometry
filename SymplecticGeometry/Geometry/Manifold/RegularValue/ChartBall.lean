/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import TauCeti.Geometry.Manifold.RegularValue
import Mathlib.Analysis.Normed.Module.Connected
import SymplecticGeometry.Topology.OpenPartialHomeomorph.Compact
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import TauCeti.Geometry.Manifold.RegularValue.Scalar.DefiningFunction
import TauCeti.Topology.ConnectedComponents
import TauCeti.Topology.OpenPartialHomeomorph.Basic

/-!
# Balls in a chart as regular sublevel sets

Let `M` be a smooth Hausdorff, σ-compact manifold with model `𝓘(ℝ, E)`, where `E` is a real
inner product space of finite dimension, and let `e` be a chart of its smooth maximal atlas
whose target contains the closed ball of radius `ρ > 0` about `c`. Then `e.symm '' closedBall c ρ`
is the sublevel set `{f ≤ 0}` of a smooth function `f : M → ℝ` with regular value `0`, and the
complement of `e.symm '' ball c ρ` is the sublevel set of `-f`. These are the sets to which
Tau Ceti's `TauCeti.isManifold_scalarRegularSublevel` and `TauCeti.boundary_scalarRegularSublevel`
give the structure of a manifold with boundary, the level set being the boundary.

The function `f` is the one that Tau Ceti's
`PartialDiffeomorph.exists_contMDiffMap_regular_definingFunction` gives for `y ↦ ‖y - c‖² - ρ²`
and the inverse of `e`, seen as a partial diffeomorphism. The identification of the three sign
sets of `y ↦ ‖y - c‖² - ρ²` with the closed ball, the open ball and the sphere follows the proof
of Tau Ceti's `PartialDiffeomorph.exists_contMDiffMap_regular_definingFunction_norm_le`.

## Main results

* `SymplecticGeometry.isRegularPoint_norm_sub_sq_sub`: every point other than `c` is a regular
  point of `z ↦ ‖z - c‖² - t` on `E`.
* `OpenPartialHomeomorph.exists_isRegularValue_image_closedBall`: a smooth `f` with regular value
  `0` such that `{f ≤ 0}`, `{f < 0}` and `{f = 0}` are the images under `e.symm` of the closed
  ball, the open ball and the sphere.
* `OpenPartialHomeomorph.exists_isRegularValue_compl_image_ball`: the same with `{g ≤ 0}` the
  complement of `e.symm '' ball c ρ` and `{g < 0}` that of `e.symm '' closedBall c ρ`.
* `OpenPartialHomeomorph.frontier_symm_image_ball`: if `E` is a proper real normed space and
  the closed ball lies in the target, the frontier of `e.symm '' ball c ρ` is the image of the
  sphere.
* `OpenPartialHomeomorph.isPreconnected_compl_symm_image_ball`: if moreover `dim E ≥ 2` and `M`
  is preconnected, the complement of `e.symm '' ball c ρ` is preconnected, since its frontier is
  the image of a sphere (`TauCeti.isPreconnected_compl_of_isPreconnected_frontier`).

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Proposition 5.47 (regular sublevel sets are manifolds with boundary).
-/

public section

open Function Metric Set TauCeti Topology
open scoped Manifold ContDiff

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {c : E}

/-- Every point `y ≠ c` of `E` is a regular point of `z ↦ ‖z - c‖² - t`. -/
theorem isRegularPoint_norm_sub_sq_sub {y : E} (hy : y ≠ c) (t : ℝ) :
    IsRegularPoint 𝓘(ℝ, E) 𝓘(ℝ) (fun z ↦ ‖z - c‖ ^ 2 - t) y := by
  set D : E →L[ℝ] ℝ := 2 • (innerSL ℝ (y - c)).comp (ContinuousLinearMap.id ℝ E)
  have hD : HasFDerivAt (fun z : E ↦ ‖z - c‖ ^ 2) D y := ((hasFDerivAt_id y).sub_const c).norm_sq
  rw [isRegularPoint_iff_surjective_fderiv, fderiv_sub_const, hD.fderiv]
  have hne : D (y - c) ≠ 0 := by
    simp only [D, smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      innerSL_apply_apply, real_inner_self_eq_norm_sq, nsmul_eq_mul, Nat.cast_ofNat]
    have := norm_pos_iff.2 (sub_ne_zero.2 hy)
    positivity
  intro s
  exact ⟨(s / D (y - c)) • (y - c), by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hne]⟩

end SymplecticGeometry

namespace OpenPartialHomeomorph

section Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] {c : E} {ρ : ℝ}
  {M : Type*} [TopologicalSpace M] [T2Space M] (e : OpenPartialHomeomorph M E)

/-- The frontier of the image under `e.symm` of a ball of nonzero radius whose closure lies in the
target of `e` is the image of its bounding sphere. -/
theorem frontier_symm_image_ball (hρ : ρ ≠ 0) (hc : closedBall c ρ ⊆ e.target) :
    frontier (e.symm '' ball c ρ) = e.symm '' sphere c ρ := by
  rw [← closure_ball c hρ] at hc
  rw [e.frontier_symm_image_of_isCompact isOpen_ball
    ((closure_ball c hρ).symm ▸ isCompact_closedBall c ρ) hc, frontier_ball c hρ]

/-- In a preconnected space, the complement of the image under `e.symm` of a ball of nonzero
radius whose closure lies in the target of `e` is preconnected when `dim E ≥ 2`: the image is
open and its frontier is the image of a sphere, which is connected. -/
theorem isPreconnected_compl_symm_image_ball [PreconnectedSpace M] (hE : 1 < Module.rank ℝ E)
    (hρ : ρ ≠ 0) (hc : closedBall c ρ ⊆ e.target) : IsPreconnected (e.symm '' ball c ρ)ᶜ := by
  refine isPreconnected_compl_of_isPreconnected_frontier
    (e.isOpen_image_symm_of_subset_target isOpen_ball (ball_subset_closedBall.trans hc)) ?_
  rw [e.frontier_symm_image_ball hρ hc]
  exact (isPreconnected_sphere hE c ρ).image _
    (e.continuousOn_symm.mono (sphere_subset_closedBall.trans hc))

end Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {c : E} {ρ : ℝ} {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
  (e : OpenPartialHomeomorph M E)

/-- **A closed ball in a chart is a regular sublevel set.** Let `e` be a chart of the smooth
maximal atlas of a Hausdorff, σ-compact manifold modelled on a finite-dimensional inner product
space `E`, and let the closed ball of radius `ρ > 0` about `c` lie in its target. There is a smooth
function `f : M → ℝ` with regular value `0` whose sublevel set `{f ≤ 0}`, strict sublevel set
`{f < 0}` and level set `{f = 0}` are the images under `e.symm` of the closed ball, the open ball
and the sphere of radius `ρ` about `c`. -/
theorem exists_isRegularValue_image_closedBall [SigmaCompactSpace M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (hc : closedBall c ρ ⊆ e.target)
    (hρ : 0 < ρ) :
    ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f ∧ IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f 0 ∧
      {x | f x ≤ 0} = e.symm '' closedBall c ρ ∧ {x | f x < 0} = e.symm '' ball c ρ ∧
      {x | f x = 0} = e.symm '' sphere c ρ := by
  set Φ := (e.toPartialDiffeomorphOfMemMaximalAtlas he).symm
  have hΦ (s : Set E) : Φ '' s = e.symm '' s := by
    congr 1
    funext v
    simp [Φ, PartialDiffeomorph.symm_toPartialEquiv]
  have hsource : Φ.source = e.target := by simp [Φ]
  set h : E → ℝ := fun y ↦ ‖y - c‖ ^ 2 - ρ ^ 2
  have hle : {y | h y ≤ 0} = closedBall c ρ := by
    ext y
    rw [mem_ofPred_eq, mem_closedBall, dist_eq_norm, sub_nonpos, sq_le_sq₀ (norm_nonneg _) hρ.le]
  have hlt : {y | h y < 0} = ball c ρ := by
    ext y
    rw [mem_ofPred_eq, mem_ball, dist_eq_norm, sub_neg, sq_lt_sq₀ (norm_nonneg _) hρ.le]
  have heq : {y | h y = 0} = sphere c ρ := by
    ext y
    rw [mem_ofPred_eq, mem_sphere, dist_eq_norm, sub_eq_zero, sq_eq_sq₀ (norm_nonneg _) hρ.le]
  have hreg (y : E) (hy : h y = 0) : IsRegularPoint 𝓘(ℝ, E) 𝓘(ℝ) h y := by
    refine SymplecticGeometry.isRegularPoint_norm_sub_sq_sub (fun hyc ↦ hρ.ne' ?_) _
    have hy' : y ∈ sphere c ρ := heq ▸ hy
    rwa [hyc, mem_sphere, dist_self, eq_comm] at hy'
  obtain ⟨g, hg, -, hgle, hglt, hgeq⟩ := Φ.exists_contMDiffMap_regular_definingFunction (f := h)
    (((contDiff_id.sub contDiff_const).norm_sq ℝ).sub contDiff_const).contMDiff.contMDiffOn
    (hle ▸ hsource ▸ hc)
    (by rw [hle, hΦ]; exact e.isClosed_image_symm_of_isCompact (isCompact_closedBall c ρ) hc)
    hreg
  exact ⟨g, g.contMDiff, hg, by rw [hgle, hle, hΦ], by rw [hglt, hlt, hΦ], by rw [hgeq, heq, hΦ]⟩

/-- **The complement of a ball in a chart is a regular sublevel set.** Under the hypotheses of
`exists_isRegularValue_image_closedBall`, there is a smooth function `g : M → ℝ` with regular
value `0` whose sublevel set `{g ≤ 0}` is the complement of `e.symm '' ball c ρ`, whose strict
sublevel set `{g < 0}` is the complement of `e.symm '' closedBall c ρ`, and whose level set
`{g = 0}` is `e.symm '' sphere c ρ`. -/
theorem exists_isRegularValue_compl_image_ball [SigmaCompactSpace M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (hc : closedBall c ρ ⊆ e.target)
    (hρ : 0 < ρ) :
    ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ g ∧ IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) g 0 ∧
      {x | g x ≤ 0} = (e.symm '' ball c ρ)ᶜ ∧ {x | g x < 0} = (e.symm '' closedBall c ρ)ᶜ ∧
      {x | g x = 0} = e.symm '' sphere c ρ := by
  obtain ⟨f, hf, hreg, hle, hlt, heq⟩ := e.exists_isRegularValue_image_closedBall he hc hρ
  refine ⟨-f, hf.neg, isRegularValue_neg_iff.2 (by rwa [neg_zero]), ?_, ?_, ?_⟩
  · rw [← hlt]
    ext x
    simp
  · rw [← hle]
    ext x
    simp
  · rw [← heq]
    ext x
    simp

end OpenPartialHomeomorph

end
