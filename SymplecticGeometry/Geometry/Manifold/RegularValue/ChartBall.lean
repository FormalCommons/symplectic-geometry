/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import TauCeti.Geometry.Manifold.RegularValue
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import SymplecticGeometry.Geometry.Manifold.ContMDiff.Indicator
import SymplecticGeometry.Topology.OpenPartialHomeomorph.Compact
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import TauCeti.Topology.ConnectedComponents
import TauCeti.Topology.OpenPartialHomeomorph.Basic

/-!
# Balls in a chart as regular sublevel sets

Let `M` be a smooth Hausdorff manifold with model `𝓘(ℝ, E)`, where `E` is a real
inner product space of finite dimension, and let `e` be a chart of its smooth maximal atlas
whose target contains the closed ball of radius `ρ > 0` about `c`. Then `e.symm '' closedBall c ρ`
is the sublevel set `{f ≤ 0}` of a smooth function `f : M → ℝ` with regular value `0`, and the
complement of `e.symm '' ball c ρ` is the sublevel set of `-f`. These are the sets to which
Tau Ceti's `TauCeti.isManifold_scalarRegularSublevel` and `TauCeti.boundary_scalarRegularSublevel`
give the structure of a manifold with boundary, the level set being the boundary.

The function `f` is `1 + β · (h - 1)` read through `e` on its source and `1` off it, where
`h y = ‖y - c‖² - ρ²` and `β` is a smooth bump function on `E` equal to `1` on a ball slightly
larger than the closed ball and supported in the target of `e`. This adapts the gluing of a
local defining function with the constant `1` in Tau Ceti's
`TauCeti.exists_contMDiffMap_definingFunction`, whose cutoff comes from Mathlib's smooth Urysohn
lemma and so needs `M` to be σ-compact; here the cutoff is built in the chart, and `M` need only
be Hausdorff. The identification of the three sign sets of `y ↦ ‖y - c‖² - ρ²` with the closed
ball, the open ball and the sphere follows the proof of Tau Ceti's
`PartialDiffeomorph.exists_contMDiffMap_regular_definingFunction_norm_le`.

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

/-- The function `y ↦ ‖y - c‖² - ρ²` on `E`, modified away from the closed ball: it agrees with
`‖y - c‖² - ρ²` on a larger ball, is positive outside the closed ball, and differs from `1` only
on a compact subset of the open set `U`. -/
private theorem exists_contDiff_eq_norm_sub_sq_sub {U : Set E} (hU : IsOpen U)
    (hc : closedBall c ρ ⊆ U) (hρ : 0 < ρ) :
    ∃ φ : E → ℝ, ∃ ρ' > ρ, ContDiff ℝ ∞ φ ∧
      (∀ y, ‖y - c‖ < ρ' → φ y = ‖y - c‖ ^ 2 - ρ ^ 2) ∧ (∀ y, ρ < ‖y - c‖ → 0 < φ y) ∧
      HasCompactSupport (fun y ↦ φ y - 1) ∧ tsupport (fun y ↦ φ y - 1) ⊆ U := by
  obtain ⟨δ, hδ, hδc⟩ := (isCompact_closedBall c ρ).exists_cthickening_subset_open hU hc
  rw [cthickening_closedBall hδ.le hρ.le] at hδc
  let β : ContDiffBump c := ⟨ρ + δ / 2, δ + ρ, by positivity, by linarith⟩
  have hpos {y : E} (hy : ρ < ‖y - c‖) : 0 < ‖y - c‖ ^ 2 - ρ ^ 2 :=
    sub_pos.2 (pow_lt_pow_left₀ hy hρ.le two_ne_zero)
  refine ⟨fun y ↦ 1 + β y * (‖y - c‖ ^ 2 - ρ ^ 2 - 1), ρ + δ / 2, by linarith,
    contDiff_const.add (β.contDiff.mul ((((contDiff_id.sub contDiff_const).norm_sq ℝ).sub
      contDiff_const).sub contDiff_const)), fun y hy ↦ ?_, fun y hy ↦ ?_, ?_, ?_⟩
  · beta_reduce
    rw [β.one_of_mem_closedBall (by rw [mem_closedBall, dist_eq_norm]; exact hy.le)]
    ring
  · beta_reduce
    have h0 := mul_nonneg (β.nonneg (x := y)) (hpos hy).le
    rcases (β.le_one (x := y)).lt_or_eq with h1 | h1
    · linarith
    · rw [h1]
      linarith [hpos hy]
  · simp_rw [add_sub_cancel_left]
    exact β.hasCompactSupport.mul_right
  · simp_rw [add_sub_cancel_left]
    exact tsupport_mul_subset_left.trans (β.tsupport_eq ▸ hδc)

/-- **A closed ball in a chart is a regular sublevel set.** Let `e` be a chart of the smooth
maximal atlas of a Hausdorff manifold modelled on a finite-dimensional inner product space `E`,
and let the closed ball of radius `ρ > 0` about `c` lie in its target. There is a smooth function
`f : M → ℝ` with regular value `0` whose sublevel set `{f ≤ 0}`, strict sublevel set `{f < 0}`
and level set `{f = 0}` are the images under `e.symm` of the closed ball, the open ball and the
sphere of radius `ρ` about `c`. -/
theorem exists_isRegularValue_image_closedBall [IsManifold 𝓘(ℝ, E) ∞ M]
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (hc : closedBall c ρ ⊆ e.target)
    (hρ : 0 < ρ) :
    ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f ∧ IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f 0 ∧
      {x | f x ≤ 0} = e.symm '' closedBall c ρ ∧ {x | f x < 0} = e.symm '' ball c ρ ∧
      {x | f x = 0} = e.symm '' sphere c ρ := by
  obtain ⟨φ, ρ', hρ', hφ, hφeq, hφpos, hφc, hφs⟩ :=
    exists_contDiff_eq_norm_sub_sq_sub e.open_target hc hρ
  set f : M → ℝ := 1 + e.source.indicator ((fun y ↦ φ y - 1) ∘ e)
  have hfs (x : M) (hx : x ∈ e.source) : f x = φ (e x) := by
    simp [f, indicator_of_mem hx]
  have hfpos (x : M) (hx : x ∉ e.source ∨ ρ < ‖e x - c‖) : 0 < f x := by
    by_cases hxs : x ∈ e.source
    · rw [hfs x hxs]
      exact hφpos _ (hx.resolve_left (not_not.2 hxs))
    · simp [f, indicator_of_notMem hxs]
  -- Each of the three sets is cut out on the closed ball by a condition on
  -- `‖y - c‖ ^ 2 - ρ ^ 2` that forces it to be nonpositive.
  have hset (P : ℝ → Prop) (hP : ∀ t, P t → t ≤ 0) (T : Set E) (hT : T ⊆ closedBall c ρ)
      (hTP : ∀ y ∈ closedBall c ρ, y ∈ T ↔ P (‖y - c‖ ^ 2 - ρ ^ 2)) :
      {x | P (f x)} = e.symm '' T := by
    rw [e.symm_image_eq_source_inter_preimage (hT.trans hc)]
    ext x
    simp only [mem_ofPred_eq, mem_preimage, mem_inter_iff]
    by_cases hx : x ∈ e.source ∧ ‖e x - c‖ ≤ ρ
    · rw [hfs x hx.1, hφeq _ (hx.2.trans_lt hρ'),
        hTP _ (by rw [mem_closedBall, dist_eq_norm]; exact hx.2)]
      exact ⟨fun h' ↦ ⟨hx.1, h'⟩, fun h' ↦ h'.2⟩
    · rw [not_and_or, not_le] at hx
      refine iff_of_false (fun h' ↦ (hfpos x hx).not_ge (hP _ h')) fun h' ↦ ?_
      have := hT h'.2
      rw [mem_closedBall, dist_eq_norm] at this
      exact hx.elim (· h'.1) this.not_gt
  have hle : {x | f x ≤ 0} = e.symm '' closedBall c ρ := by
    refine hset (· ≤ 0) (fun _ ↦ id) _ subset_rfl fun y hy ↦ iff_of_true hy ?_
    rw [sub_nonpos]
    rw [mem_closedBall, dist_eq_norm] at hy
    exact pow_le_pow_left₀ (norm_nonneg _) hy 2
  have hlt : {x | f x < 0} = e.symm '' ball c ρ := by
    refine hset (· < 0) (fun _ ↦ le_of_lt) _ ball_subset_closedBall fun y _ ↦ ?_
    rw [mem_ball, dist_eq_norm, sub_neg, sq_lt_sq₀ (norm_nonneg _) hρ.le]
  have heq : {x | f x = 0} = e.symm '' sphere c ρ := by
    refine hset (· = 0) (fun _ ↦ le_of_eq) _ sphere_subset_closedBall fun y _ ↦ ?_
    rw [mem_sphere, dist_eq_norm, sub_eq_zero, sq_eq_sq₀ (norm_nonneg _) hρ.le]
  refine ⟨f, contMDiff_const.add (e.contMDiff_indicator_comp he
    (hφ.sub contDiff_const).contMDiff.contMDiffOn hφc hφs), ?_, hle, hlt, heq⟩
  rw [isRegularValue_iff]
  intro x hx
  have hx' : x ∈ e.source ∩ e ⁻¹' sphere c ρ := by
    rw [← e.symm_image_eq_source_inter_preimage (sphere_subset_closedBall.trans hc), ← heq]
    exact hx
  have hxc : ‖e x - c‖ = ρ := by
    have := hx'.2
    rwa [mem_preimage, mem_sphere, dist_eq_norm] at this
  -- Near `x`, `f` is `‖e · - c‖ ^ 2 - ρ ^ 2`, which is regular at `x` since `e` is a local
  -- diffeomorphism and `e x ≠ c`.
  have hev : f =ᶠ[𝓝 x] (fun y ↦ ‖y - c‖ ^ 2 - ρ ^ 2) ∘ e := by
    filter_upwards [(e.continuousOn.isOpen_inter_preimage e.open_source isOpen_ball).mem_nhds
      (show x ∈ e.source ∩ e ⁻¹' ball c ρ' by
        rw [mem_inter_iff, mem_preimage, mem_ball, dist_eq_norm, hxc]
        exact ⟨hx'.1, hρ'⟩)] with z hz
    have hz2 := hz.2
    rw [mem_preimage, mem_ball, dist_eq_norm] at hz2
    rw [hfs z hz.1, Function.comp_apply, hφeq _ hz2]
  have he' : IsRegularPoint 𝓘(ℝ, E) 𝓘(ℝ, E) e x :=
    (e.isLocalDiffeomorphAt_of_mem_maximalAtlas he hx'.1).isRegularPoint (by simp)
  have hreg := (SymplecticGeometry.isRegularPoint_norm_sub_sq_sub (c := c) (y := e x)
    (fun h0 ↦ by rw [h0, sub_self, norm_zero] at hxc; exact hρ.ne' hxc.symm) (ρ ^ 2)).comp he'
  rw [isRegularPoint_iff, hev.mfderiv_eq]
  exact isRegularPoint_iff.1 hreg

/-- **The complement of a ball in a chart is a regular sublevel set.** Under the hypotheses of
`exists_isRegularValue_image_closedBall`, there is a smooth function `g : M → ℝ` with regular
value `0` whose sublevel set `{g ≤ 0}` is the complement of `e.symm '' ball c ρ`, whose strict
sublevel set `{g < 0}` is the complement of `e.symm '' closedBall c ρ`, and whose level set
`{g = 0}` is `e.symm '' sphere c ρ`. -/
theorem exists_isRegularValue_compl_image_ball [IsManifold 𝓘(ℝ, E) ∞ M]
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
