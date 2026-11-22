/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue
public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.DiscComplement.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.Connected
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart
import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import TauCeti.Geometry.Manifold.RegularValue.Scalar.DefiningFunction
import TauCeti.Topology.ConnectedComponents

/-!
# Balls in a chart as regular sublevel sets

Let `M` be a smooth Hausdorff, σ-compact manifold with model `𝓘(ℝ, E)`, where `E` is a real
inner product space of finite dimension, and let `e` be a chart of its smooth maximal atlas
whose target contains the closed ball of radius `ρ > 0` about `c`. Then `e.symm '' closedBall c ρ`
is the sublevel set `{f ≤ 0}` of a smooth function `f : M → ℝ` with regular value `0`, and the
complement of `e.symm '' ball c ρ` is the sublevel set of `-f`. These are the sets to which
Tau Ceti's `TauCeti.isManifold_scalarRegularSublevel` and `TauCeti.boundary_scalarRegularSublevel`
give the structure of a manifold with boundary, the level set being the boundary.

On the source of `e` the function `x ↦ ‖e x - c‖² - ρ²` is a local defining function for the
closed ball image: its derivative is that of `y ↦ ‖y - c‖²` composed with the invertible
derivative of `e`, and does not vanish off `e.symm c`. Tau Ceti's
`TauCeti.exists_contMDiffMap_regular_definingFunction` extends it to all of `M`.

## Main results

* `SymplecticGeometry.isRegularPoint_norm_sub_sq_sub`: every point other than `c` is a regular
  point of `z ↦ ‖z - c‖² - t` on `E`.
* `OpenPartialHomeomorph.exists_isRegularValue_image_closedBall`: a smooth `f` with regular value
  `0` such that `{f ≤ 0}`, `{f < 0}` and `{f = 0}` are the images under `e.symm` of the closed
  ball, the open ball and the sphere.
* `OpenPartialHomeomorph.exists_isRegularValue_compl_image_ball`: the same with `{g ≤ 0}` the
  complement of `e.symm '' ball c ρ` and `{g < 0}` that of `e.symm '' closedBall c ρ`.
* `OpenPartialHomeomorph.closure_image_symm_ball` and
  `OpenPartialHomeomorph.frontier_image_symm_ball`: if the closed ball lies in the target, the
  closure and the frontier of `e.symm '' ball c ρ` are the images of the closed ball and of the
  sphere.
* `OpenPartialHomeomorph.isPreconnected_compl_image_ball`: if `dim E ≥ 2` and `M` is
  preconnected, the complement of `e.symm '' ball c ρ` is preconnected, since its frontier is the
  image of a sphere (`TauCeti.isPreconnected_compl_of_isPreconnected_frontier`).
* `SymplecticGeometry.CoordinateDisc.exists_isRegularValue_disc_subset_ofChart` and
  `SymplecticGeometry.CoordinateDisc.exists_isRegularValue_discComplement_subset_ofChart`: for
  the coordinate disc `CoordinateDisc.ofChart` of a chart of a surface, there is a regular
  sublevel set with nonempty boundary that is connected and contains the closed disc in its
  interior, and another that contains the complement of the open disc in its interior and is
  connected when `M` is.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Proposition 5.47 (regular sublevel sets are manifolds with boundary).
-/

public section

open Function Metric Set TauCeti Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {c : E}

namespace SymplecticGeometry

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

variable {M : Type*} [TopologicalSpace M] (e : OpenPartialHomeomorph M E)

variable [ChartedSpace E M] [FiniteDimensional ℝ E] [T2Space M] {ρ : ℝ}

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
  set h : E → ℝ := fun y ↦ ‖y - c‖ ^ 2 - ρ ^ 2
  -- The points of the source where a condition on `h ∘ e` holds that cuts out `S` in the target.
  have hset {p : ℝ → Prop} {S : Set E} (hS : S ⊆ e.target) (hpS : ∀ y, p (h y) ↔ y ∈ S) :
      {x | x ∈ e.source ∧ p ((h ∘ e) x)} = e.symm '' S := by
    rw [e.symm_image_eq_source_inter_preimage hS]
    ext x
    simp [hpS]
  have hle (y : E) : h y ≤ 0 ↔ y ∈ closedBall c ρ := by
    rw [mem_closedBall, dist_eq_norm, sub_nonpos, sq_le_sq₀ (norm_nonneg _) hρ.le]
  have hlt (y : E) : h y < 0 ↔ y ∈ ball c ρ := by
    rw [mem_ball, dist_eq_norm, sub_neg, sq_lt_sq₀ (norm_nonneg _) hρ.le]
  have heq (y : E) : h y = 0 ↔ y ∈ sphere c ρ := by
    rw [mem_sphere, dist_eq_norm, sub_eq_zero, sq_eq_sq₀ (norm_nonneg _) hρ.le]
  have hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞ (h ∘ e) e.source :=
    (((contDiff_id.sub contDiff_const).norm_sq ℝ).sub contDiff_const).contMDiff.comp_contMDiffOn
      (contMDiffOn_of_mem_maximalAtlas he)
  have hs : IsClosed {x | x ∈ e.source ∧ (h ∘ e) x ≤ 0} := by
    rw [hset (p := (· ≤ 0)) hc hle]
    exact ((isCompact_closedBall c ρ).image_of_continuousOn
      (e.continuousOn_symm.mono hc)).isClosed
  have hreg (x : M) (hx : x ∈ e.source) (hx₀ : (h ∘ e) x = 0) :
      IsRegularPoint 𝓘(ℝ, E) 𝓘(ℝ) (h ∘ e) x := by
    have hxc : e x ≠ c := by
      rintro hxc
      rw [comp_apply, heq, hxc, mem_sphere, dist_self] at hx₀
      exact hρ.ne hx₀
    have he₁ : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M :=
      IsManifold.maximalAtlas_subset_of_le (by simp) he
    exact (SymplecticGeometry.isRegularPoint_norm_sub_sq_sub hxc _).comp
      (isRegularPoint_iff.2 (isInvertible_mfderiv_chart he₁ hx).surjective)
  obtain ⟨g, hg, -, hgle, hglt, hgeq⟩ :=
    exists_contMDiffMap_regular_definingFunction (n := ⊤) e.open_source hf hs hreg
  refine ⟨g, g.contMDiff, hg, ?_, ?_, ?_⟩
  · rw [← hset (p := (· ≤ 0)) hc hle]
    exact ext hgle
  · rw [← hset (p := (· < 0)) (ball_subset_closedBall.trans hc) hlt]
    exact ext hglt
  · rw [← hset (p := (· = 0)) (sphere_subset_closedBall.trans hc) heq]
    exact ext hgeq

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

omit [ChartedSpace E M] in
/-- The closure of the image under `e.symm` of a ball of nonzero radius whose closure lies in the
target of `e` is the image of the closed ball. -/
theorem closure_image_symm_ball (hρ : ρ ≠ 0) (hc : closedBall c ρ ⊆ e.target) :
    closure (e.symm '' ball c ρ) = e.symm '' closedBall c ρ := by
  refine subset_antisymm (closure_minimal (image_mono ball_subset_closedBall)
    ((isCompact_closedBall c ρ).image_of_continuousOn (e.continuousOn_symm.mono hc)).isClosed) ?_
  rintro _ ⟨y, hy, rfl⟩
  exact mem_closure_image (e.continuousAt_symm (hc hy)) (by rwa [closure_ball c hρ])

omit [ChartedSpace E M] in
/-- The frontier of the image under `e.symm` of a ball of nonzero radius whose closure lies in the
target of `e` is the image of its bounding sphere. -/
theorem frontier_image_symm_ball (hρ : ρ ≠ 0) (hc : closedBall c ρ ⊆ e.target) :
    frontier (e.symm '' ball c ρ) = e.symm '' sphere c ρ := by
  have hU := e.isOpen_image_symm_of_subset_target isOpen_ball (ball_subset_closedBall.trans hc)
  rw [frontier, e.closure_image_symm_ball hρ hc, hU.interior_eq,
    ← (e.symm.injOn.mono hc).image_sdiff_subset ball_subset_closedBall, closedBall_sdiff_ball]

omit [ChartedSpace E M] in
/-- In a preconnected space, the complement of the image under `e.symm` of a ball of nonzero
radius whose closure lies in the target of `e` is preconnected when `dim E ≥ 2`: the image is
open and its frontier is the image of a sphere, which is connected. -/
theorem isPreconnected_compl_image_ball [PreconnectedSpace M] (hE : 1 < Module.rank ℝ E)
    (hρ : ρ ≠ 0) (hc : closedBall c ρ ⊆ e.target) : IsPreconnected (e.symm '' ball c ρ)ᶜ := by
  refine isPreconnected_compl_of_isPreconnected_frontier
    (e.isOpen_image_symm_of_subset_target isOpen_ball (ball_subset_closedBall.trans hc)) ?_
  rw [e.frontier_image_symm_ball hρ hc]
  exact (isPreconnected_sphere hE c ρ).image _
    (e.continuousOn_symm.mono (sphere_subset_closedBall.trans hc))

end OpenPartialHomeomorph

namespace SymplecticGeometry.CoordinateDisc

variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M] [SigmaCompactSpace M]
  {o : Manifold.Orientation (𝓡 2) M (Fin 2)}
  {e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))}
  {c : EuclideanSpace ℝ (Fin 2)} {r : ℝ}

/-- **A regular sublevel set around a coordinate disc.** Let `e` be a chart of the smooth
maximal atlas of a Hausdorff, σ-compact smooth surface `M`, and `CoordinateDisc.ofChart e hr hc he`
the coordinate disc it gives. There is a smooth function `f : M → ℝ` with regular value `0` such
that the closed disc lies in `{f < 0}`, the sublevel set `{f ≤ 0}` is connected and the level set
`{f = 0}` is nonempty. -/
theorem exists_isRegularValue_disc_subset_ofChart
    (hea : e ∈ IsManifold.maximalAtlas (𝓡 2) ∞ M) (hr : 0 < r)
    (hc : Metric.ball c r ⊆ e.target)
    (he : ∀ x ∈ e.source,
      o.IsOrientationPreservingAt (Manifold.Orientation.euclideanSpace 2) e x) :
    ∃ f : M → ℝ, ContMDiff (𝓡 2) 𝓘(ℝ) ∞ f ∧ IsRegularValue (𝓡 2) 𝓘(ℝ) f 0 ∧
      (ofChart e hr hc he).disc ⊆ {x | f x < 0} ∧ IsConnected {x | f x ≤ 0} ∧
      {x | f x = 0}.Nonempty := by
  have hρ : 0 < 3 * r / 4 := by positivity
  have hball : closedBall c (3 * r / 4) ⊆ e.target :=
    (closedBall_subset_ball (by linarith)).trans hc
  obtain ⟨f, hf, ha, hle, hlt, heq⟩ := e.exists_isRegularValue_image_closedBall hea hball hρ
  refine ⟨f, hf, ha, ?_, ?_, ?_⟩
  · rw [disc_ofChart, hlt]
    exact image_mono (closedBall_subset_ball (by linarith))
  · rw [hle]
    exact (isConnected_closedBall hρ.le).image _ (e.continuousOn_symm.mono hball)
  · rw [heq]
    exact (NormedSpace.sphere_nonempty.2 hρ.le).image _

/-- **A regular sublevel set around the complement of a coordinate disc.** Let `e` be a chart of
the smooth maximal atlas of a connected, Hausdorff, σ-compact smooth surface `M`, and
`CoordinateDisc.ofChart e hr hc he` the coordinate disc it gives. There is a smooth function
`g : M → ℝ` with regular value `0` such that the complement `discComplement` of the open disc
lies in `{g < 0}`, the sublevel set `{g ≤ 0}` is connected and the level set `{g = 0}` is
nonempty. -/
theorem exists_isRegularValue_discComplement_subset_ofChart [ConnectedSpace M]
    (hea : e ∈ IsManifold.maximalAtlas (𝓡 2) ∞ M) (hr : 0 < r)
    (hc : Metric.ball c r ⊆ e.target)
    (he : ∀ x ∈ e.source,
      o.IsOrientationPreservingAt (Manifold.Orientation.euclideanSpace 2) e x) :
    ∃ g : M → ℝ, ContMDiff (𝓡 2) 𝓘(ℝ) ∞ g ∧ IsRegularValue (𝓡 2) 𝓘(ℝ) g 0 ∧
      discComplement (fun _ : Unit ↦ ofChart e hr hc he) ⊆ {x | g x < 0} ∧
      IsConnected {x | g x ≤ 0} ∧ {x | g x = 0}.Nonempty := by
  have hρ : 0 < r / 4 := by positivity
  have hball : closedBall c (r / 4) ⊆ e.target := (closedBall_subset_ball (by linarith)).trans hc
  obtain ⟨g, hg, hb, hle, hlt, heq⟩ := e.exists_isRegularValue_compl_image_ball hea hball hρ
  have hne : {x | g x = 0}.Nonempty := by
    rw [heq]
    exact (NormedSpace.sphere_nonempty.2 hρ.le).image _
  refine ⟨g, hg, hb, ?_, ⟨hne.mono fun x hx ↦ le_of_eq hx, ?_⟩, hne⟩
  · rw [discComplement_def, iUnion_const, openDisc_ofChart, hlt]
    exact compl_subset_compl.2 (image_mono (closedBall_subset_ball (by linarith)))
  · rw [hle]
    exact e.isPreconnected_compl_image_ball (by
      rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]; norm_num) hρ.ne' hball

end SymplecticGeometry.CoordinateDisc
