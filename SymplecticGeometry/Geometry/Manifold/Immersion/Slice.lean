/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import SymplecticGeometry.Geometry.Manifold.Immersion.Chart
public import TauCeti.Analysis.InnerProductSpace.Calculus
public import TauCeti.Geometry.Manifold.Morse.Hessian

/-!
# The squared normal coordinate of an embedding in a slice chart

Let `f : M → N` be a `C^n` immersion at `x` with complement `F`, with normal-form charts `φ` on
`M` and `ψ` on `N` and linear equivalence `L : E × F ≃ E''` (`h.domChart`, `h.codChart`,
`h.equiv`). Read through `L⁻¹`, the extended chart `ψ` has an `E`-coordinate and an
`F`-coordinate, the *normal coordinate* `p ↦ (L⁻¹ (ψ p)).2`, and `f` reads as `u ↦ (u, 0)` there.

If `f` is moreover a topological embedding and `M` is boundaryless, then on a neighbourhood `V`
of `f x` a point lies in the image of `f` exactly when its normal coordinate vanishes. Unlike
Tau Ceti's slice chart, which is only an open partial homeomorphism, the coordinates here are
those of the chart `ψ` of the maximal atlas, so they are `C^n`.

For a linear isomorphism `e : F ≃L[ℝ] W` onto a real inner product space, the squared normal
coordinate `g p = ‖e (L⁻¹ (ψ p)).2‖²` is nonnegative and `C^n` on the source of `ψ`; on `V` it
vanishes exactly on the image of `f`, since `e` is injective. It has a critical point at each
`f y` with `y` in the source of `φ`, and for `n ≥ 2` its critical Hessian there is
`2 ⟪e (L⁻¹ (dψ u)).2, e (L⁻¹ (dψ w)).2⟫`, which is positive on every vector off the tangent
image of `f`. Nothing here asks for finite dimension.

The set-level statement follows the proof of Tau Ceti's
`TauCeti.exists_isSliceChart_of_isEmbedding_of_isImmersionAtOfComplement`, keeping the chart of
the maximal atlas. The statements on `g` follow `TauCeti.IsAdaptedChart.norm_sq_snd_eq_zero_iff`,
`TauCeti.IsAdaptedChart.mem_criticalPoints_norm_sq_snd`,
`TauCeti.IsAdaptedChart.criticalHessian_norm_sq_snd_apply` and
`TauCeti.IsAdaptedChart.criticalHessian_norm_sq_snd_pos` of this library's
`Geometry/Manifold/Complex/JConvex/TotallyReal.lean`, with a slice chart of an embedding in place
of a chart adapted to a totally real submanifold.

## Main results

* `Manifold.IsImmersionAtOfComplement.equiv_symm_codChart_extend_apply`: in the split
  coordinates of the codomain chart, `f` is `u ↦ (u, 0)` on the domain chart's side.
* `Manifold.IsImmersionAtOfComplement.exists_isOpen_mem_range_iff_snd_eq_zero`: near `f x`, the
  image of an embedding is the zero set of the normal coordinate.
* `Manifold.IsImmersionAtOfComplement.contMDiffOn_norm_sq_snd`,
  `Manifold.IsImmersionAtOfComplement.mem_criticalPoints_norm_sq_snd`,
  `Manifold.IsImmersionAtOfComplement.criticalHessian_norm_sq_snd_apply` and
  `Manifold.IsImmersionAtOfComplement.criticalHessian_norm_sq_snd_pos`: smoothness, critical
  points and the critical Hessian of the squared normal coordinate.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Chapter 5 (slice charts of embedded submanifolds).
* [M. W. Hirsch, *Differential Topology*][Hirsch1976], Springer GTM 33 (1976), Chapter 1.
-/

public section

open Set Function Filter Manifold Topology TauCeti
open scoped ContDiff Manifold

namespace Manifold.IsImmersionAtOfComplement

section Slice

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 E'' G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : WithTop ℕ∞} {f : M → N} {x : M}

/-- In the coordinates `E × F` of the codomain chart, read through `h.equiv`, an immersion is the
inclusion `u ↦ (u, 0)` of the coordinates of the domain chart. -/
theorem equiv_symm_codChart_extend_apply (h : IsImmersionAtOfComplement F I J n f x) {y : M}
    (hy : y ∈ h.domChart.source) :
    h.equiv.symm (h.codChart.extend J (f y)) = (h.domChart.extend I y, 0) := by
  have hy' : y ∈ (h.domChart.extend I).source := by rwa [h.domChart.extend_source]
  have hw := h.writtenInCharts ((h.domChart.extend I).map_source hy')
  simp only [comp_apply, (h.domChart.extend I).left_inv hy'] at hw
  rw [hw, ContinuousLinearEquiv.symm_apply_apply]

/-- **The slice of an embedding.** Let `f` be a topological embedding of a boundaryless manifold
which is an immersion at `x`. Then there is an open neighbourhood `V` of `f x` inside the source
of the codomain chart, whose preimage lies in the source of the domain chart, on which a point
lies in the image of `f` exactly when its `F`-coordinate `(h.equiv.symm (ψ p)).2` vanishes,
`ψ` being the extended codomain chart. -/
theorem exists_isOpen_mem_range_iff_snd_eq_zero [I.Boundaryless]
    (h : IsImmersionAtOfComplement F I J n f x) (hf : IsEmbedding f) :
    ∃ V : Set N, IsOpen V ∧ f x ∈ V ∧ V ⊆ h.codChart.source ∧ f ⁻¹' V ⊆ h.domChart.source ∧
      ∀ p ∈ V, (p ∈ range f ↔ (h.equiv.symm (h.codChart.extend J p)).2 = 0) := by
  -- Because `f` is an embedding, an open set of `N` cuts `f '' h.domChart.source` out of the
  -- image.
  obtain ⟨O, hO, hOf⟩ := hf.isInducing.isOpen_iff.1 h.domChart.open_source
  have hmemO : ∀ y : M, f y ∈ O ↔ y ∈ h.domChart.source := fun y ↦ by rw [← hOf]; rfl
  -- The part of the codomain chart lying over the target of the domain chart.
  have hU : IsOpen ((fun v : E × F ↦ I.symm v.1) ⁻¹' h.domChart.target) :=
    h.domChart.open_target.preimage (I.continuous_symm.comp continuous_fst)
  have hc : ContinuousOn (fun p ↦ h.equiv.symm (h.codChart.extend J p)) h.codChart.source := by
    have := h.codChart.continuousOn_extend (I := J)
    rw [h.codChart.extend_source] at this
    exact h.equiv.symm.continuous.comp_continuousOn this
  refine ⟨(h.codChart.source ∩ (fun p ↦ h.equiv.symm (h.codChart.extend J p)) ⁻¹'
      ((fun v : E × F ↦ I.symm v.1) ⁻¹' h.domChart.target)) ∩ O,
    (hc.isOpen_inter_preimage h.codChart.open_source hU).inter hO, ?_, fun p hp ↦ hp.1.1,
    fun y hy ↦ (hmemO y).1 hy.2, fun p hp ↦ ⟨?_, fun hp0 ↦ ?_⟩⟩
  · refine ⟨⟨h.mem_codChart_source, ?_⟩, (hmemO x).2 h.mem_domChart_source⟩
    rw [mem_preimage, h.equiv_symm_codChart_extend_apply h.mem_domChart_source,
      mem_preimage, OpenPartialHomeomorph.extend_coe, comp_apply, I.left_inv]
    exact h.domChart.map_source h.mem_domChart_source
  · rintro ⟨y, rfl⟩
    rw [h.equiv_symm_codChart_extend_apply ((hmemO y).1 hp.2)]
  · -- A point of the slice over the target of the domain chart is the image of a point of
    -- the domain chart's source.
    set u := (h.equiv.symm (h.codChart.extend J p)).1
    have hmem : u ∈ (h.domChart.extend I).target := by
      rw [h.domChart.extend_target, I.range_eq_univ, inter_univ]
      exact hp.1.2
    have hys : (h.domChart.extend I).symm u ∈ h.domChart.source := by
      rw [← h.domChart.extend_source (I := I)]
      exact (h.domChart.extend I).map_target hmem
    refine ⟨(h.domChart.extend I).symm u, (h.codChart.extend J).injOn ?_ ?_ ?_⟩
    · rw [h.codChart.extend_source]; exact h.source_subset_preimage_source hys
    · rw [h.codChart.extend_source]; exact hp.1.1
    · apply h.equiv.symm.injective
      rw [h.equiv_symm_codChart_extend_apply hys, (h.domChart.extend I).right_inv hmem, ← hp0]

end Slice

section NormSq

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ E'' G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {n : WithTop ℕ∞} {f : M → N} {x : M} (h : IsImmersionAtOfComplement F I J n f x) (e : F ≃L[ℝ] W)
include h

/-- The squared normal coordinate `p ↦ ‖e (h.equiv.symm (ψ p)).2‖²` of an immersion is `C^n` on
the source of the codomain chart `ψ`. -/
theorem contMDiffOn_norm_sq_snd :
    ContMDiffOn J 𝓘(ℝ) n (fun p ↦ ‖e (h.equiv.symm (h.codChart.extend J p)).2‖ ^ 2)
      h.codChart.source :=
  ((contDiff_norm_sq ℝ).comp (e.contDiff.comp (contDiff_snd.comp h.equiv.symm.contDiff))).contMDiff
    |>.comp_contMDiffOn (h.codChart.contMDiffOn_extend h.codChart_mem_maximalAtlas)

/-- The image `f y` of a point `y` of the domain chart's source is a critical point of the squared
normal coordinate, which takes its minimum `0` there. -/
theorem mem_criticalPoints_norm_sq_snd [BoundarylessManifold J N] {y : M}
    (hy : y ∈ h.domChart.source) :
    f y ∈ criticalPoints J (fun p ↦ ‖e (h.equiv.symm (h.codChart.extend J p)).2‖ ^ 2) := by
  refine IsLocalMin.mem_criticalPoints (Eventually.of_forall fun p ↦ ?_)
    BoundarylessManifold.isInteriorPoint
  simp only [h.equiv_symm_codChart_extend_apply hy, map_zero, norm_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  positivity

/-- **The Hessian of the squared normal coordinate.** For `n ≥ 2` and `y` in the domain chart's
source, the critical Hessian at `f y` of `p ↦ ‖e (L⁻¹ (ψ p)).2‖²`, `ψ` the extended codomain chart
and `L = h.equiv`, is `2 ⟪e (L⁻¹ (dψ u)).2, e (L⁻¹ (dψ w)).2⟫`. -/
theorem criticalHessian_norm_sq_snd_apply [J.Boundaryless] (hn : 2 ≤ n) {y : M}
    (hy : y ∈ h.domChart.source) (u w : TangentSpace J (f y)) :
    criticalHessian J (fun p ↦ ‖e (h.equiv.symm (h.codChart.extend J p)).2‖ ^ 2) (f y) u w =
      2 * inner ℝ (e (h.equiv.symm (mfderiv J 𝓘(ℝ, E'') (h.codChart.extend J) (f y) u)).2)
        (e (h.equiv.symm (mfderiv J 𝓘(ℝ, E'') (h.codChart.extend J) (f y) w)).2) := by
  have hψ : ContMDiffAt J 𝓘(ℝ, E'') 2 (h.codChart.extend J) (f y) :=
    (h.codChart.contMDiffAt_extend h.codChart_mem_maximalAtlas
      (h.source_subset_preimage_source hy)).of_le hn
  set A : E'' →L[ℝ] W :=
    (e : F →L[ℝ] W).comp ((ContinuousLinearMap.snd ℝ E F).comp (h.equiv.symm : E'' →L[ℝ] E × F))
  have hA : ∀ v, A v = e (h.equiv.symm v).2 := fun _ ↦ by simp [A]
  have hφ : ContMDiffAt J 𝓘(ℝ, W) 2 (fun p ↦ A (h.codChart.extend J p)) (f y) :=
    A.contDiff.contMDiff.contMDiffAt.comp (f y) hψ
  have hcrit : A (h.codChart.extend J (f y)) ∈ criticalPoints 𝓘(ℝ, W) (fun z : W ↦ ‖z‖ ^ 2) := by
    refine IsLocalMin.mem_criticalPoints (Eventually.of_forall fun z ↦ ?_)
      BoundarylessManifold.isInteriorPoint
    simp only [hA, h.equiv_symm_codChart_extend_apply hy, map_zero, norm_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity
  -- The second-order chain rule at the critical point `0` of `‖·‖²`.
  have hH := criticalHessian_comp_apply (f := fun z : W ↦ ‖z‖ ^ 2) rfl
    (contDiff_norm_sq ℝ).contMDiff.contMDiffAt hφ hcrit u w
  have hD : mfderiv J 𝓘(ℝ, W) (fun p ↦ A (h.codChart.extend J p)) (f y) =
      A.comp (mfderiv J 𝓘(ℝ, E'') (h.codChart.extend J) (f y)) :=
    (A.hasFDerivAt.hasMFDerivAt.comp (f y)
      (hψ.mdifferentiableAt two_ne_zero).hasMFDerivAt).mfderiv
  rw [hD, criticalHessian_modelSpace] at hH
  exact hH.trans (TauCeti.fderiv_fderiv_norm_sq_apply (E := W) _ _ _)

/-- **Positivity of the Hessian off the tangent image.** For `n ≥ 2` and `y` in the domain chart's
source, the critical Hessian at `f y` of the squared normal coordinate is positive on every
tangent vector that is not in the range of the derivative of `f` at `y`. -/
theorem criticalHessian_norm_sq_snd_pos [J.Boundaryless] (hn : 2 ≤ n) {y : M}
    (hy : y ∈ h.domChart.source) {v : TangentSpace J (f y)}
    (hv : v ∉ LinearMap.range (mfderiv I J f y).toLinearMap) :
    0 < criticalHessian J (fun p ↦ ‖e (h.equiv.symm (h.codChart.extend J p)).2‖ ^ 2) (f y) v v := by
  have h1 : (1 : WithTop ℕ∞) ≤ n := le_trans (by norm_num) hn
  rw [h.criticalHessian_norm_sq_snd_apply e hn hy, real_inner_self_eq_norm_sq]
  suffices (h.equiv.symm (mfderiv J 𝓘(ℝ, E'') (h.codChart.extend J) (f y) v)).2 ≠ 0 by
    have : e (h.equiv.symm (mfderiv J 𝓘(ℝ, E'') (h.codChart.extend J) (f y) v)).2 ≠ 0 := by
      simpa using this
    positivity
  intro h0
  apply hv
  -- A vector whose normal coordinate vanishes is `dψ (df w)` for some `w`, hence tangent to `f`.
  obtain ⟨Lφ, hLφ⟩ := isInvertible_mfderiv_extend
    (IsManifold.maximalAtlas_subset_of_le h1 h.domChart_mem_maximalAtlas) hy
  obtain ⟨Lψ, hLψ⟩ := isInvertible_mfderiv_extend
    (IsManifold.maximalAtlas_subset_of_le h1 h.codChart_mem_maximalAtlas)
    (h.source_subset_preimage_source hy)
  have hsurj : Surjective (mfderiv I 𝓘(ℝ, E) (h.domChart.extend I) y) := hLφ ▸ Lφ.surjective
  have hinj : Injective (mfderiv J 𝓘(ℝ, E'') (h.codChart.extend J) (f y)) :=
    hLψ ▸ Lψ.injective
  obtain ⟨w, hw⟩ := hsurj (h.equiv.symm (mfderiv J 𝓘(ℝ, E'') (h.codChart.extend J) (f y) v)).1
  refine ⟨w, hinj ?_⟩
  have hc : mfderiv J 𝓘(ℝ, E'') (h.codChart.extend J) (f y) (mfderiv I J f y w) =
      h.equiv (mfderiv I 𝓘(ℝ, E) (h.domChart.extend I) y w, 0) := by
    have := congr($(h.mfderiv_extend_comp_mfderiv (one_pos.trans_le h1).ne' hy) w)
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply] at this
    -- `this` applies `h.equiv` (as a linear map) to `inl _ = (_, 0)`.
    exact this
  rw [ContinuousLinearMap.coe_coe, hc, hw, ← h0, Prod.mk.eta]
  -- `apply_symm_apply` read in `TangentSpace 𝓘(ℝ, E'') _`, which is `E''` by definition.
  exact h.equiv.apply_symm_apply _

end NormSq

end Manifold.IsImmersionAtOfComplement

end
