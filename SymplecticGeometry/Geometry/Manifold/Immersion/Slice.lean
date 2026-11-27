/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Geometry.Manifold.Morse.Hessian
import SymplecticGeometry.Geometry.Manifold.Immersion.Chart
import SymplecticGeometry.Geometry.Manifold.Morse.Hessian

/-!
# The squared normal coordinate of an embedding in a slice chart

Let `f : M → N` be a `C^n` immersion at `x` with complement `F`, with normal-form charts `φ` on
`M` and `ψ` on `N` and linear equivalence `L : E × F ≃ E''` (`h.domChart`, `h.codChart`,
`h.equiv`). Read through `L⁻¹`, the extended chart `ψ` has an `E`-coordinate and an
`F`-coordinate, the *normal coordinate* `p ↦ (L⁻¹ (ψ p)).2`, and `f` reads as `u ↦ (u, 0)` there
(`Manifold.IsImmersionAtOfComplement.equiv_symm_codChart_extend_apply`).

If `f` is moreover a topological embedding and `M` is boundaryless, then on a neighbourhood `V`
of `f x` a point lies in the image of `f` exactly when its normal coordinate vanishes. Tau Ceti's
`TauCeti.exists_contMDiffOn_isSliceChart_of_isEmbedding_of_isImmersionAtOfComplement` gives a
`C^n` slice chart but does not say which one; here the coordinates are those of the normal-form
chart `ψ` itself. The pointwise statements below on the squared normal coordinate hold for any
immersion, but `Manifold.IsImmersionAtOfComplement.mem_range_iff_norm_sq_snd_eq_zero` and
`Manifold.IsSmoothEmbedding.exists_contMDiffOn_criticalHessian_pos` need the image of `f` to be
cut out in the coordinates of `ψ`.

For a linear isomorphism `e : F ≃L[ℝ] W` onto a real inner product space, the squared normal
coordinate `g p = ‖e (L⁻¹ (ψ p)).2‖²` is `C^n` on the source of `ψ`, vanishes exactly where the
normal coordinate does, and so, on `V`, exactly on the image of `f`. It has a critical point at
each `f y` with `y` in the source of `φ`, and for `n ≥ 2` its critical Hessian there is
`2 ⟪e (L⁻¹ (dψ u)).2, e (L⁻¹ (dψ w)).2⟫`, which is positive on every vector off the tangent
image of `f`. Nothing here asks for finite dimension, except the last statement, where an
inner product on the complement comes from `toEuclidean`: for a `C^n` embedding `f`, `n ≥ 2`,
into a manifold with finite-dimensional model, every point of the image has an open
neighbourhood carrying such a function
(`Manifold.IsSmoothEmbedding.exists_contMDiffOn_criticalHessian_pos`).

The set-level statement follows the proof of Tau Ceti's
`TauCeti.exists_contMDiffOn_isSliceChart_of_isEmbedding_of_isImmersionAtOfComplement`, but
concludes in the coordinates `h.equiv.symm (h.codChart.extend J p)` of `ψ`, with
`V ⊆ h.codChart.source` and `f ⁻¹' V ⊆ h.domChart.source`. The statements on `g` follow
`TauCeti.IsAdaptedChart.norm_sq_snd_eq_zero_iff`,
`TauCeti.IsAdaptedChart.mem_criticalPoints_norm_sq_snd`,
`TauCeti.IsAdaptedChart.criticalHessian_norm_sq_snd_apply` and
`TauCeti.IsAdaptedChart.criticalHessian_norm_sq_snd_pos` of this library's
`Geometry/Manifold/Complex/JConvex/TotallyReal.lean`, with a slice chart of an embedding in place
of a chart adapted to a totally real submanifold; the steps of the last proofs that do not depend
on the chart are `TauCeti.mem_criticalPoints_norm_sq_of_eq_zero` and
`TauCeti.criticalHessian_norm_sq_continuousLinearMap_comp_apply_of_eq_zero` of
`Geometry/Manifold/Morse/Hessian.lean`.

## Main results

* `Manifold.IsImmersionAtOfComplement.exists_isOpen_mem_range_iff_snd_eq_zero`: near `f x`, the
  image of an embedding is the zero set of the normal coordinate.
* `Manifold.IsImmersionAtOfComplement.norm_sq_snd_eq_zero_iff` and
  `Manifold.IsImmersionAtOfComplement.mem_range_iff_norm_sq_snd_eq_zero`: the zero set of the
  squared normal coordinate.
* `Manifold.IsImmersionAtOfComplement.contMDiffOn_norm_sq_snd`,
  `Manifold.IsImmersionAtOfComplement.mem_criticalPoints_norm_sq_snd`,
  `Manifold.IsImmersionAtOfComplement.criticalHessian_norm_sq_snd_apply` and
  `Manifold.IsImmersionAtOfComplement.criticalHessian_norm_sq_snd_pos`: smoothness, critical
  points and the critical Hessian of the squared normal coordinate.
* `Manifold.IsSmoothEmbedding.exists_contMDiffOn_criticalHessian_pos`: these facts, collected for
  a `C^n` embedding near a point of its image.

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
    have hmem : (h.equiv.symm (h.codChart.extend J p)).1 ∈ (h.domChart.extend I).target := by
      rw [h.domChart.extend_target, I.range_eq_univ, inter_univ]
      exact hp.1.2
    obtain ⟨hsrc, hext, -, -⟩ := h.mem_codChart_source_and_extend_eq hmem
    refine ⟨(h.domChart.extend I).symm (h.equiv.symm (h.codChart.extend J p)).1,
      (h.codChart.extend J).injOn ?_ ?_ ?_⟩
    · rwa [h.codChart.extend_source]
    · rw [h.codChart.extend_source]; exact hp.1.1
    · rw [hext, ← hp0, Prod.mk.eta, ContinuousLinearEquiv.apply_symm_apply]

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

/-- The squared normal coordinate `‖e (h.equiv.symm (ψ p)).2‖²` of an immersion, `ψ` the extended
codomain chart, vanishes exactly where the normal coordinate `(h.equiv.symm (ψ p)).2` does. -/
theorem norm_sq_snd_eq_zero_iff (p : N) :
    ‖e (h.equiv.symm (h.codChart.extend J p)).2‖ ^ 2 = 0 ↔
      (h.equiv.symm (h.codChart.extend J p)).2 = 0 := by
  simp

/-- On a set `V` where the image of `f` is the zero set of the normal coordinate, as given by
`exists_isOpen_mem_range_iff_snd_eq_zero`, it is also the zero set of the squared normal
coordinate `p ↦ ‖e (h.equiv.symm (ψ p)).2‖²`. -/
theorem mem_range_iff_norm_sq_snd_eq_zero {V : Set N}
    (hV : ∀ p ∈ V, (p ∈ range f ↔ (h.equiv.symm (h.codChart.extend J p)).2 = 0)) {p : N}
    (hp : p ∈ V) : p ∈ range f ↔ ‖e (h.equiv.symm (h.codChart.extend J p)).2‖ ^ 2 = 0 := by
  rw [hV p hp, h.norm_sq_snd_eq_zero_iff e]

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
    f y ∈ criticalPoints J (fun p ↦ ‖e (h.equiv.symm (h.codChart.extend J p)).2‖ ^ 2) :=
  mem_criticalPoints_norm_sq_of_eq_zero
    (by rw [h.equiv_symm_codChart_extend_apply hy, map_zero])
    BoundarylessManifold.isInteriorPoint

/-- **The Hessian of the squared normal coordinate.** For `n ≥ 2` and `y` in the domain chart's
source, the critical Hessian at `f y` of `p ↦ ‖e (L⁻¹ (ψ p)).2‖²`, `ψ` the extended codomain chart
and `L = h.equiv`, is `2 ⟪e (L⁻¹ (dψ u)).2, e (L⁻¹ (dψ w)).2⟫`. -/
theorem criticalHessian_norm_sq_snd_apply [J.Boundaryless] (hn : 2 ≤ n) {y : M}
    (hy : y ∈ h.domChart.source) (u w : TangentSpace J (f y)) :
    criticalHessian J (fun p ↦ ‖e (h.equiv.symm (h.codChart.extend J p)).2‖ ^ 2) (f y) u w =
      2 * inner ℝ (e (h.equiv.symm (mfderiv J 𝓘(ℝ, E'') (h.codChart.extend J) (f y) u)).2)
        (e (h.equiv.symm (mfderiv J 𝓘(ℝ, E'') (h.codChart.extend J) (f y) w)).2) := by
  have := criticalHessian_norm_sq_continuousLinearMap_comp_apply_of_eq_zero
    (A := (e : F →L[ℝ] W).comp
      ((ContinuousLinearMap.snd ℝ E F).comp (h.equiv.symm : E'' →L[ℝ] E × F)))
    ((h.codChart.contMDiffAt_extend h.codChart_mem_maximalAtlas
      (h.source_subset_preimage_source hy)).of_le hn)
    (by simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.coe_snd',
      h.equiv_symm_codChart_extend_apply hy, map_zero]) u w
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.coe_snd'] at this
  exact this

/-- **Positivity of the Hessian off the tangent image.** For `n ≥ 2` and `y` in the domain chart's
source, the critical Hessian at `f y` of the squared normal coordinate is positive on every
tangent vector that is not in the range of the derivative of `f` at `y`. -/
theorem criticalHessian_norm_sq_snd_pos [J.Boundaryless] (hn : 2 ≤ n) {y : M}
    (hy : y ∈ h.domChart.source) {v : TangentSpace J (f y)}
    (hv : v ∉ LinearMap.range (mfderiv I J f y).toLinearMap) :
    0 < criticalHessian J (fun p ↦ ‖e (h.equiv.symm (h.codChart.extend J p)).2‖ ^ 2) (f y) v v := by
  rw [h.criticalHessian_norm_sq_snd_apply e hn hy, real_inner_self_eq_norm_sq]
  have := (h.snd_equiv_symm_mfderiv_extend_eq_zero_iff
    (ENat.one_le_iff_ne_zero_withTop.1 (one_le_two.trans hn)) hy v).not.2 hv
  have : e (h.equiv.symm (mfderiv J 𝓘(ℝ, E'') (h.codChart.extend J) (f y) v)).2 ≠ 0 := by
    simpa using this
  positivity

end NormSq

end Manifold.IsImmersionAtOfComplement

namespace Manifold.IsSmoothEmbedding

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [FiniteDimensional ℝ E'']
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ E'' G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : WithTop ℕ∞} {f : M → N}

/-- **A local squared distance to an embedded submanifold.** Let `f` be a `C^n` embedding,
`n ≥ 2`, of a boundaryless manifold into a boundaryless manifold with finite-dimensional model.
Each point `f x` has an open neighbourhood `V` with a nonnegative function `g`, `C^n` on `V`, that
vanishes on `V` exactly on the image of `f`, and such that each point `f y` of `V` is a critical
point of `g` at which the critical Hessian of `g` is positive on every vector off the tangent
image of `f` at `y`. -/
theorem exists_contMDiffOn_criticalHessian_pos [I.Boundaryless] [J.Boundaryless]
    (hf : IsSmoothEmbedding I J n f) (hn : 2 ≤ n) (x : M) :
    ∃ V : Set N, IsOpen V ∧ f x ∈ V ∧ ∃ g : N → ℝ, ContMDiffOn J 𝓘(ℝ) n g V ∧ (∀ p, 0 ≤ g p) ∧
      (∀ p ∈ V, g p = 0 ↔ p ∈ range f) ∧
      ∀ y, f y ∈ V → f y ∈ criticalPoints J g ∧
        ∀ v ∉ LinearMap.range (mfderiv I J f y).toLinearMap, 0 < criticalHessian J g (f y) v v := by
  have h := (hf.isImmersion.isImmersionAt x).isImmersionAtOfComplement_complement
  -- The complement is finite-dimensional, as a quotient of the model `E''` of `N`.
  have : FiniteDimensional ℝ (hf.isImmersion.isImmersionAt x).complement :=
    Module.Finite.of_surjective ((LinearMap.snd ℝ E _).comp h.equiv.symm.toLinearMap)
      fun v ↦ ⟨h.equiv (0, v), by simp⟩
  obtain ⟨V, hVo, hxV, hVsrc, hVdom, hV⟩ := h.exists_isOpen_mem_range_iff_snd_eq_zero hf.isEmbedding
  exact ⟨V, hVo, hxV, _, (h.contMDiffOn_norm_sq_snd toEuclidean).mono hVsrc,
    fun _ ↦ sq_nonneg _, fun _ hp ↦ (h.mem_range_iff_norm_sq_snd_eq_zero toEuclidean hV hp).symm,
    fun _ hy ↦ ⟨h.mem_criticalPoints_norm_sq_snd toEuclidean (hVdom hy),
      fun _ hv ↦ h.criticalHessian_norm_sq_snd_pos toEuclidean hn (hVdom hy) hv⟩⟩

end Manifold.IsSmoothEmbedding

end
