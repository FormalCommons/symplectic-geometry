/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import TauCeti.Geometry.Manifold.MFDeriv.Constancy
import TauCeti.Topology.LocallyConstant.ConnectedComponents

/-!
# Locally constant maps and vanishing differentials

A locally constant map between manifolds has zero differential at every point
(`IsLocallyConstant.mfderiv_eq_zero`). This is the converse of Tau Ceti's
`MDifferentiable.isLocallyConstant_of_mfderiv_eq_zero`, which needs real manifolds and a
differentiable map; the converse holds over any nontrivially normed field.

The proof is the step that Tau Ceti's
`CovariantDerivative.hasParallelCurvature_iff_isLocallyConstant_scalarCurvature_of_finrank_eq_two`
(in `TauCeti/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/LocallySymmetric.lean`)
takes inline: near each point the map agrees with a constant map, whose differential is zero.

In the other direction, `Convex.apply_eq_of_hasMFDerivWithinAt_zero`: a map from a convex subset
of a real normed space to a manifold, whose derivative within that subset vanishes at each of its
points, is constant on it. The subset need not be open, so this applies to curves on closed
intervals, which Tau Ceti's `MDifferentiableOn.apply_eq_of_mfderiv_eq_zero` (on open
preconnected sets) does not reach. The proof adapts the chart argument of Tau Ceti's
`MDifferentiableOn.eventuallyEq_const_of_mfderiv_eq_zero`, with Mathlib's
`Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le` in place of
`Convex.is_const_of_fderivWithin_eq_zero`.

`MDifferentiable.eq_of_mfderiv_eq` is the manifold form of Mathlib's `eq_of_fderiv_eq`: two
differentiable maps from a preconnected real manifold to a real normed space, with the same
differential everywhere and the same value at one point, are equal. It applies Tau Ceti's
`MDifferentiable.apply_eq_of_mfderiv_eq_zero` to their difference.
-/

public section

open scoped Manifold

namespace IsLocallyConstant

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N] {f : M → N}

/-- A locally constant map between manifolds has zero differential at every point. -/
theorem mfderiv_eq_zero (hf : IsLocallyConstant f) (x : M) : mfderiv I J f x = 0 := by
  rw [Filter.EventuallyEq.mfderiv_eq ((IsLocallyConstant.iff_eventually_eq f).mp hf x)]
  exact mfderiv_const

end IsLocallyConstant

namespace Convex

open Set Filter Topology

variable {E F G N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N] {s : Set E} {g : E → N}

/-- A map from a convex subset `s` of a real normed space to a manifold, whose derivative within
`s` is zero at every point of `s`, takes the same value at any two points of `s`. -/
theorem apply_eq_of_hasMFDerivWithinAt_zero (hs : Convex ℝ s)
    (hg : ∀ x ∈ s, HasMFDerivWithinAt 𝓘(ℝ, E) J g s x 0) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    g x = g y := by
  -- Near each point of `s` the map stays in one chart, where the mean value inequality on a
  -- convex neighbourhood within `s` makes its coordinate expression constant.
  have hloc (z : E) (hz : z ∈ s) : ∀ᶠ w in 𝓝[s] z, g w = g z := by
    set d := extChartAt J (g z)
    have hU : g ⁻¹' d.source ∈ 𝓝[s] z :=
      (hg z hz).continuousWithinAt.preimage_mem_nhdsWithin
        ((isOpen_extChartAt_source (g z)).mem_nhds (mem_extChartAt_source (g z)))
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.mp hU
    have hderiv (w : E) (hw : w ∈ Metric.ball z δ ∩ s) :
        HasFDerivWithinAt (d ∘ g) (0 : E →L[ℝ] F) (Metric.ball z δ ∩ s) w := by
      have hd := (mdifferentiableAt_extChartAt (I := J)
        (by simpa only [d, extChartAt_source, mem_preimage] using hball hw)).hasMFDerivAt
      have h := HasMFDerivAt.comp_hasMFDerivWithinAt (s := Metric.ball z δ ∩ s) w hd
        ((hg w hw.2).mono inter_subset_right)
      rw [ContinuousLinearMap.comp_zero] at h
      exact hasMFDerivWithinAt_iff_hasFDerivWithinAt.mp h
    have hz' : z ∈ Metric.ball z δ ∩ s := ⟨Metric.mem_ball_self hδ, hz⟩
    filter_upwards [inter_mem_nhdsWithin s (Metric.ball_mem_nhds z hδ)] with w hw
    have hw' : w ∈ Metric.ball z δ ∩ s := ⟨hw.2, hw.1⟩
    have h := ((convex_ball z δ).inter hs).norm_image_sub_le_of_norm_hasFDerivWithin_le hderiv
      (C := 0) (fun _ _ ↦ by simp) hz' hw'
    rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at h
    exact d.injOn (hball hw') (hball hz') h
  -- A locally constant map on the preconnected set `s` is constant.
  have hlc : IsLocallyConstant (s.domRestrict g) :=
    (IsLocallyConstant.iff_eventually_eq _).mpr fun z ↦ by
      have h := hloc z z.property
      rw [nhdsWithin_eq_map_subtypeVal z.property, eventually_map] at h
      exact h
  exact hlc.apply_eq_of_isPreconnected_of_subset hs.isPreconnected subset_rfl hx hy

end Convex

namespace MDifferentiable

variable {E F H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- Two differentiable maps from a preconnected real manifold to a real normed space, with the
same differential at every point and the same value at one point, are equal. -/
theorem eq_of_mfderiv_eq [IsManifold I 1 M] [PreconnectedSpace M] {f g : M → F}
    (hf : MDifferentiable I 𝓘(ℝ, F) f) (hg : MDifferentiable I 𝓘(ℝ, F) g)
    (hfg : ∀ x, mfderiv I 𝓘(ℝ, F) f x = mfderiv I 𝓘(ℝ, F) g x) (x : M) (hx : f x = g x) :
    f = g := by
  funext y
  have h := (hf.sub hg).apply_eq_of_mfderiv_eq_zero
    (fun z ↦ (mfderiv_sub (hf z) (hg z)).trans (sub_eq_zero.2 (hfg z))) y x
  simpa [hx, sub_eq_zero] using h

end MDifferentiable

end
