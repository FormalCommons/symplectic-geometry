/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.GradientFlow
import TauCeti.Topology.Order.MonotoneConvergence

/-!
# The value of `f` at an ω-limit point of a negative gradient trajectory

This file is a part of Tau Ceti's `TauCeti/Geometry/Manifold/Morse/GradientFlow.lean`, copied
from Tau Ceti's main branch at commit `07c8b6b1f5ff5bdab8363e207e59d68eccc82bef`, which the
pinned version of Tau Ceti does not have yet. It contains two declarations of that file. Let `γ`
be the maximal integral curve of `-grad f` through `x`, defined for all positive time, and let
`z` be a cluster point of `γ t` as `t → ∞`. Since `f` decreases along `γ`, it stays above `f z`
(`TauCeti.le_comp_maximalIntegralCurve_neg_mgradient`) and tends to `f z`
(`TauCeti.tendsto_comp_maximalIntegralCurve_neg_mgradient`).

Changes from Tau Ceti's file: only these two declarations are taken, with the `variable` lines
they need and the imports they use; this module docstring replaces Tau Ceti's; the declarations,
their docstrings and their proofs are unchanged.

The pinned version of Tau Ceti has a `TauCeti.le_comp_maximalIntegralCurve_neg_mgradient` of its
own, in `TauCeti/Geometry/Manifold/Morse/ExponentialConvergence.lean`, which assumes that `γ`
converges to `z`. Its main branch replaces it by the one here. So this file cannot be imported
together with that file of the pinned version, nor with any file that imports it, such as the
pinned `TauCeti/Geometry/Manifold/Morse/Bott/ExponentialConvergence.lean`,
`Morse/Trajectory.lean`, `Morse/Sphere/GradientFlow.lean` and
`Riemannian/Submersion/GradientFlow.lean`.

## References

* M. W. Hirsch, S. Smale and R. L. Devaney, *Differential Equations, Dynamical Systems, and an
  Introduction to Chaos*, second edition, Academic Press, 2004, Chapter 9 (gradient systems).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Proposition 2.1.6.
-/

public section

open Bundle Filter Function MeasureTheory Set Topology TauCeti.Manifold
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I 2 M]
  [BoundarylessManifold I M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {f : M → ℝ} {x : M} {t : ℝ}

/-- **The value at an ω-limit point bounds `f` from below along the trajectory.** If the maximal
integral curve `γ` of `-grad f` through `x` exists for all positive time and `z` is a cluster point
of `γ t` as `t → ∞`, then `f z ≤ f (γ t)` for every `t ≥ 0`, since `f` decreases along `γ`. -/
theorem le_comp_maximalIntegralCurve_neg_mgradient (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hx : Ici 0 ⊆ maximalIntegralCurveInterval (-mgradient I f) x) {z : M}
    (hz : MapClusterPt z atTop (maximalIntegralCurve (-mgradient I f) x)) (ht : 0 ≤ t) :
    f z ≤ f (maximalIntegralCurve (-mgradient I f) x t) :=
  (isClosed_le hf.continuous continuous_const).mem_of_mapClusterPt hz <| by
    filter_upwards [eventually_ge_atTop t] with s hs
    exact antitoneOn_comp_maximalIntegralCurve_neg_mgradient hf (hx ht) (hx (ht.trans hs)) hs

/-- **Along a forward trajectory, `f` tends to its value at every ω-limit point.** If the maximal
integral curve `γ` of `-grad f` through `x` exists for all positive time and `z` is a cluster point
of `γ t` as `t → ∞`, then `f (γ t)` tends to `f z`. -/
theorem tendsto_comp_maximalIntegralCurve_neg_mgradient (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hx : Ici 0 ⊆ maximalIntegralCurveInterval (-mgradient I f) x) {z : M}
    (hz : MapClusterPt z atTop (maximalIntegralCurve (-mgradient I f) x)) :
    Tendsto (fun s ↦ f (maximalIntegralCurve (-mgradient I f) x s)) atTop (𝓝 (f z)) := by
  set γ := maximalIntegralCurve (-mgradient I f) x
  -- The function `f` is antitone along the forward trajectory and bounded below by `f z`.
  have hg := tendsto_atTop_ciInf_of_antitoneOn_Ici
    ((antitoneOn_comp_maximalIntegralCurve_neg_mgradient hf).mono hx)
    ⟨f z, by rintro _ ⟨s, hs, rfl⟩; exact le_comp_maximalIntegralCurve_neg_mgradient hf hx hz hs⟩
  -- The limit is the value of `f` at the cluster point `z`.
  have hne : NeBot (𝓝 (f z) ⊓ 𝓝 (⨅ s : Ici (0 : ℝ), f (γ s))) :=
    NeBot.mono (hz.continuousAt_comp hf.continuous.continuousAt) (inf_le_inf_left _ hg)
  rwa [eq_of_nhds_neBot hne]

end TauCeti
