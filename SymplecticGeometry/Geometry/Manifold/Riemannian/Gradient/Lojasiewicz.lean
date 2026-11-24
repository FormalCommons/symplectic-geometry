/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.GradientFlow
import TauCeti.Geometry.Manifold.Morse.ExponentialConvergence
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.Distance

/-!
# Convergence of negative gradient trajectories under a Łojasiewicz inequality

Let `f` be a `C²` function on a boundaryless finite-dimensional manifold `M` with a `C¹`
Riemannian metric, and let `γ` be the maximal integral curve of `-grad f` through `x`, defined for
all positive time. If `p` is a cluster point of `γ t` as `t → ∞`, and near `p` the function `f`
satisfies a Łojasiewicz gradient inequality

`c * |f y - f p| ^ θ ≤ ‖grad f y‖`,  with `c > 0` and `θ < 1`,

then `γ` converges to `p`, and for large `t` the Riemannian distance from `γ t` to `p` is at most
`(f (γ t) - f p) ^ (1 - θ) / (c * (1 - θ))`
(`SymplecticGeometry.tendsto_maximalIntegralCurve_neg_mgradient_of_lojasiewicz`). Nothing is
assumed about the critical points of `f` near `p`: they may form a continuum. The bound has the
form of the one in Tau Ceti's normed-space theorem
`IsIntegralCurveOn.exists_tendsto_atTop_of_lojasiewicz`.

Convergence is Tau Ceti's `TauCeti.tendsto_maximalIntegralCurve_neg_mgradient_of_mapClusterPt`,
in `TauCeti/Geometry/Manifold/Morse/ExponentialConvergence.lean`. Once `γ`
stays where the inequality holds, the Łojasiewicz length bound
`TauCeti.pathELength_maximalIntegralCurve_neg_mgradient_le_of_lojasiewicz` bounds its tail
lengths, and `TauCeti.Manifold.riemannianEDist_le_of_tendsto_of_forall_pathELength_le` turns that
into the bound on the distance. This adapts the proof of Tau Ceti's
`TauCeti.exists_riemannianEDist_le_mul_sqrt_maximalIntegralCurve_neg_mgradient`, the case
`θ = 1 / 2` for a trajectory converging to a critical point; its last step is that of Tau Ceti's
private `pathELength_le_of_forall_abs_le`.

## Main results

* `SymplecticGeometry.tendsto_maximalIntegralCurve_neg_mgradient_of_lojasiewicz`: convergence to
  a cluster point at which a Łojasiewicz inequality holds, with the tail bound on the distance.

## References

* S. Łojasiewicz, *Une propriété topologique des sous-ensembles analytiques réels*, Les Équations
  aux Dérivées Partielles, Éditions du CNRS, Paris, 1963, 87–89.
* E. Lerman, *Gradient flow of the norm squared of a moment map*, Enseign. Math. 51 (2005),
  117–127, proof of Theorem 1.1.
-/

public section

open Bundle Filter Manifold Set Topology TauCeti TauCeti.Manifold
open scoped ContDiff ENNReal Manifold

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I 2 M]
  [BoundarylessManifold I M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {f : M → ℝ} {x p : M} {c θ : ℝ}

/-- **Convergence of a negative gradient trajectory under a Łojasiewicz inequality.** Let `f` be
a `C²` function on a boundaryless finite-dimensional manifold with a `C¹` Riemannian metric, and
let the maximal integral curve `γ` of `-grad f` through `x` be defined for all positive time. If
`p` is a cluster point of `γ t` as `t → ∞` and near `p` the inequality
`c * |f y - f p| ^ θ ≤ ‖grad f y‖` holds, with `c > 0` and `θ < 1`, then `γ` converges to `p`,
and for all large `t` the Riemannian distance from `γ t` to `p` is at most
`(f (γ t) - f p) ^ (1 - θ) / (c * (1 - θ))`.

A trajectory whose forward part lies in a compact set, for instance any trajectory on a compact
manifold, is defined for all positive time
(`TauCeti.Ici_subset_maximalIntegralCurveInterval_neg_mgradient`) and has a cluster point. -/
theorem tendsto_maximalIntegralCurve_neg_mgradient_of_lojasiewicz (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hx : Ici 0 ⊆ maximalIntegralCurveInterval (-mgradient I f) x)
    (hp : MapClusterPt p atTop (maximalIntegralCurve (-mgradient I f) x)) (hc : 0 < c)
    (hθ : θ < 1) (hL : ∀ᶠ y in 𝓝 p, c * |f y - f p| ^ θ ≤ ‖mgradient I f y‖) :
    Tendsto (maximalIntegralCurve (-mgradient I f) x) atTop (𝓝 p) ∧
      ∀ᶠ t in atTop, riemannianEDist I (maximalIntegralCurve (-mgradient I f) x t) p ≤
        ENNReal.ofReal
          ((f (maximalIntegralCurve (-mgradient I f) x t) - f p) ^ (1 - θ) / (c * (1 - θ))) := by
  have : IsManifold I 1 M := IsManifold.of_le one_le_two
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := 1)
  set γ := maximalIntegralCurve (-mgradient I f) x
  have htend : Tendsto γ atTop (𝓝 p) :=
    tendsto_maximalIntegralCurve_neg_mgradient_of_mapClusterPt hf hx hp ⟨θ, hθ, c, hc, hL⟩
  refine ⟨htend, ?_⟩
  have hb : ∀ s, 0 ≤ s → f p ≤ f (γ s) := fun s hs ↦
    le_comp_maximalIntegralCurve_neg_mgradient hf hx hp hs
  -- After some time `T ≥ 0` the trajectory stays where the inequality holds.
  obtain ⟨T, hT⟩ := eventually_atTop.mp ((htend.eventually hL).and (eventually_ge_atTop 0))
  filter_upwards [eventually_ge_atTop T] with t ht
  have ht0 : 0 ≤ t := (hT T le_rfl).2.trans ht
  refine riemannianEDist_le_of_tendsto_of_forall_pathELength_le
    ((contMDiffOn_maximalIntegralCurve_neg_mgradient hf).mono fun s hs ↦ hx (ht0.trans hs))
    htend fun s ↦ (pathELength_mono le_rfl (le_max_left s t)).trans ?_
  have hts : t ≤ max s t := le_max_right s t
  refine (pathELength_maximalIntegralCurve_neg_mgradient_le_of_lojasiewicz hf hθ hc hts
    (fun u hu ↦ hx (ht0.trans hu.1)) (hb _ (ht0.trans hts)) fun u hu ↦ ?_).trans
    (ENNReal.ofReal_le_ofReal ?_)
  · simpa only [abs_of_nonneg (sub_nonneg.mpr (hb u (ht0.trans hu.1)))] using
      (hT u (ht.trans hu.1)).1
  · gcongr
    exact sub_le_self _ (Real.rpow_nonneg (sub_nonneg.mpr (hb _ (ht0.trans hts))) _)

end SymplecticGeometry

end
