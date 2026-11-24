/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.GradientFlow
import TauCeti.Analysis.Calculus.Lojasiewicz
import TauCeti.Geometry.Manifold.Riemannian.ArcLength
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
assumed about the critical points of `f` near `p`: they may form a continuum. This is the manifold
counterpart, for an arbitrary `C¹` metric, of Tau Ceti's normed-space theorem
`IsIntegralCurveOn.exists_tendsto_atTop_of_lojasiewicz`.

## The argument

Write `e t = f (γ t) - f p` and `g t = ‖grad f (γ t)‖`. Since `f` decreases along `γ` and `f p` is a
cluster value of `f ∘ γ`, the excess `e` is nonnegative, and `e' = -g ^ 2`. On every time interval
`[a, b)` during which `γ` stays where the inequality holds, the Riemannian length of `γ` over
`[a, b]`, which is `∫ g`, is at most `e a ^ (1 - θ) / (c * (1 - θ))`, by Tau Ceti's scalar bound
`TauCeti.integral_le_rpow_sub_rpow_of_lojasiewicz`.

The inequality is only known near `p`, so the curve has to be trapped there
(`SymplecticGeometry.riemannianEDist_maximalIntegralCurve_neg_mgradient_lt_of_lojasiewicz`). Let
the inequality hold on the Riemannian ball of radius `δ` about `p`, which Mathlib's
`setOfPred_riemannianEDist_lt_subset_nhds` provides inside any neighbourhood, and let `T` be a time
at which `γ T` lies within `δ / 2` of `p` and `e T ^ (1 - θ) / (c * (1 - θ)) < δ / 2`. If `γ` left
the ball after `T`, then at the first time `τ` it does so, the length of `γ` over `[T, τ]` would be
less than `δ / 2`, so `γ τ` would still lie in the ball. As `δ` may be taken as small as wished,
`γ` converges to `p`; the distance bound then follows from Tau Ceti's
`TauCeti.Manifold.riemannianEDist_le_of_tendsto_of_forall_pathELength_le`. The choice of `T` near
the cluster point and the passage from Riemannian balls to neighbourhoods adapt the proof of Tau
Ceti's `TauCeti.Manifold.tendsto_of_mapClusterPt_of_forall_pathELength_le`, which assumes the
tail lengths small instead of proving it. Working with the Riemannian distance rather than in a
chart avoids comparing the metric with the norm of a chart.

## Main results

* `Manifold.isOpen_setOfPred_riemannianEDist_lt`: balls for the Riemannian extended distance are
  open.
* `SymplecticGeometry.le_comp_maximalIntegralCurve_neg_mgradient_of_mapClusterPt`: along a forward
  negative gradient trajectory, `f` stays above its value at each cluster point.
* `SymplecticGeometry.pathELength_maximalIntegralCurve_neg_mgradient_le_of_lojasiewicz`: the
  Łojasiewicz length bound for a piece of the trajectory on which the inequality holds.
* `SymplecticGeometry.riemannianEDist_maximalIntegralCurve_neg_mgradient_lt_of_lojasiewicz`:
  the trapping argument.
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
open scoped ContDiff ENNReal Manifold NNReal

namespace Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- An open ball for the Riemannian extended distance is open. -/
theorem isOpen_setOfPred_riemannianEDist_lt (x : M) (r : ℝ≥0∞) :
    IsOpen {y | riemannianEDist I x y < r} := isOpen_iff_mem_nhds.mpr fun y hy ↦ by
  obtain ⟨ε, hε, hεr⟩ := ENNReal.lt_iff_exists_add_pos_lt.mp hy
  filter_upwards [eventually_riemannianEDist_lt I y (c := ε) (by exact_mod_cast hε)] with z hz
  exact (riemannianEDist_triangle.trans_lt (ENNReal.add_lt_add_left (ne_top_of_lt hy) hz)).trans
    hεr

end Manifold

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I 2 M]
  [BoundarylessManifold I M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {f : M → ℝ} {x p : M} {c θ : ℝ}

/-- **A forward negative gradient trajectory stays above its cluster values.** If the maximal
integral curve `γ` of `-grad f` through `x` is defined for all positive time and `p` is a cluster
point of `γ t` as `t → ∞`, then `f p ≤ f (γ t)` for every `t ≥ 0`. -/
theorem le_comp_maximalIntegralCurve_neg_mgradient_of_mapClusterPt (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hx : Ici 0 ⊆ maximalIntegralCurveInterval (-mgradient I f) x)
    (hp : MapClusterPt p atTop (maximalIntegralCurve (-mgradient I f) x)) {t : ℝ} (ht : 0 ≤ t) :
    f p ≤ f (maximalIntegralCurve (-mgradient I f) x t) := by
  refine isClosed_Iic.mem_of_mapClusterPt (hp.continuousAt_comp hf.continuous.continuousAt) ?_
  filter_upwards [eventually_ge_atTop t] with s hs
  exact antitoneOn_comp_maximalIntegralCurve_neg_mgradient hf (hx ht) (hx (ht.trans hs)) hs

/-- **The Łojasiewicz length bound on a manifold.** Let the maximal integral curve `γ` of
`-grad f` through `x` be defined on `[a, b]`, with `f (γ t) ≥ f p` there. If
`c * (f (γ t) - f p) ^ θ ≤ ‖grad f (γ t)‖` for `t ∈ [a, b)`, with `c > 0` and `θ < 1`, then the
Riemannian length of `γ` over `[a, b]` is at most `(f (γ a) - f p) ^ (1 - θ) / (c * (1 - θ))`. -/
theorem pathELength_maximalIntegralCurve_neg_mgradient_le_of_lojasiewicz
    (hf : ContMDiff I 𝓘(ℝ) 2 f) {a b : ℝ} (hab : a ≤ b)
    (hx : Icc a b ⊆ maximalIntegralCurveInterval (-mgradient I f) x) (hc : 0 < c) (hθ : θ < 1)
    (hb : ∀ t ∈ Icc a b, f p ≤ f (maximalIntegralCurve (-mgradient I f) x t))
    (hL : ∀ t ∈ Ico a b, c * (f (maximalIntegralCurve (-mgradient I f) x t) - f p) ^ θ ≤
      ‖mgradient I f (maximalIntegralCurve (-mgradient I f) x t)‖) :
    pathELength I (maximalIntegralCurve (-mgradient I f) x) a b ≤
      ENNReal.ofReal
        ((f (maximalIntegralCurve (-mgradient I f) x a) - f p) ^ (1 - θ) / (c * (1 - θ))) := by
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := 1)
  set γ := maximalIntegralCurve (-mgradient I f) x
  -- The length of `γ` is the integral of its speed `‖grad f (γ t)‖`.
  have hlen : pathELength I γ a b = ENNReal.ofReal (∫ t in a..b, ‖mgradient I f (γ t)‖) := by
    rw [ContMDiffOn.pathELength_eq_ofReal_integral_norm_curveVelocityWithin
      (contMDiffOn_maximalIntegralCurve_neg_mgradient hf) hx]
    refine congrArg ENNReal.ofReal (intervalIntegral.integral_congr fun t ht ↦ ?_)
    rw [uIcc_of_le hab] at ht
    simp only [curveVelocityWithin_of_mem_nhds (isOpen_maximalIntegralCurveInterval.mem_nhds
      (hx ht)), γ, curveVelocity_maximalIntegralCurve_neg_mgradient hf (hx ht), norm_neg]
  rw [hlen]
  refine ENNReal.ofReal_le_ofReal ((integral_le_rpow_sub_rpow_of_lojasiewicz hab hc hθ
    (fun t ht ↦ ((hasDerivAt_comp_maximalIntegralCurve_neg_mgradient hf (hx ht)).sub_const
      (f p)).hasDerivWithinAt) (fun t ht ↦ sub_nonneg.mpr (hb t ht)) hL).trans ?_)
  gcongr
  exact sub_le_self _ (Real.rpow_nonneg (sub_nonneg.mpr (hb b (right_mem_Icc.mpr hab))) _)

/-- **Trapping a trajectory where a Łojasiewicz inequality holds.** Let the maximal integral curve
`γ` of `-grad f` through `x` be defined for all positive time, with `f (γ t) ≥ f p` for `t ≥ 0`,
and let `c * |f y - f p| ^ θ ≤ ‖grad f y‖`, with `c > 0` and `θ < 1`, for all `y` at Riemannian
distance less than `δ` from `p`. If at some time `T ≥ 0` the distance from `p` to `γ T` plus
`(f (γ T) - f p) ^ (1 - θ) / (c * (1 - θ))` is less than `δ`, then `γ t` stays at distance less
than `δ` from `p` for all `t ≥ T`. -/
theorem riemannianEDist_maximalIntegralCurve_neg_mgradient_lt_of_lojasiewicz
    (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hx : Ici 0 ⊆ maximalIntegralCurveInterval (-mgradient I f) x) (hc : 0 < c) (hθ : θ < 1)
    (hb : ∀ t, 0 ≤ t → f p ≤ f (maximalIntegralCurve (-mgradient I f) x t)) {δ : ℝ≥0∞}
    (hL : ∀ y, riemannianEDist I p y < δ → c * |f y - f p| ^ θ ≤ ‖mgradient I f y‖)
    {T : ℝ} (hT : 0 ≤ T)
    (hTδ : riemannianEDist I p (maximalIntegralCurve (-mgradient I f) x T) +
      ENNReal.ofReal
        ((f (maximalIntegralCurve (-mgradient I f) x T) - f p) ^ (1 - θ) / (c * (1 - θ))) < δ)
    {t : ℝ} (ht : T ≤ t) :
    riemannianEDist I p (maximalIntegralCurve (-mgradient I f) x t) < δ := by
  have : IsManifold I 1 M := IsManifold.of_le one_le_two
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := 1)
  set γ := maximalIntegralCurve (-mgradient I f) x
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Ici 0) :=
    (contMDiffOn_maximalIntegralCurve_neg_mgradient hf).mono hx
  -- Up to any time `u ≥ T` before which `γ` stays in the ball, `γ u` is in the ball.
  have key : ∀ u, T ≤ u → (∀ s ∈ Ico T u, riemannianEDist I p (γ s) < δ) →
      riemannianEDist I p (γ u) < δ := by
    intro u hu hin
    have hsub : Icc T u ⊆ Ici 0 := fun s hs ↦ hT.trans hs.1
    calc riemannianEDist I p (γ u)
        ≤ riemannianEDist I p (γ T) + riemannianEDist I (γ T) (γ u) := riemannianEDist_triangle
      _ ≤ riemannianEDist I p (γ T) + pathELength I γ T u := by
          gcongr
          exact riemannianEDist_le_pathELength (hγ.mono hsub) rfl rfl hu
      _ ≤ riemannianEDist I p (γ T) + ENNReal.ofReal
            ((f (γ T) - f p) ^ (1 - θ) / (c * (1 - θ))) := by
          gcongr
          refine pathELength_maximalIntegralCurve_neg_mgradient_le_of_lojasiewicz hf hu
            (hsub.trans hx) hc hθ (fun s hs ↦ hb s (hsub hs)) fun s hs ↦ ?_
          simpa only [abs_of_nonneg (sub_nonneg.mpr (hb s (hsub (Ico_subset_Icc_self hs))))]
            using hL _ (hin s hs)
      _ < δ := hTδ
  -- Otherwise consider the first time `τ ∈ [T, t]` at which `γ` is outside the ball.
  by_contra hout
  set A := {s ∈ Icc T t | ¬ riemannianEDist I p (γ s) < δ}
  have hA : A.Nonempty := ⟨t, ⟨ht, le_rfl⟩, hout⟩
  have hAc : IsClosed A := by
    exact ContinuousOn.preimage_isClosed_of_isClosed
      (hγ.continuousOn.mono (Icc_subset_Ici_self.trans (Ici_subset_Ici.mpr hT))) isClosed_Icc
      (isOpen_setOfPred_riemannianEDist_lt I p δ).isClosed_compl
  have hAb : BddBelow A := ⟨T, fun s hs ↦ hs.1.1⟩
  have hτ : sInf A ∈ A := hAc.csInf_mem hA hAb
  exact hτ.2 (key _ hτ.1.1 fun s hs ↦ by_contra fun h ↦
    (csInf_le hAb ⟨⟨hs.1, hs.2.le.trans hτ.1.2⟩, h⟩).not_gt hs.2)

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
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  have : IsManifold I 1 M := IsManifold.of_le one_le_two
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := 1)
  set γ := maximalIntegralCurve (-mgradient I f) x
  set K := c * (1 - θ)
  have hb : ∀ t, 0 ≤ t → f p ≤ f (γ t) := fun t ht ↦
    le_comp_maximalIntegralCurve_neg_mgradient_of_mapClusterPt hf hx hp ht
  -- The excess term `(f y - f p) ^ (1 - θ) / K` is small near `p`.
  have hsmall : ∀ ε > (0 : ℝ≥0∞),
      ∀ᶠ y in 𝓝 p, ENNReal.ofReal ((f y - f p) ^ (1 - θ) / K) < ε := by
    intro ε hε
    have hcont : ContinuousAt (fun y ↦ ENNReal.ofReal ((f y - f p) ^ (1 - θ) / K)) p :=
      ENNReal.continuous_ofReal.continuousAt.comp (((Real.continuousAt_rpow_const _ _
        (Or.inr (sub_pos.mpr hθ).le)).comp
        (hf.continuous.continuousAt.sub continuousAt_const)).div_const K)
    refine hcont.eventually (gt_mem_nhds ?_)
    simpa [Real.zero_rpow (sub_pos.mpr hθ).ne'] using hε
  -- If the inequality holds on the ball of radius `δ` about `p`, the curve is eventually in it.
  have htrap : ∀ δ : ℝ≥0, 0 < δ → {y | riemannianEDist I p y < δ} ⊆
      {y | c * |f y - f p| ^ θ ≤ ‖mgradient I f y‖} →
      ∀ᶠ t in atTop, riemannianEDist I p (γ t) < δ := by
    intro δ hδ hδL
    have hδ2 : (0 : ℝ≥0∞) < (δ : ℝ≥0∞) / 2 := ENNReal.half_pos (by exact_mod_cast hδ.ne')
    obtain ⟨T, ⟨hTd, hTe⟩, hT⟩ := ((hp.frequently ((eventually_riemannianEDist_lt I p hδ2).and
      (hsmall _ hδ2))).and_eventually (eventually_ge_atTop 0)).exists
    filter_upwards [eventually_ge_atTop T] with t ht
    exact riemannianEDist_maximalIntegralCurve_neg_mgradient_lt_of_lojasiewicz hf hx hc hθ hb
      (fun y hy ↦ hδL hy) hT ((ENNReal.add_lt_add hTd hTe).trans_eq (ENNReal.add_halves _)) ht
  obtain ⟨δ₀, hδ₀, hδ₀L⟩ := setOfPred_riemannianEDist_lt_subset_nhds I hL
  have htend : Tendsto γ atTop (𝓝 p) := by
    intro V hV
    obtain ⟨δ, hδ, hδV⟩ := setOfPred_riemannianEDist_lt_subset_nhds I (inter_mem hV hL)
    exact mem_map.mpr (mem_of_superset (htrap δ hδ fun y hy ↦ (hδV hy).2)
      fun t ht ↦ (hδV ht).1)
  refine ⟨htend, ?_⟩
  -- For the bound, apply the length estimate along the tail spent in the ball of radius `δ₀`.
  obtain ⟨T, hT⟩ := eventually_atTop.mp ((htrap δ₀ hδ₀ hδ₀L).and (eventually_ge_atTop 0))
  filter_upwards [eventually_ge_atTop T] with t ht
  have ht0 : 0 ≤ t := (hT T le_rfl).2.trans ht
  refine riemannianEDist_le_of_tendsto_of_forall_pathELength_le
    ((contMDiffOn_maximalIntegralCurve_neg_mgradient hf).mono fun s hs ↦ hx (ht0.trans hs))
    htend fun s ↦ ?_
  refine (pathELength_mono le_rfl (le_max_left s t)).trans ?_
  refine pathELength_maximalIntegralCurve_neg_mgradient_le_of_lojasiewicz hf (le_max_right s t)
    (fun u hu ↦ hx (ht0.trans hu.1)) hc hθ (fun u hu ↦ hb u (ht0.trans hu.1)) fun u hu ↦ ?_
  simpa only [mem_ofPred_eq, abs_of_nonneg (sub_nonneg.mpr (hb u (ht0.trans hu.1)))] using
    hδ₀L (hT u (ht.trans hu.1)).1

end SymplecticGeometry

end
