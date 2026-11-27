/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.GradientFlow
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.Calculus.Lojasiewicz
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

If instead the forward part of `γ` stays in a compact set `K`, and such an inequality holds near
each critical point of `f` in `K`, with constants depending on the point, then `γ` exists for all
positive time and converges to a critical point in `K`, with the same bound
(`SymplecticGeometry.exists_tendsto_maximalIntegralCurve_neg_mgradient_of_lojasiewicz`). The
trapped trajectory exists for all positive time
(`TauCeti.Ici_subset_maximalIntegralCurveInterval_neg_mgradient`) and has a cluster point in `K`,
which is critical (`TauCeti.mem_criticalPoints_of_mapClusterPt_maximalIntegralCurve_neg_mgradient`);
the first theorem applies there. This follows the proof of Tau Ceti's
`exists_tendsto_and_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient_of_lojasiewicz`,
the case `θ = 1 / 2` with an exponential bound.

Under the hypotheses of the first theorem, the speed `‖grad f (γ t)‖` of `γ` is integrable on
`(0, ∞)` (`SymplecticGeometry.integrableOn_Ioi_norm_mgradient_maximalIntegralCurve_of_lojasiewicz`):
once `γ` stays where the inequality holds, from a time `T` on, Tau Ceti's scalar bound
`TauCeti.integral_le_rpow_sub_rpow_of_lojasiewicz`, applied to the excess `e t = f (γ t) - f p`
with derivative `-‖grad f (γ t)‖ ^ 2`, bounds the integral of the speed over `[T, b]` uniformly
in `b`. This adapts the proof of Tau Ceti's
`IsIntegralCurveOn.integrableOn_norm_gradient_Ioi_of_lojasiewicz`, with its private step
`integral_norm_gradient_le_of_lojasiewicz_of_le`, from integral curves of a gradient on a Hilbert
space to maximal integral curves of `-grad f` on a manifold. The excess is integrable too
(`SymplecticGeometry.integrableOn_Ioi_sub_comp_maximalIntegralCurve_of_lojasiewicz`), since `e`
decreases, so that after `T` we have `c * e = e ^ (1 - θ) * (c * e ^ θ) ≤ e 0 ^ (1 - θ) * ‖grad f‖`.
For `θ = 1 / 2` the energy identity would do, but for `θ > 1 / 2` the excess is not bounded by a
multiple of `‖grad f‖ ^ 2`, and the finite length of `γ` is what is needed.

## Main results

* `SymplecticGeometry.tendsto_maximalIntegralCurve_neg_mgradient_of_lojasiewicz`: convergence to
  a cluster point at which a Łojasiewicz inequality holds, with the tail bound on the distance.
* `SymplecticGeometry.exists_tendsto_maximalIntegralCurve_neg_mgradient_of_lojasiewicz`: a
  trajectory trapped in a compact set where the inequality holds near every critical point
  converges to one of them, with the same bound.
* `SymplecticGeometry.integrableOn_Ioi_norm_mgradient_maximalIntegralCurve_of_lojasiewicz`,
  `SymplecticGeometry.integrableOn_Ioi_sub_comp_maximalIntegralCurve_of_lojasiewicz`: the speed of
  such a trajectory, and the excess of `f` over its value at the limit, are integrable on
  `(0, ∞)`.

## References

* S. Łojasiewicz, *Une propriété topologique des sous-ensembles analytiques réels*, Les Équations
  aux Dérivées Partielles, Éditions du CNRS, Paris, 1963, 87–89.
* E. Lerman, *Gradient flow of the norm squared of a moment map*, Enseign. Math. 51 (2005),
  117–127, proof of Theorem 1.1.
-/

public section

open Bundle Filter Manifold MeasureTheory Set Topology TauCeti TauCeti.Manifold
open scoped ContDiff ENNReal Manifold

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I 2 M]
  [BoundarylessManifold I M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {f : M → ℝ} {x p : M} {K : Set M} {c θ : ℝ}

/-- **Convergence of a negative gradient trajectory under a Łojasiewicz inequality.** Let `f` be
a `C²` function on a boundaryless finite-dimensional manifold with a `C¹` Riemannian metric, and
let the maximal integral curve `γ` of `-grad f` through `x` be defined for all positive time. If
`p` is a cluster point of `γ t` as `t → ∞` and near `p` the inequality
`c * |f y - f p| ^ θ ≤ ‖grad f y‖` holds, with `c > 0` and `θ < 1`, then `γ` converges to `p`,
and for all large `t` the Riemannian distance from `γ t` to `p` is at most
`(f (γ t) - f p) ^ (1 - θ) / (c * (1 - θ))`.

For a trajectory whose forward part lies in a compact set, for instance any trajectory on a
compact manifold, use
`SymplecticGeometry.exists_tendsto_maximalIntegralCurve_neg_mgradient_of_lojasiewicz`, which
needs neither global existence nor a cluster point as a hypothesis. -/
theorem tendsto_maximalIntegralCurve_neg_mgradient_of_lojasiewicz (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hx : Ici 0 ⊆ maximalIntegralCurveInterval (-mgradient I f) x)
    (hp : MapClusterPt p atTop (maximalIntegralCurve (-mgradient I f) x)) (hc : 0 < c)
    (hθ : θ < 1) (hL : ∀ᶠ y in 𝓝 p, c * |f y - f p| ^ θ ≤ ‖mgradient I f y‖) :
    Tendsto (maximalIntegralCurve (-mgradient I f) x) atTop (𝓝 p) ∧
      ∀ᶠ t in atTop, riemannianEDist I (maximalIntegralCurve (-mgradient I f) x t) p ≤
        ENNReal.ofReal
          ((f (maximalIntegralCurve (-mgradient I f) x t) - f p) ^ (1 - θ) / (c * (1 - θ))) := by
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

/-- **Convergence of a trapped negative gradient trajectory under Łojasiewicz inequalities.** Let
`f` be a `C²` function on a boundaryless finite-dimensional manifold with a `C¹` Riemannian
metric, and let the forward part of the maximal integral curve `γ` of `-grad f` through `x` stay
in a compact set `K`. Suppose that near every critical point `q` of `f` in `K` an inequality
`c * |f y - f q| ^ θ ≤ ‖grad f y‖` holds, for some `c > 0` and `θ < 1` that may depend on `q`.
Then `γ` is defined for all `t ≥ 0` and converges to a critical point `p` of `f` in `K`.
Moreover, whenever `c * |f y - f p| ^ θ ≤ ‖grad f y‖` holds near `p`, with `c > 0` and `θ < 1`,
the Riemannian distance from `γ t` to `p` is at most `(f (γ t) - f p) ^ (1 - θ) / (c * (1 - θ))`
for all large `t`. The critical points in `K` need not be isolated. -/
theorem exists_tendsto_maximalIntegralCurve_neg_mgradient_of_lojasiewicz
    (hf : ContMDiff I 𝓘(ℝ) 2 f) (hK : IsCompact K)
    (hmem : MapsTo (maximalIntegralCurve (-mgradient I f) x)
      (maximalIntegralCurveInterval (-mgradient I f) x ∩ Ici 0) K)
    (hL : ∀ q ∈ criticalPoints I f ∩ K, ∃ θ < (1 : ℝ), ∃ c > 0,
      ∀ᶠ y in 𝓝 q, c * |f y - f q| ^ θ ≤ ‖mgradient I f y‖) :
    Ici 0 ⊆ maximalIntegralCurveInterval (-mgradient I f) x ∧
      ∃ p ∈ criticalPoints I f ∩ K,
        Tendsto (maximalIntegralCurve (-mgradient I f) x) atTop (𝓝 p) ∧
        ∀ ⦃c θ : ℝ⦄, 0 < c → θ < 1 →
          (∀ᶠ y in 𝓝 p, c * |f y - f p| ^ θ ≤ ‖mgradient I f y‖) → ∀ᶠ t in atTop,
            riemannianEDist I (maximalIntegralCurve (-mgradient I f) x t) p ≤
              ENNReal.ofReal
                ((f (maximalIntegralCurve (-mgradient I f) x t) - f p) ^ (1 - θ) /
                  (c * (1 - θ))) := by
  have hx := Ici_subset_maximalIntegralCurveInterval_neg_mgradient hK hmem hf
  -- The trajectory has a cluster point in `K`, which is critical.
  obtain ⟨p, hpK, hp⟩ := hK.exists_mapClusterPt (f := atTop)
    (u := maximalIntegralCurve (-mgradient I f) x) (tendsto_principal.2
      (by filter_upwards [eventually_ge_atTop 0] with t ht using hmem ⟨hx ht, ht⟩))
  have hpc : p ∈ criticalPoints I f ∩ K :=
    ⟨mem_criticalPoints_of_mapClusterPt_maximalIntegralCurve_neg_mgradient hK hmem hf hp, hpK⟩
  obtain ⟨θ, hθ, c, hc, hLp⟩ := hL p hpc
  exact ⟨hx, p, hpc, (tendsto_maximalIntegralCurve_neg_mgradient_of_lojasiewicz hf hx hp hc hθ
    hLp).1, fun c' θ' hc' hθ' hL' ↦
      (tendsto_maximalIntegralCurve_neg_mgradient_of_lojasiewicz hf hx hp hc' hθ' hL').2⟩

/-- **A negative gradient trajectory under a Łojasiewicz inequality has integrable speed.** In the
setting of `tendsto_maximalIntegralCurve_neg_mgradient_of_lojasiewicz`, the length
`‖grad f (γ t)‖` of the velocity of `γ` is integrable on `(0, ∞)`. -/
theorem integrableOn_Ioi_norm_mgradient_maximalIntegralCurve_of_lojasiewicz
    (hf : ContMDiff I 𝓘(ℝ) 2 f) (hx : Ici 0 ⊆ maximalIntegralCurveInterval (-mgradient I f) x)
    (hp : MapClusterPt p atTop (maximalIntegralCurve (-mgradient I f) x)) (hc : 0 < c)
    (hθ : θ < 1) (hL : ∀ᶠ y in 𝓝 p, c * |f y - f p| ^ θ ≤ ‖mgradient I f y‖) :
    IntegrableOn (fun t ↦ ‖mgradient I f (maximalIntegralCurve (-mgradient I f) x t)‖)
      (Ioi 0) := by
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := 1)
  set γ := maximalIntegralCurve (-mgradient I f) x
  have htend : Tendsto γ atTop (𝓝 p) :=
    (tendsto_maximalIntegralCurve_neg_mgradient_of_lojasiewicz hf hx hp hc hθ hL).1
  have hb (s : ℝ) (hs : 0 ≤ s) : 0 ≤ f (γ s) - f p :=
    sub_nonneg.mpr (le_comp_maximalIntegralCurve_neg_mgradient hf hx hp hs)
  have hgc : ContinuousOn (fun t ↦ ‖mgradient I f (γ t)‖) (Ici 0) :=
    (continuous_norm_mgradient (hf.of_le one_le_two)).comp_continuousOn
      ((contMDiffOn_maximalIntegralCurve_neg_mgradient hf).continuousOn.mono hx)
  -- After some time `T ≥ 0` the trajectory stays where the inequality holds.
  obtain ⟨T, hT⟩ := eventually_atTop.mp ((htend.eventually hL).and (eventually_ge_atTop 0))
  have hT0 : 0 ≤ T := (hT T le_rfl).2
  have hTi : IntegrableOn (fun t ↦ ‖mgradient I f (γ t)‖) (Ioi T) := by
    refine integrableOn_Ioi_of_intervalIntegral_norm_bounded
      ((f (γ T) - f p) ^ (1 - θ) / (c * (1 - θ))) T (b := id) (l := atTop)
      (fun b ↦ ((hgc.mono (Icc_subset_Ici_self.trans (Ici_subset_Ici.mpr hT0))).integrableOn_Icc
        (b := b)).mono_set Ioc_subset_Icc_self) tendsto_id ?_
    filter_upwards [eventually_ge_atTop T] with b hTb
    simp only [id, norm_norm]
    refine (integral_le_rpow_sub_rpow_of_lojasiewicz hTb hc hθ (fun t ht ↦
      ((hasDerivAt_comp_maximalIntegralCurve_neg_mgradient hf (hx (hT0.trans ht.1))).sub_const
        (f p)).hasDerivWithinAt) (fun t ht ↦ hb t (hT0.trans ht.1)) fun t ht ↦ ?_).trans ?_
    · simpa only [abs_of_nonneg (hb t (hT0.trans ht.1))] using (hT t ht.1).1
    · gcongr
      exact sub_le_self _ (Real.rpow_nonneg (hb b (hT0.trans hTb)) _)
  rw [← Ioc_union_Ioi_eq_Ioi hT0]
  exact ((hgc.mono Icc_subset_Ici_self).integrableOn_Icc.mono_set Ioc_subset_Icc_self).union hTi

/-- **The excess of a negative gradient trajectory under a Łojasiewicz inequality is
integrable.** In the setting of `tendsto_maximalIntegralCurve_neg_mgradient_of_lojasiewicz`, the
excess `f (γ t) - f p` of `f` along `γ` over its value at the limit `p` is integrable on
`(0, ∞)`. -/
theorem integrableOn_Ioi_sub_comp_maximalIntegralCurve_of_lojasiewicz
    (hf : ContMDiff I 𝓘(ℝ) 2 f) (hx : Ici 0 ⊆ maximalIntegralCurveInterval (-mgradient I f) x)
    (hp : MapClusterPt p atTop (maximalIntegralCurve (-mgradient I f) x)) (hc : 0 < c)
    (hθ : θ < 1) (hL : ∀ᶠ y in 𝓝 p, c * |f y - f p| ^ θ ≤ ‖mgradient I f y‖) :
    IntegrableOn (fun t ↦ f (maximalIntegralCurve (-mgradient I f) x t) - f p) (Ioi 0) := by
  set γ := maximalIntegralCurve (-mgradient I f) x
  set e : ℝ → ℝ := fun t ↦ f (γ t) - f p
  have htend : Tendsto γ atTop (𝓝 p) :=
    (tendsto_maximalIntegralCurve_neg_mgradient_of_lojasiewicz hf hx hp hc hθ hL).1
  have hb (s : ℝ) (hs : 0 ≤ s) : 0 ≤ f (γ s) - f p :=
    sub_nonneg.mpr (le_comp_maximalIntegralCurve_neg_mgradient hf hx hp hs)
  have hec : ContinuousOn e (Ici 0) :=
    (hf.continuous.comp_continuousOn
      ((contMDiffOn_maximalIntegralCurve_neg_mgradient hf).continuousOn.mono hx)).sub
      continuousOn_const
  have hg := integrableOn_Ioi_norm_mgradient_maximalIntegralCurve_of_lojasiewicz hf hx hp hc hθ hL
  obtain ⟨T, hT⟩ := eventually_atTop.mp ((htend.eventually hL).and (eventually_ge_atTop 0))
  have hT0 : 0 ≤ T := (hT T le_rfl).2
  -- After `T`, `c * e = e ^ (1 - θ) * (c * e ^ θ) ≤ e 0 ^ (1 - θ) * ‖grad f‖`.
  have hTi : IntegrableOn e (Ioi T) := by
    refine ((hg.mono_set (Ioi_subset_Ioi hT0)).const_mul (e 0 ^ (1 - θ) / c)).mono'
      ((hec.mono fun s hs ↦ hT0.trans (le_of_lt hs)).aestronglyMeasurable measurableSet_Ioi)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht ↦ ?_))
    have ht0 : 0 ≤ t := hT0.trans (le_of_lt ht)
    have he0 := hb t ht0
    have hanti : f (γ t) - f p ≤ f (γ 0) - f p := sub_le_sub_right
      (antitoneOn_comp_maximalIntegralCurve_neg_mgradient hf (hx le_rfl) (hx ht0) ht0) _
    have hL' : c * (f (γ t) - f p) ^ θ ≤ ‖mgradient I f (γ t)‖ := by
      simpa only [abs_of_nonneg he0] using (hT t (le_of_lt ht)).1
    rw [Real.norm_of_nonneg he0, div_mul_eq_mul_div, le_div_iff₀ hc]
    calc (f (γ t) - f p) * c = (f (γ t) - f p) ^ (1 - θ) * (c * (f (γ t) - f p) ^ θ) := by
          rw [mul_left_comm, ← Real.rpow_add' he0 (by norm_num), sub_add_cancel, Real.rpow_one,
            mul_comm]
      _ ≤ (f (γ 0) - f p) ^ (1 - θ) * ‖mgradient I f (γ t)‖ := by
          gcongr
          exact Real.rpow_nonneg (hb 0 le_rfl) _
  rw [← Ioc_union_Ioi_eq_Ioi hT0]
  exact ((hec.mono Icc_subset_Ici_self).integrableOn_Icc.mono_set Ioc_subset_Icc_self).union hTi

end SymplecticGeometry

end
