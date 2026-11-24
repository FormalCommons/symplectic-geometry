/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Riemannian.PathELength
public import TauCeti.Geometry.Manifold.Morse.GradientFlow
import SymplecticGeometry.Geometry.Manifold.Morse.GradientFlow
import SymplecticGeometry.Geometry.Manifold.Riemannian.Distance
import TauCeti.Analysis.Calculus.Lojasiewicz
import TauCeti.Analysis.Calculus.Lojasiewicz.Comparison
import TauCeti.Geometry.Manifold.Riemannian.ArcLength
import TauCeti.Geometry.Manifold.Riemannian.Distance
import TauCeti.Topology.Order.Interval

/-!
# Łojasiewicz's convergence theorem for negative gradient trajectories on a manifold

This file is a part of Tau Ceti's `TauCeti/Geometry/Manifold/Morse/ExponentialConvergence.lean`,
copied from Tau Ceti's main branch at commit `07c8b6b1f5ff5bdab8363e207e59d68eccc82bef`. The
pinned version of Tau Ceti does not have Łojasiewicz's convergence theorem yet.

Let `f` be a `C²` function on a boundaryless finite-dimensional manifold `M` with a `C¹`
Riemannian metric, and let `γ` be the maximal integral curve of `-grad f` through `x`. Along any
stretch of time during which `γ` stays where a Łojasiewicz inequality `c * e ^ θ ≤ ‖grad f‖` holds
for the excess `e = f (γ t) - f p`, with `c > 0` and `θ < 1`, we have `e' = -‖grad f‖²`, so the
length of `γ` over that stretch is at most `1 / (c * (1 - θ))` times the drop of `e ^ (1 - θ)`
(`TauCeti.pathELength_maximalIntegralCurve_neg_mgradient_le_of_lojasiewicz`, from the scalar
bound `TauCeti.integral_le_rpow_sub_rpow_of_lojasiewicz`).

**Łojasiewicz's convergence theorem**
(`TauCeti.tendsto_maximalIntegralCurve_neg_mgradient_of_mapClusterPt`) says that a forward
trajectory converges to each of its cluster points `p` near which a Łojasiewicz inequality
`c * |f y - f p| ^ θ ≤ ‖grad f y‖` holds, for any exponent `θ < 1`. Here `p` is only a cluster
point, but `f` still stays above `f p` along `γ`
(`TauCeti.le_comp_maximalIntegralCurve_neg_mgradient`), so the length bound applies. Once `γ`
comes close enough to `p`, at a time when `e ^ (1 - θ)` is small, it cannot travel far enough to
leave a Riemannian ball about `p` on which the inequality holds, and its remaining length is
small. Nothing is assumed about the other critical points: they need not be isolated.

A Łojasiewicz inequality with exponent `1/2` in the preferred chart at `p` gives one for the
Riemannian gradient
(`TauCeti.exists_mul_abs_sub_le_norm_mgradient_sq_of_fderiv_comp_extChartAt_symm`), since in
that chart the differential of `f` is bounded by a multiple of the length of its gradient
(`TauCeti.Manifold.eventually_norm_fderiv_comp_extChartAt_symm_le_mul_norm_mgradient`).

Changes from Tau Ceti's file: only the three theorems listed below and the two private steps of
their proofs, `pathELength_le_of_forall_abs_le` and `riemannianEDist_lt_of_lojasiewicz`, are taken,
with the sections and `variable` lines they need and the imports they use; this module docstring
replaces Tau Ceti's, and keeps the parts of its text that concern these declarations. The
declarations `TauCeti.le_comp_maximalIntegralCurve_neg_mgradient` and
`TauCeti.tendsto_comp_maximalIntegralCurve_neg_mgradient` of Tau Ceti's `GradientFlow.lean`, and
`TauCeti.Manifold.isOpen_setOfPred_riemannianEDist_lt` of its `Riemannian/Distance.lean`, at the
same commit, come from this library's copies of those files. The declarations, their docstrings
and their proofs are unchanged.

Since it imports the copy of `GradientFlow.lean`, this file cannot be imported together with the
pinned `TauCeti/Geometry/Manifold/Morse/ExponentialConvergence.lean`, nor with any file that
imports it, such as the pinned `TauCeti/Geometry/Manifold/Morse/Bott/ExponentialConvergence.lean`:
both declare `TauCeti.le_comp_maximalIntegralCurve_neg_mgradient`. The pinned
`TauCeti/Geometry/Manifold/Morse/ExponentialConvergence.lean` also declares
`TauCeti.exists_mul_abs_sub_le_norm_mgradient_sq_of_fderiv_comp_extChartAt_symm`; it is copied here
so that the Morse–Bott inequality can be stated next to these theorems, in this library's copy of
`TauCeti/Geometry/Manifold/Morse/Bott/ExponentialConvergence.lean`.

## Main results

* `TauCeti.exists_mul_abs_sub_le_norm_mgradient_sq_of_fderiv_comp_extChartAt_symm`: a
  Łojasiewicz inequality with exponent `1/2` in the preferred chart at `p` gives one for the
  Riemannian gradient.
* `TauCeti.pathELength_maximalIntegralCurve_neg_mgradient_le_of_lojasiewicz`: Łojasiewicz's
  bound on the length of a trajectory along which a Łojasiewicz inequality with any exponent
  `θ < 1` holds.
* `TauCeti.tendsto_maximalIntegralCurve_neg_mgradient_of_mapClusterPt`: Łojasiewicz's convergence
  theorem, a forward trajectory converges to a cluster point near which a Łojasiewicz inequality
  with any exponent `θ < 1` holds.

## References

* S. Łojasiewicz, *Une propriété topologique des sous-ensembles analytiques réels*, Les Équations
  aux Dérivées Partielles, Éditions du CNRS, Paris, 1963, 87--89.
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2.
-/

public section

open Bundle Filter MeasureTheory Set Topology TauCeti.Manifold
open scoped ContDiff ENNReal Manifold NNReal

namespace TauCeti

section Lojasiewicz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  {f : M → ℝ} {p : M}

/-- **Łojasiewicz's gradient inequality passes from the preferred chart to the Riemannian
gradient.** If near `p` the absolute energy difference `|f y - f p|` is bounded by a multiple of
the squared norm of the differential of `f` read in the preferred extended chart at `p`, then it is
bounded by a multiple of the squared Riemannian length of the gradient of `f` at `y`, for any
continuous Riemannian metric. -/
theorem exists_mul_abs_sub_le_norm_mgradient_sq_of_fderiv_comp_extChartAt_symm
    (h : ∃ lam > 0, ∀ᶠ y in 𝓝 p, lam * |f y - f p| ≤
      ‖fderiv ℝ (f ∘ (extChartAt I p).symm) (extChartAt I p y)‖ ^ 2) :
    ∃ lam > 0, ∀ᶠ y in 𝓝 p, lam * |f y - f p| ≤ ‖mgradient I f y‖ ^ 2 := by
  obtain ⟨C, -, hbd⟩ :=
    eventually_norm_fderiv_comp_extChartAt_symm_le_mul_norm_mgradient (I := I) p
  exact exists_mul_le_sq_of_eventually_le_mul h (.of_forall fun _ ↦ norm_nonneg _)
    (hbd.mono fun y hy ↦ hy f)

end Lojasiewicz

section Decay

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I 2 M]
  [BoundarylessManifold I M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {f : M → ℝ} {x p : M}

/-! ### Length of a trajectory and distance to its limit -/

/-- **Łojasiewicz's length bound.** Let the maximal integral curve `γ` of `-grad f` through `x` be
defined on `[a, b]`, and let `c ≤ f (γ b)`. If `c₀ * (f (γ t) - c) ^ θ ≤ ‖grad f (γ t)‖` for
`t ∈ [a, b)`, with `c₀ > 0` and `θ < 1`, then the Riemannian length of `γ` on `[a, b]` is at most
`((f (γ a) - c) ^ (1 - θ) - (f (γ b) - c) ^ (1 - θ)) / (c₀ * (1 - θ))`. -/
theorem pathELength_maximalIntegralCurve_neg_mgradient_le_of_lojasiewicz
    (hf : ContMDiff I 𝓘(ℝ) 2 f) {a b c θ c₀ : ℝ} (hθ : θ < 1) (hc₀ : 0 < c₀) (hab : a ≤ b)
    (hsub : Icc a b ⊆ maximalIntegralCurveInterval (-mgradient I f) x)
    (hc : c ≤ f (maximalIntegralCurve (-mgradient I f) x b))
    (hloj : ∀ t ∈ Ico a b, c₀ * (f (maximalIntegralCurve (-mgradient I f) x t) - c) ^ θ ≤
      ‖mgradient I f (maximalIntegralCurve (-mgradient I f) x t)‖) :
    Manifold.pathELength I (maximalIntegralCurve (-mgradient I f) x) a b ≤
      ENNReal.ofReal (((f (maximalIntegralCurve (-mgradient I f) x a) - c) ^ (1 - θ) -
        (f (maximalIntegralCurve (-mgradient I f) x b) - c) ^ (1 - θ)) / (c₀ * (1 - θ))) := by
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := 1)
  have : IsManifold I 1 M := IsManifold.of_le one_le_two
  set γ := maximalIntegralCurve (-mgradient I f) x
  set e : ℝ → ℝ := fun t ↦ f (γ t) - c
  set g : ℝ → ℝ := fun t ↦ ‖mgradient I f (γ t)‖
  -- The excess `e` of `f` over `c` has derivative `-g²` and stays nonnegative.
  have he : ∀ t ∈ Icc a b, HasDerivWithinAt e (-g t ^ 2) (Icc a b) t := fun t ht ↦
    ((hasDerivAt_comp_maximalIntegralCurve_neg_mgradient hf (hsub ht)).sub_const
      c).hasDerivWithinAt
  have he₀ : ∀ t ∈ Icc a b, 0 ≤ e t := fun t ht ↦ sub_nonneg.2 (hc.trans
    (antitoneOn_comp_maximalIntegralCurve_neg_mgradient hf (hsub ht)
      (hsub (right_mem_Icc.2 hab)) ht.2))
  -- The length of `γ` is the integral of its speed `g`.
  have hspeed : ∀ t ∈ uIcc a b,
      ‖curveVelocityWithin I γ (maximalIntegralCurveInterval (-mgradient I f) x) t‖ = g t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    rw [curveVelocityWithin_of_mem_nhds (isOpen_maximalIntegralCurveInterval.mem_nhds (hsub ht)),
      curveVelocity_maximalIntegralCurve_neg_mgradient hf (hsub ht), norm_neg]
  rw [(contMDiffOn_maximalIntegralCurve_neg_mgradient
    hf).pathELength_eq_ofReal_integral_norm_curveVelocityWithin hsub,
    intervalIntegral.integral_congr hspeed]
  exact ENNReal.ofReal_le_ofReal (integral_le_rpow_sub_rpow_of_lojasiewicz hab hc₀ hθ he he₀ hloj)

/-- The length bound of `pathELength_maximalIntegralCurve_neg_mgradient_le_of_lojasiewicz` with
`c = f p`, in the form used for convergence to an ω-limit point `p`, below which `f` stays along
the trajectory. -/
private theorem pathELength_le_of_forall_abs_le (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hx : Ici 0 ⊆ maximalIntegralCurveInterval (-mgradient I f) x)
    (hle : ∀ t ∈ Ici (0 : ℝ), f p ≤ f (maximalIntegralCurve (-mgradient I f) x t))
    {θ c₀ : ℝ} (hθ : θ < 1) (hc₀ : 0 < c₀) {t s : ℝ} (ht : 0 ≤ t) (hts : t ≤ s)
    (hloj : ∀ u ∈ Ico t s, c₀ * |f (maximalIntegralCurve (-mgradient I f) x u) - f p| ^ θ ≤
      ‖mgradient I f (maximalIntegralCurve (-mgradient I f) x u)‖) :
    Manifold.pathELength I (maximalIntegralCurve (-mgradient I f) x) t s ≤
      ENNReal.ofReal
        ((f (maximalIntegralCurve (-mgradient I f) x t) - f p) ^ (1 - θ) / (c₀ * (1 - θ))) := by
  refine (pathELength_maximalIntegralCurve_neg_mgradient_le_of_lojasiewicz hf hθ hc₀ hts
    (fun u hu ↦ hx (ht.trans hu.1)) (hle s (ht.trans hts)) fun u hu ↦ ?_).trans
    (ENNReal.ofReal_le_ofReal ?_)
  · simpa only [abs_of_nonneg (sub_nonneg.2 (hle u (ht.trans hu.1)))] using hloj u hu
  · exact div_le_div_of_nonneg_right (sub_le_self _ (Real.rpow_nonneg
      (sub_nonneg.2 (hle s (ht.trans hts))) _)) (mul_pos hc₀ (sub_pos.2 hθ)).le

end Decay

/-! ### Convergence to an ω-limit point with a Łojasiewicz inequality -/

section ClusterPoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I 2 M]
  [BoundarylessManifold I M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {f : M → ℝ} {x p : M}

/-- **A trajectory cannot leave a Łojasiewicz ball once it is deep inside.** Let `f` stay above
`f p` along the forward trajectory `γ` of `-grad f`, and let the Łojasiewicz inequality hold on the
Riemannian ball of radius `r` about `p`. If at some time `t₀ ≥ 0` the point `γ t₀` lies within
`r / 2` of `p` and the length bound `(f (γ t₀) - f p) ^ (1 - θ) / (c * (1 - θ))` is at most
`r / 2`, then `γ`
stays in the ball after `t₀`: at a first exit time `τ`, the length of `γ` on `[t₀, τ]` would be at
most `r / 2`, which keeps `γ τ` inside the ball. -/
private theorem riemannianEDist_lt_of_lojasiewicz (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hx : Ici 0 ⊆ maximalIntegralCurveInterval (-mgradient I f) x)
    (hle : ∀ t ∈ Ici (0 : ℝ), f p ≤ f (maximalIntegralCurve (-mgradient I f) x t))
    {θ c : ℝ} (hθ : θ < 1) (hc : 0 < c) {r : ℝ≥0}
    (hrU : ∀ y, Manifold.riemannianEDist I p y < r → c * |f y - f p| ^ θ ≤ ‖mgradient I f y‖)
    {t₀ : ℝ} (ht₀0 : 0 ≤ t₀)
    (ht₀ : Manifold.riemannianEDist I p (maximalIntegralCurve (-mgradient I f) x t₀) < r / 2)
    (hL : ENNReal.ofReal ((f (maximalIntegralCurve (-mgradient I f) x t₀) - f p) ^ (1 - θ) /
      (c * (1 - θ))) ≤ r / 2)
    {s : ℝ} (hs : t₀ ≤ s) :
    Manifold.riemannianEDist I p (maximalIntegralCurve (-mgradient I f) x s) < r := by
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := 1)
  have : IsManifold I 1 M := IsManifold.of_le one_le_two
  set γ := maximalIntegralCurve (-mgradient I f) x
  have hγ₀ : ∀ {s}, CMDiff[Icc t₀ s] 1 γ :=
    (contMDiffOn_maximalIntegralCurve_neg_mgradient hf).mono
      (Icc_subset_Ici_self.trans ((Ici_subset_Ici.2 ht₀0).trans hx))
  by_contra! hsr
  -- The first time `τ ∈ [t₀, s]` at which `γ` is outside the ball.
  obtain ⟨τ, hτ, -, hτV, -, hin⟩ :=
    (Manifold.isOpen_setOfPred_riemannianEDist_lt I p r).exists_first_exit hγ₀.continuousOn
      (ht₀.trans_le ENNReal.half_le_self) ⟨s, ⟨hs, le_rfl⟩, not_lt.2 hsr⟩
  -- Before `τ` the trajectory stays in the ball, so its length on `[t₀, τ]` is at most `r / 2`.
  have hdist : Manifold.riemannianEDist I (γ t₀) (γ τ) ≤ r / 2 :=
    (Manifold.riemannianEDist_le_pathELength hγ₀ rfl rfl hτ.1).trans
      ((pathELength_le_of_forall_abs_le hf hx hle hθ hc ht₀0 hτ.1 fun u hu ↦
        hrU _ (hin u hu)).trans hL)
  refine hτV ?_
  calc Manifold.riemannianEDist I p (γ τ)
      ≤ Manifold.riemannianEDist I p (γ t₀) + Manifold.riemannianEDist I (γ t₀) (γ τ) :=
        Manifold.riemannianEDist_triangle
    _ < r / 2 + r / 2 :=
        ENNReal.add_lt_add_of_lt_of_le (ne_top_of_le_ne_top (by finiteness) hdist) ht₀ hdist
    _ = r := ENNReal.add_halves _

/-- **Łojasiewicz's convergence theorem.** If the maximal integral curve `γ` of `-grad f` through
`x` exists for all positive time and has a cluster point `p` as `t → ∞` near which
`c * |f y - f p| ^ θ ≤ ‖grad f y‖` for some `θ < 1` and `c > 0`, then `γ` converges to `p`.

The inequality holds with `θ = 1 / 2` near a nondegenerate critical point
(`TauCeti.IsManifoldNondegenerateCriticalPoint.exists_mul_abs_sub_le_norm_mgradient_sq`) and near
a point of a Morse–Bott critical submanifold
(`SmoothEmbedding.IsNondegenerateCriticalSubmanifold.exists_mul_abs_sub_le_norm_mgradient_sq`),
where the critical points need not be isolated. -/
theorem tendsto_maximalIntegralCurve_neg_mgradient_of_mapClusterPt
    (hf : ContMDiff I 𝓘(ℝ) 2 f) (hx : Ici 0 ⊆ maximalIntegralCurveInterval (-mgradient I f) x)
    (hp : MapClusterPt p atTop (maximalIntegralCurve (-mgradient I f) x))
    (hloj : ∃ θ < (1 : ℝ), ∃ c > 0, ∀ᶠ y in 𝓝 p, c * |f y - f p| ^ θ ≤ ‖mgradient I f y‖) :
    Tendsto (maximalIntegralCurve (-mgradient I f) x) atTop (𝓝 p) := by
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := 1)
  have : IsManifold I 1 M := IsManifold.of_le one_le_two
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  set γ := maximalIntegralCurve (-mgradient I f) x
  obtain ⟨θ, hθ, c, hc, hU⟩ := hloj
  have hle : ∀ t ∈ Ici (0 : ℝ), f p ≤ f (γ t) := fun t ht ↦
    le_comp_maximalIntegralCurve_neg_mgradient hf hx hp ht
  -- The bound on the length of `γ` after time `t` tends to `0`, since `f (γ t) → f p`.
  have hL0 : Tendsto (fun t ↦ ENNReal.ofReal ((f (γ t) - f p) ^ (1 - θ) / (c * (1 - θ)))) atTop
      (𝓝 0) := by
    have hlim : Tendsto (fun t ↦ f (γ t) - f p) atTop (𝓝 (f p - f p)) :=
      (tendsto_comp_maximalIntegralCurve_neg_mgradient hf hx hp).sub_const _
    rw [sub_self] at hlim
    have h := ENNReal.tendsto_ofReal (((Real.continuousAt_rpow_const 0 (1 - θ)
      (Or.inr (sub_pos.2 hθ).le)).tendsto.comp hlim).div_const (c * (1 - θ)))
    rwa [Real.zero_rpow (sub_pos.2 hθ).ne', zero_div, ENNReal.ofReal_zero] at h
  -- Choose a radius `r` such that the Riemannian ball of radius `r` about `p` lies where the
  -- Łojasiewicz inequality holds, then a time `t₀ ≥ 0` at which `γ` is within `r / 2` of `p` and
  -- after which the length bound is at most `r / 2`. After `t₀` the trajectory stays in the ball.
  obtain ⟨r, hr, hrU⟩ := setOfPred_riemannianEDist_lt_subset_nhds I hU
  have hr2 : (0 : ℝ≥0∞) < (r : ℝ≥0∞) / 2 := ENNReal.half_pos (by exact_mod_cast hr.ne')
  obtain ⟨T, hT⟩ := eventually_atTop.1
    ((ENNReal.tendsto_nhds_zero.1 hL0 _ hr2).and (eventually_ge_atTop 0))
  obtain ⟨t₀, ht₀, ht₀T⟩ := ((hp.frequently (eventually_riemannianEDist_lt I p hr2)).and_eventually
    (eventually_ge_atTop T)).exists
  have hstay : ∀ s ≥ t₀, Manifold.riemannianEDist I p (γ s) < r := fun s hs ↦
    riemannianEDist_lt_of_lojasiewicz hf hx hle hθ hc (fun y hy ↦ hrU hy) (hT t₀ ht₀T).2 ht₀
      (hT t₀ ht₀T).1 hs
  -- Hence the tail lengths of `γ` after `t₀` tend to `0`.
  refine Manifold.tendsto_of_mapClusterPt_of_forall_pathELength_le
    ((contMDiffOn_maximalIntegralCurve_neg_mgradient hf).mono hx) hp fun ε hε ↦ ?_
  filter_upwards [eventually_ge_atTop t₀, ENNReal.tendsto_nhds_zero.1 hL0 ε hε] with t ht hLt s
  rcases le_total t s with hts | hst
  · exact (pathELength_le_of_forall_abs_le hf hx hle hθ hc ((hT t₀ ht₀T).2.trans ht) hts
      fun u hu ↦ hrU (hstay u (ht.trans hu.1))).trans hLt
  · exact (Manifold.pathELength_mono le_rfl hst).trans (by simp)

end ClusterPoint

end TauCeti
