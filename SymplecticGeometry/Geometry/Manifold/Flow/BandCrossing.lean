/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.IntegralCurve.GlobalFlow
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import TauCeti.Geometry.Manifold.IntegralCurve.Monotone
import TauCeti.Geometry.Manifold.MFDeriv.Curve
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Integral curves cross a band of descent in bounded time

Let `v` be a vector field and `f : M → ℝ` a function with `df(v) ≤ 0`. If `df(v) ≤ -ε` for some
`ε > 0` on the band `f⁻¹[a, b]`, an integral curve that starts at or below the level `b` loses at
least `ε` of height per unit of time while it is in the band, so it is strictly below the level
`a` once more than `(b - a) / ε` units of time have passed. When the band is compact, `f` is `C¹`
and `v` is continuous, `df(v)` is bounded away from zero on the band as soon as it is negative
there, so a single time works for every integral curve starting at or below `b`. For a complete
`C¹` field this says that the flow `TauCeti.globalFlow v` carries all of `{f ≤ b}` below the
level `a` within a common time.

While an integral curve is in the band, `f` decreases strictly along it; this already follows
from Tau Ceti's `IsMIntegralCurve.lt_of_mvfderiv_apply_lt_zero`.

The proofs follow those of Tau Ceti's `TauCeti.comp_maximalIntegralCurve_neg_mgradient_le_sub_mul`,
`TauCeti.comp_maximalIntegralCurve_neg_mgradient_lt` and
`TauCeti.exists_forall_comp_maximalIntegralCurve_neg_mgradient_lt`
(`TauCeti/Geometry/Manifold/Morse/GradientFlow.lean`), which treat the field `-grad f`, for which
`df(v) = -‖grad f‖²`; here the field is any field along which `f` does not increase.

## Main results

* `IsMIntegralCurveOn.apply_le_add_mul`: if `df(v) ≤ C` along an integral curve on `[s, t]`, then
  `f` grows by at most `C (t - s)` along it.
* `IsMIntegralCurve.apply_lt_of_mvfderiv_apply_le_neg`: an integral curve along which `f` does
  not increase, starting at or below `b`, is below `a` after a time `t` with `ε t > b - a`, when
  `df(v) ≤ -ε` at its points in the band `f⁻¹[a, b]`.
* `TauCeti.exists_forall_isMIntegralCurve_apply_lt`: on a compact band where `df(v) < 0`, one time
  works for every such integral curve.
* `TauCeti.exists_forall_globalFlow_lt`: the flow of a complete `C¹` field with `df(v) ≤ 0` carries
  `{f ≤ b}` below `a` within a common time.

## References

* M. W. Hirsch, S. Smale and R. L. Devaney, *Differential Equations, Dynamical Systems, and an
  Introduction to Chaos*, second edition, Academic Press, 2004, Chapter 9 (gradient systems).
* J. Milnor, *Morse Theory*, Princeton University Press, 1963, Theorem 3.1.
-/

public section

open Set
open scoped Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {v : (x : M) → TangentSpace I x} {γ : ℝ → M} {f : M → ℝ}

/-- **Growth along an integral curve with bounded derivative.** If `f` is differentiable along an
integral curve `γ` of `v` on `[s, t]` and `df(v) ≤ C` at the points of `γ` at times in `(s, t)`,
then `f (γ t) ≤ f (γ s) + C (t - s)`. -/
theorem IsMIntegralCurveOn.apply_le_add_mul {s t C : ℝ} (hγ : IsMIntegralCurveOn γ v (Icc s t))
    (hf : ∀ u ∈ Icc s t, MDifferentiableAt I 𝓘(ℝ) f (γ u))
    (hC : ∀ u ∈ Ioo s t, mvfderiv I f (γ u) (v (γ u)) ≤ C) (hst : s ≤ t) :
    f (γ t) ≤ f (γ s) + C * (t - s) := by
  have hd (u : ℝ) (hu : u ∈ Icc s t) :=
    TauCeti.Manifold.hasDerivWithinAt_comp_curve (hf u hu) (hγ u hu)
  have hd' (u : ℝ) (hu : u ∈ interior (Icc s t)) :
      HasDerivAt (f ∘ γ) (mvfderiv I f (γ u) (v (γ u))) u :=
    (hd u (interior_subset hu)).hasDerivAt (mem_interior_iff_mem_nhds.1 hu)
  have h := (convex_Icc s t).image_sub_le_mul_sub_of_deriv_le
    (fun u hu ↦ (hd u hu).continuousWithinAt)
    (fun u hu ↦ (hd' u hu).differentiableAt.differentiableWithinAt)
    (fun u hu ↦ by
      rw [(hd' u hu).deriv]
      exact hC u (by rwa [interior_Icc] at hu))
    s ⟨le_rfl, hst⟩ t ⟨hst, le_rfl⟩ hst
  simp only [Function.comp_apply] at h
  linarith

/-- **Crossing a band of descent.** Let `γ` be an integral curve of `v` along which `f` is
differentiable with `df(v) ≤ 0`, and with `df(v) ≤ -ε` at its points in the band `f⁻¹[a, b]`. If
`f (γ s) ≤ b`, then `f (γ t) < a` at every time `t ≥ s` with `b - a < ε (t - s)`: the curve cannot
stay in the band for that long. -/
theorem IsMIntegralCurve.apply_lt_of_mvfderiv_apply_le_neg (hγ : IsMIntegralCurve γ v)
    (hf : ∀ u, MDifferentiableAt I 𝓘(ℝ) f (γ u)) (hvf : ∀ u, mvfderiv I f (γ u) (v (γ u)) ≤ 0)
    {a b ε : ℝ} (hε : ∀ u, a ≤ f (γ u) → f (γ u) ≤ b → mvfderiv I f (γ u) (v (γ u)) ≤ -ε)
    {s t : ℝ} (hs : f (γ s) ≤ b) (hst : s ≤ t) (hεt : b - a < ε * (t - s)) : f (γ t) < a := by
  have hanti := hγ.antitone_comp hf hvf
  by_contra! h
  -- Between the times `s` and `t` the curve stays in the band, since `f` decreases along it.
  have hle := (hγ.isMIntegralCurveOn (Icc s t)).apply_le_add_mul (fun u _ ↦ hf u)
    (fun u hu ↦ hε u (h.trans (hanti hu.2.le)) ((hanti hu.1.le).trans hs)) hst
  linarith

namespace TauCeti

/-- **Crossing a compact band of descent in a common time.** Let `v` be a continuous vector field
and `f` a `C¹` function such that the band `f⁻¹[a, b]` is compact and `df(v) < 0` on it. There is
a time `T ≥ 0` such that every integral curve `γ` of `v` along which `df(v) ≤ 0`, with
`f (γ s) ≤ b`, satisfies `f (γ t) < a` for all `t ≥ s + T`. -/
theorem exists_forall_isMIntegralCurve_apply_lt [IsManifold I 1 M]
    (hv : Continuous fun y ↦ (⟨y, v y⟩ : TangentBundle I M)) (hf : ContMDiff I 𝓘(ℝ) 1 f)
    {a b : ℝ} (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hneg : ∀ y, a ≤ f y → f y ≤ b → mvfderiv I f y (v y) < 0) :
    ∃ T, 0 ≤ T ∧ ∀ γ : ℝ → M, IsMIntegralCurve γ v →
      (∀ u, mvfderiv I f (γ u) (v (γ u)) ≤ 0) → ∀ s t, f (γ s) ≤ b → s + T ≤ t → f (γ t) < a := by
  -- On the compact band, `df(v)` attains a negative maximum `-ε`.
  obtain ⟨ε, hε0, hε⟩ : ∃ ε > 0, ∀ y, a ≤ f y → f y ≤ b → mvfderiv I f y (v y) ≤ -ε := by
    rcases (f ⁻¹' Icc a b).eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun y ha hb ↦ (he.subset (mem_preimage.2 ⟨ha, hb⟩)).elim⟩
    have hcont : Continuous fun y ↦ mvfderiv I f y (v y) :=
      (hf.contMDiff_mvfderiv_apply (m := 0) (by simp)).continuous.comp hv
    obtain ⟨y₀, hy₀, hmax⟩ := hcompact.exists_isMaxOn hne hcont.continuousOn
    refine ⟨_, neg_pos.2 (hneg y₀ hy₀.1 hy₀.2), fun y ha hb ↦ ?_⟩
    rw [neg_neg]
    exact isMaxOn_iff.1 hmax y ⟨ha, hb⟩
  refine ⟨max 0 ((b - a) / ε) + 1, by positivity, fun γ hγ hvf s t hs hst ↦
    hγ.apply_lt_of_mvfderiv_apply_le_neg (fun u ↦ (hf (γ u)).mdifferentiableAt one_ne_zero) hvf
      (fun u ha hb ↦ hε (γ u) ha hb) hs (by linarith [le_max_left 0 ((b - a) / ε)]) ?_⟩
  have : (b - a) / ε < t - s := by linarith [le_max_right 0 ((b - a) / ε)]
  exact (div_lt_iff₀' hε0).1 this

variable [CompleteSpace E] [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M]

/-- **The flow crosses a compact band of descent in a common time.** Let `v` be a complete `C¹`
vector field and `f` a `C¹` function with `df(v) ≤ 0`, such that the band `f⁻¹[a, b]` is compact
and `df(v) < 0` on it. There is a time `T ≥ 0` such that the flow of `v` carries every point of
`{f ≤ b}` strictly below the level `a` at every time `t ≥ T`. -/
theorem exists_forall_globalFlow_lt
    (hv : ContMDiff I I.tangent 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hcomplete : IsCompleteVectorField v) (hf : ContMDiff I 𝓘(ℝ) 1 f)
    (hvf : ∀ y, mvfderiv I f y (v y) ≤ 0) {a b : ℝ} (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hneg : ∀ y, a ≤ f y → f y ≤ b → mvfderiv I f y (v y) < 0) :
    ∃ T, 0 ≤ T ∧ ∀ x, f x ≤ b → ∀ t, T ≤ t → f (globalFlow v hv hcomplete t x) < a := by
  obtain ⟨T, hT0, hT⟩ := exists_forall_isMIntegralCurve_apply_lt hv.continuous hf hcompact hneg
  refine ⟨T, hT0, fun x hx t ht ↦ hT _ (isMIntegralCurve_globalFlow hv hcomplete x)
    (fun u ↦ hvf _) 0 t ?_ (by linarith)⟩
  rwa [Flow.map_zero_apply]

end TauCeti

end
