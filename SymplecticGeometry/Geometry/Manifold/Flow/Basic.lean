/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.Instances.Icc
public import TauCeti.Geometry.Manifold.Algebra.SMul
public import TauCeti.Geometry.Manifold.Flow.Basic
public import TauCeti.Geometry.Manifold.Flow.Complete
public import TauCeti.Geometry.Manifold.Flow.Diffeomorph

/-!
# Maximal flows: time-map differentials, integral curves, equivariance, translation

Let `v` be a `C¹` vector field on a Hausdorff boundaryless manifold modelled on a complete space,
with maximal flow `φ` (`TauCeti.flowOf`). If time `t` is defined at `x`, the differentials
`(dφ_t)_x` and `(dφ_{-t})_{φ_t x}` are inverse to each other
(`TauCeti.mfderiv_flowOf_neg_apply_mfderiv_flowOf`,
`TauCeti.mfderiv_flowOf_apply_mfderiv_flowOf_neg`). So a covector `p` at `x` is carried by the
time-`t` map to the covector `p ∘ (dφ_{-t})_{φ_t x}` at `φ_t x`. Both statements follow from Tau
Ceti's chain rule for the time maps, `TauCeti.mfderiv_flowOf_add_apply`, and
`TauCeti.mfderiv_flowOf_zero_apply_eq_self`.

## Main results

* `TauCeti.mfderiv_flowOf_neg_apply_mfderiv_flowOf`: `(dφ_{-t})_{φ_t x} ∘ (dφ_t)_x = id`.
* `TauCeti.mfderiv_flowOf_apply_mfderiv_flowOf_neg`: `(dφ_t)_x ∘ (dφ_{-t})_{φ_t x} = id`.
* `IsMIntegralCurveOn.comp_add_Ioo`, `IsMIntegralCurveOn.sub_mem_flowDomain`,
  `IsMIntegralCurveOn.flowOf_sub_eq`: an integral curve `γ` on `(a, b)` shifted in time stays an
  integral curve, and for `t₀, t ∈ (a, b)` the maximal flow takes `γ t₀` to `γ t` in time
  `t - t₀`, from Tau Ceti's `IsMIntegralCurveOn.subset_maximalIntegralCurveInterval` and
  `IsMIntegralCurveOn.eqOn_maximalIntegralCurve`.
* `TauCeti.eventuallyEq_flowOf_sub_of_isMIntegralCurveOn`,
  `TauCeti.contMDiffAt_of_isMIntegralCurveOn`: if the lines `t ↦ Φ (t, s)` of `Φ : ℝ × S → M`
  are integral curves on `(a, b)`, then near each point of `(a, b) × S` the map `Φ` is the flow
  out of its slice at some `t₀ ∈ (a, b)`, run for time `t - t₀`; so `Φ` is `C^n` there when the
  field and that slice are, by Tau Ceti's `TauCeti.contMDiffAt_flowOf_comp`.
* `TauCeti.smul_flowOf`: the maximal flow of a `C¹` field invariant under a `C¹` group action
  commutes with the action; this is Tau Ceti's `Diffeomorph.apply_flowOf` for
  `Diffeomorph.constSmul`.
* `TauCeti.apply_flowOf_eq_add`: if `df(v) = 1` on a set `W`, then `f (φ_t x) = f x + t` as long
  as the trajectory from time `0` to time `t` stays in `W`, by Tau Ceti's
  `TauCeti.hasDerivAt_comp_flowOf` and the mean value inequality.
* `TauCeti.eventually_apply_flowOf_eq_add`: if `df(v) = 1` near `φ_r x`, then
  `f (φ_s x) = f (φ_r x) + (s - r)` for `s` near `r`.
* `TauCeti.apply_flowOf_eq_add_of_preimage_uIcc_subset`: if time `t` is defined at `x`, `f` is
  continuous and `df(v) = 1` on an open set `W`, then `f (φ_t x) = f x + t` as soon as `W`
  contains every level of `f` between `f x` and `f x + t`. Here the trajectory is not assumed to
  stay in `W`: the times near which `f` grows like time form an open subset of `[0, t]` (or
  `[t, 0]`) that is closed in it, so all of it, by connectedness.
* `TauCeti.apply_flowOf_sub_eq`, `TauCeti.flowOf_sub_level_injective`,
  `TauCeti.range_flowOf_sub_level`: if moreover the field is complete and `W` contains the band
  `f⁻¹([a, b])`, the map `(x, s) ↦ φ_{s - a} x` from `{x // f x = a} × [a, b]` to `M` takes
  `(x, s)` to the level `s`, is injective, and has the band as its range. This is the local
  version of Tau Ceti's `Flow.zeroLevelProductDiffeomorph`, where `f` grows like time along the
  whole flow. Tau Ceti's `Flow.bandHomeomorph`, `Flow.apply_eq_sub_of_mem_Icc` and
  `TauCeti.apply_globalFlow_eq_sub` are close relatives under stronger hypotheses.
* `TauCeti.isIntegralCurve_maximalIntegralCurve_of_isCompact`: on a complete real normed space,
  the maximal integral curve of a compactly supported `C¹` field is a global integral curve, by
  Tau Ceti's `TauCeti.isCompleteVectorField_of_isCompact_of_eq_zero_off`.
* `maximalIntegralCurve_zero_of_vectorSpace`: Tau Ceti's `maximalIntegralCurve_zero` for a field
  given as a map `E → E`, as a `simp` lemma.
-/

public section

open Set Filter
open scoped Manifold Topology

namespace TauCeti

section FlowInverse

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [BoundarylessManifold I M] [IsManifold I 1 M] {v : (x : M) → TangentSpace I x}
  {t : ℝ} {x : M}

/-- **The differential of the time-`(-t)` map inverts that of the time-`t` map.** Along a
trajectory of a `C¹` vector field, if time `t` is defined at `x`, the differential of the
time-`(-t)` map at `flowOf v t x` is a left inverse of the differential of the time-`t` map
at `x`. -/
theorem mfderiv_flowOf_neg_apply_mfderiv_flowOf
    (hv : ContMDiff I I.tangent 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (ht : (t, x) ∈ flowDomain v) (w : TangentSpace I x) :
    -- The tangent spaces at `flowOf v (-t) (flowOf v t x)` and `x` are both the model space `E`.
    @Eq E (mfderiv I I (flowOf v (-t)) (flowOf v t x) (mfderiv I I (flowOf v t) x w)) w := by
  rw [mfderiv_flowOf_add_apply hv ht rfl (neg_mem_flowDomain_flowOf hv ht), add_neg_cancel]
  exact mfderiv_flowOf_zero_apply_eq_self v x w

/-- **The differential of the time-`(-t)` map inverts that of the time-`t` map.** Along a
trajectory of a `C¹` vector field, if time `t` is defined at `x`, the differential of the
time-`(-t)` map at `flowOf v t x` is a right inverse of the differential of the time-`t` map
at `x`. -/
theorem mfderiv_flowOf_apply_mfderiv_flowOf_neg
    (hv : ContMDiff I I.tangent 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (ht : (t, x) ∈ flowDomain v) (w : TangentSpace I (flowOf v t x)) :
    mfderiv I I (flowOf v t) x (mfderiv I I (flowOf v (-t)) (flowOf v t x) w) = w := by
  rw [mfderiv_flowOf_add_apply hv (neg_mem_flowDomain_flowOf hv ht) (flowOf_neg_flowOf hv ht) ht,
    neg_add_cancel]
  exact mfderiv_flowOf_zero_apply_eq_self v _ w

end FlowInverse

section IntegralCurve

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {v : (x : M) → TangentSpace I x} {γ : ℝ → M} {a b t₀ t : ℝ}

/-- Shifting time by `dt` turns an integral curve on `(a, b)` into one on `(a - dt, b - dt)`. -/
theorem _root_.IsMIntegralCurveOn.comp_add_Ioo (hγ : IsMIntegralCurveOn γ v (Ioo a b)) (dt : ℝ) :
    IsMIntegralCurveOn (γ ∘ (· + dt)) v (Ioo (a - dt) (b - dt)) := by
  rw [← preimage_add_const_Ioo]
  exact hγ.comp_add dt

/-- If `γ` is an integral curve of `v` on `(a, b)` and `t₀, t ∈ (a, b)`, the maximal flow of `v`
from `γ t₀` is defined at time `t - t₀`. -/
theorem _root_.IsMIntegralCurveOn.sub_mem_flowDomain (hγ : IsMIntegralCurveOn γ v (Ioo a b))
    (ht₀ : t₀ ∈ Ioo a b) (ht : t ∈ Ioo a b) : (t - t₀, γ t₀) ∈ flowDomain v :=
  mem_flowDomain.2 ((hγ.comp_add_Ioo t₀).subset_maximalIntegralCurveInterval
    ⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩ (by simp) ⟨by linarith [ht.1], by linarith [ht.2]⟩)

/-- **An integral curve is a trajectory of the flow.** On a Hausdorff boundaryless manifold, if
`γ` is an integral curve of the `C¹` vector field `v` on `(a, b)` and `t₀, t ∈ (a, b)`, the
maximal flow of `v` takes `γ t₀` to `γ t` in time `t - t₀`. -/
theorem _root_.IsMIntegralCurveOn.flowOf_sub_eq [T2Space M] [IsManifold I 1 M]
    [BoundarylessManifold I M]
    (hv : ContMDiff I I.tangent 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hγ : IsMIntegralCurveOn γ v (Ioo a b)) (ht₀ : t₀ ∈ Ioo a b) (ht : t ∈ Ioo a b) :
    flowOf v (t - t₀) (γ t₀) = γ t := by
  rw [flowOf_apply, (hγ.comp_add_Ioo t₀).eqOn_maximalIntegralCurve hv
    ⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩ (by simp) ⟨by linarith [ht.1], by linarith [ht.2]⟩]
  simp

/-- If the lines `t ↦ Φ (t, s)` of `Φ : ℝ × S → M` are integral curves of the `C¹` field `v` on
`(a, b)` and `t₀, t ∈ (a, b)`, then near `(t, s)` the map `Φ` is the maximal flow of `v` out of the
slice at `t₀`, run for time `q.1 - t₀`. -/
theorem eventuallyEq_flowOf_sub_of_isMIntegralCurveOn [CompleteSpace E] [T2Space M]
    [IsManifold I 1 M] [BoundarylessManifold I M] {S : Type*} [TopologicalSpace S]
    {Φ : ℝ × S → M} (hv : ContMDiff I I.tangent 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hΦ : ∀ s, IsMIntegralCurveOn (fun t ↦ Φ (t, s)) v (Ioo a b)) (ht₀ : t₀ ∈ Ioo a b)
    (ht : t ∈ Ioo a b) (s : S) :
    Φ =ᶠ[𝓝 (t, s)] fun q ↦ flowOf v (q.1 - t₀) (Φ (t₀, q.2)) := by
  filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds (mk_mem_prod ht (mem_univ s))] with p hp
  exact ((hΦ p.2).flowOf_sub_eq hv ht₀ hp.1).symm

/-- If the lines `t ↦ Φ (t, s)` of `Φ : ℝ × S → M` are integral curves of the `C^n` field `v`,
`1 ≤ n`, on `(a, b)` and the slice `Φ (t₀, ·)` at some `t₀ ∈ (a, b)` is `C^n`, then `Φ` is `C^n`
at every point of `(a, b) × S`. -/
theorem contMDiffAt_of_isMIntegralCurveOn [CompleteSpace E] [T2Space M] [IsManifold I 1 M]
    [BoundarylessManifold I M] {n : ℕ∞} (hn : 1 ≤ n) [IsManifold I n M]
    {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S] {Φ : ℝ × S → M}
    (hv : ContMDiff I I.tangent n (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hΦ : ∀ s, IsMIntegralCurveOn (fun t ↦ Φ (t, s)) v (Ioo a b)) (ht₀ : t₀ ∈ Ioo a b)
    (hΦ₀ : ContMDiff J I n fun s ↦ Φ (t₀, s)) (ht : t ∈ Ioo a b) (s : S) :
    ContMDiffAt (𝓘(ℝ).prod J) I n Φ (t, s) :=
  (contMDiffAt_flowOf_comp hn hv (contMDiffAt_fst.sub contMDiffAt_const)
    (hΦ₀.comp contMDiff_snd).contMDiffAt ((hΦ s).sub_mem_flowDomain ht₀ ht)).congr_of_eventuallyEq
    (eventuallyEq_flowOf_sub_of_isMIntegralCurveOn (hv.of_le (mod_cast hn)) hΦ ht₀ ht s)

end IntegralCurve

section Translation

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I 1 M] [BoundarylessManifold I M] {v : (x : M) → TangentSpace I x}

/-- **Equivariance of flows.** The maximal flow of a `C¹` vector field `v` that is invariant under
a `C¹` group action (the differential of each `g • ·` carries `v x` to `v (g • x)`) commutes
with the action. -/
theorem smul_flowOf {G : Type*} [Group G] [MulAction G M] [ContMDiffConstSMul I 1 G M]
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hinv : ∀ (g : G) (x : M), mfderiv I I (g • ·) x (v x) = v (g • x)) (g : G) (t : ℝ)
    (x : M) :
    g • flowOf v t x = flowOf v t (g • x) := by
  simpa [Diffeomorph.coe_constSmul] using (Diffeomorph.constSmul I 1 g).apply_flowOf one_ne_zero
    hv (by rw [Diffeomorph.coe_constSmul]; exact hinv g) t x

/-- If a `C¹` vector field `v` satisfies `df(v) = 1` on a set `W`, then
`f (φ_t x) = f x + t` for the maximal flow `φ` of `v`, whenever `(t, x)` is in the flow domain
and the trajectory from time `0` to time `t` stays in `W`. -/
theorem apply_flowOf_eq_add
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    {f : M → ℝ} {W : Set M} (hfv : ∀ y ∈ W, mfderiv I 𝓘(ℝ) f y (v y) = 1) {t : ℝ} {x : M}
    (ht : (t, x) ∈ flowDomain v) (htW : ∀ s ∈ uIcc 0 t, flowOf v s x ∈ W) :
    f (flowOf v t x) = f x + t := by
  -- `df(v) = 1 ≠ 0` on `W`, so `f` is differentiable there.
  have hf (y : M) (hy : y ∈ W) : MDifferentiableAt I 𝓘(ℝ) f y :=
    mdifferentiableAt_of_mvfderiv_apply_ne_zero (v := v y) (by
      rw [mvfderiv_apply_eq_mfderiv_apply, hfv y hy]
      exact one_ne_zero)
  have hderiv : ∀ s ∈ uIcc 0 t,
      HasDerivWithinAt (fun s ↦ f (flowOf v s x) - s) 0 (uIcc 0 t) s := by
    intro s hs
    have hd := hasDerivAt_comp_flowOf hv (uIcc_subset_setOf_mem_flowDomain ht hs)
      (hf _ (htW s hs))
    rw [mvfderiv_apply_eq_mfderiv_apply, hfv _ (htW s hs)] at hd
    have hd' : HasDerivAt (fun s ↦ f (flowOf v s x) - s) (1 - 1) s := hd.sub (hasDerivAt_id' s)
    rw [sub_self] at hd'
    exact hd'.hasDerivWithinAt
  have h := (convex_uIcc 0 t).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv
    (fun _ _ ↦ by simp : ∀ s ∈ uIcc 0 t, ‖(0 : ℝ)‖ ≤ 0) left_mem_uIcc right_mem_uIcc
  rw [zero_mul, norm_le_zero_iff, flowOf_zero] at h
  linarith

/-- **Local translation along the flow.** If a `C¹` vector field `v` satisfies `df(v) = 1` on a
neighbourhood `W` of `φ_r x`, where `φ` is the maximal flow of `v` and `(r, x)` is in its domain,
then `f (φ_s x) = f (φ_r x) + (s - r)` for all `s` near `r`. -/
theorem eventually_apply_flowOf_eq_add
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    {f : M → ℝ} {W : Set M} (hfv : ∀ y ∈ W, mfderiv I 𝓘(ℝ) f y (v y) = 1) {r : ℝ} {x : M}
    (hr : (r, x) ∈ flowDomain v) (hW : W ∈ 𝓝 (flowOf v r x)) :
    ∀ᶠ s in 𝓝 r, f (flowOf v s x) = f (flowOf v r x) + (s - r) := by
  have hdom : {s | (s, x) ∈ flowDomain v} ∈ 𝓝 r := by
    simpa only [mem_flowDomain, ofPred_mem_eq] using
      isOpen_maximalIntegralCurveInterval.mem_nhds (mem_flowDomain.mp hr)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1
    (inter_mem hdom ((mdifferentiableAt_flowOf hv hr).continuousAt.preimage_mem_nhds hW))
  filter_upwards [Metric.ball_mem_nhds r hε] with s hs
  -- The times from `r` to `s` stay in the ball, so in the domain and, flowed, in `W`.
  have hmem (q : ℝ) (hq : q ∈ uIcc 0 (s - r)) : r + q ∈ Metric.ball r ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs ⊢
    rcases mem_uIcc.1 hq with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> constructor <;> linarith
  have hsr : (s - r, flowOf v r x) ∈ flowDomain v := by
    rw [mem_flowDomain_flowOf_iff hv hr, add_sub_cancel]
    exact (hball hs).1
  have key := apply_flowOf_eq_add hv hfv hsr fun q hq ↦ by
    have hq' : (q, flowOf v r x) ∈ flowDomain v :=
      (mem_flowDomain_flowOf_iff hv hr).2 (hball (hmem q hq)).1
    rw [(flowOf_add hv hr hq').2]
    exact (hball (hmem q hq)).2
  rwa [(flowOf_add hv hr hsr).2, add_sub_cancel] at key

/-- **Translation along the flow between two levels.** Let `v` be a `C¹` vector field with
maximal flow `φ`, with time `t` defined at `x`, and `f` a continuous function with `df(v) = 1` on
an open set `W`. If `W` contains every point where `f` takes a value between `f x` and `f x + t`,
then `f (φ_t x) = f x + t`, for `t` of either sign. -/
theorem apply_flowOf_eq_add_of_preimage_uIcc_subset
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    {f : M → ℝ} (hf : Continuous f) {W : Set M}
    (hW : IsOpen W) (hfv : ∀ y ∈ W, mfderiv I 𝓘(ℝ) f y (v y) = 1) {t : ℝ} {x : M}
    (ht : (t, x) ∈ flowDomain v) (hband : f ⁻¹' uIcc (f x) (f x + t) ⊆ W) :
    f (flowOf v t x) = f x + t := by
  have hdom := uIcc_subset_setOf_mem_flowDomain ht
  have hloc (r : ℝ) (hr : f (flowOf v r x) = f x + r) (hrt : r ∈ uIcc 0 t) :
      ∀ᶠ s in 𝓝 r, f (flowOf v s x) = f x + s := by
    have hrW : flowOf v r x ∈ W := hband <| by
      rw [mem_preimage, hr, mem_uIcc]
      rcases mem_uIcc.1 hrt with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact Or.inl ⟨by linarith, by linarith⟩
      · exact Or.inr ⟨by linarith, by linarith⟩
    filter_upwards [eventually_apply_flowOf_eq_add hv hfv (hdom hrt) (hW.mem_nhds hrW)]
      with s hs
    rw [hs, hr]
    ring
  -- The times near which `f` grows like time along the trajectory form an open set that
  -- contains `0` and is closed in `uIcc 0 t`, so contains all of it. For the closedness,
  -- `s ↦ f (φ_s x) - s` is continuous at each time of `uIcc 0 t` and equals `f x` on that set.
  have hsub : uIcc 0 t ⊆ {r | ∀ᶠ s in 𝓝 r, f (flowOf v s x) = f x + s} := by
    refine isPreconnected_uIcc.subset_of_closure_inter_subset isOpen_setOfPred_eventually_nhds
      ⟨0, left_mem_uIcc, hloc 0 (by rw [flowOf_zero, add_zero]) left_mem_uIcc⟩ ?_
    rintro r ⟨hr, hrt⟩
    have hg : ContinuousAt (fun s ↦ f (flowOf v s x) - s) r :=
      (hf.continuousAt.comp (mdifferentiableAt_flowOf hv (hdom hrt)).continuousAt).sub
        continuousAt_id
    have himage : (fun s ↦ f (flowOf v s x) - s) ''
        {r | ∀ᶠ s in 𝓝 r, f (flowOf v s x) = f x + s} ⊆ {f x} := by
      rintro _ ⟨s, hs, rfl⟩
      simp only [mem_singleton_iff]
      rw [hs.self_of_nhds, add_sub_cancel_right]
    have hr' := closure_mono himage (mem_closure_image hg hr)
    rw [closure_singleton, mem_singleton_iff] at hr'
    exact hloc r (by linarith) hrt
  exact (hsub right_mem_uIcc).self_of_nhds

section Band

variable (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
  (hcomplete : IsCompleteVectorField v) {f : M → ℝ} (hf : Continuous f) {W : Set M}
  (hW : IsOpen W) (hfv : ∀ y ∈ W, mfderiv I 𝓘(ℝ) f y (v y) = 1) {a b : ℝ}
  (hband : f ⁻¹' Icc a b ⊆ W)
include hv hcomplete hf hW hfv hband

/-- **The flow from the bottom level of a band.** Let `v` be a complete `C¹` vector field with
maximal flow `φ`, and `f` a continuous function with `df(v) = 1` on an open set containing the
band `f⁻¹([a, b])`. Flowing a point of the level `f = a` for time `s - a`, with `s ∈ [a, b]`,
lands on the level `f = s`. -/
theorem apply_flowOf_sub_eq {x : M} (hx : f x = a) {s : ℝ} (hs : s ∈ Icc a b) :
    f (flowOf v (s - a) x) = s := by
  have hsub : uIcc (f x) (f x + (s - a)) ⊆ Icc a b := by
    rw [hx, add_sub_cancel]
    exact uIcc_subset_Icc (left_mem_Icc.2 (hs.1.trans hs.2)) hs
  rw [apply_flowOf_eq_add_of_preimage_uIcc_subset hv hf hW hfv
    (hcomplete.mem_flowDomain _ _) ((preimage_mono hsub).trans hband), hx, add_sub_cancel]

/-- **The flow from the bottom level of a band is injective.** Under the hypotheses of
`TauCeti.apply_flowOf_sub_eq`, the map `(x, s) ↦ φ_{s - a} x` from the product of the level
`f = a` with `[a, b]` to `M` is injective. -/
theorem flowOf_sub_level_injective :
    Function.Injective fun p : {x : M // f x = a} × Icc a b ↦ flowOf v (p.2 - a) p.1 := by
  rintro ⟨⟨x, hx⟩, s, hs⟩ ⟨⟨y, hy⟩, s', hs'⟩ h
  dsimp only at h
  obtain rfl : s = s' := by
    rw [← apply_flowOf_sub_eq hv hcomplete hf hW hfv hband hx hs, h,
      apply_flowOf_sub_eq hv hcomplete hf hW hfv hband hy hs']
  obtain rfl : x = y := by
    rw [← flowOf_neg_flowOf hv (hcomplete.mem_flowDomain (s - a) x), h,
      flowOf_neg_flowOf hv (hcomplete.mem_flowDomain (s - a) y)]
  rfl

/-- **The flow from the bottom level sweeps out the band.** Under the hypotheses of
`TauCeti.apply_flowOf_sub_eq`, the range of the map `(x, s) ↦ φ_{s - a} x` from the product of
the level `f = a` with `[a, b]` to `M` is the band `f⁻¹([a, b])`. -/
theorem range_flowOf_sub_level :
    range (fun p : {x : M // f x = a} × Icc a b ↦ flowOf v (p.2 - a) p.1) = f ⁻¹' Icc a b := by
  ext y
  constructor
  · rintro ⟨⟨⟨x, hx⟩, s, hs⟩, rfl⟩
    rw [mem_preimage, apply_flowOf_sub_eq hv hcomplete hf hW hfv hband hx hs]
    exact hs
  · intro hy
    have hsub : uIcc (f y) (f y + (a - f y)) ⊆ Icc a b := by
      rw [add_sub_cancel]
      exact uIcc_subset_Icc hy (left_mem_Icc.2 (hy.1.trans hy.2))
    have hlev : f (flowOf v (a - f y) y) = a := by
      rw [apply_flowOf_eq_add_of_preimage_uIcc_subset hv hf hW hfv
        (hcomplete.mem_flowDomain _ _) ((preimage_mono hsub).trans hband), add_sub_cancel]
    refine ⟨(⟨_, hlev⟩, ⟨f y, hy⟩), ?_⟩
    dsimp only
    rw [← neg_sub (f y) a, flowOf_flowOf_neg hv hcomplete]

end Band

end Translation

section CompactSupport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The maximal integral curve of a compactly supported `C¹` vector field on a complete real
normed space is a global integral curve. -/
theorem isIntegralCurve_maximalIntegralCurve_of_isCompact {v : E → E} {K : Set E}
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1
      (fun y ↦ (⟨y, v y⟩ : TangentBundle 𝓘(ℝ, E) E)))
    (hK : IsCompact K) (hzero : ∀ y ∉ K, v y = 0) (x : E) :
    IsIntegralCurve (maximalIntegralCurve (I := 𝓘(ℝ, E)) v x) (fun _ ↦ v) :=
  isIntegralCurveOn_univ.1 <| isMIntegralCurveOn_iff_isIntegralCurveOn.1 <|
    (isMIntegralCurve_maximalIntegralCurve_of_eq_univ hv
      ((isCompleteVectorField_of_isCompact_of_eq_zero_off hv hK hzero)
        |>.maximalIntegralCurveInterval_eq_univ x)).isMIntegralCurveOn univ

end CompactSupport

end TauCeti

section VectorSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The maximal integral curve of a vector field `v : E → E` on a real normed space starts at its
initial point. This is `maximalIntegralCurve_zero`, stated for a field valued in the tangent
spaces of `E`; `simp` does not find that one for an `E`-valued field, nor does `rw` unless
`v` is named. -/
@[simp]
theorem maximalIntegralCurve_zero_of_vectorSpace (v : E → E) (x : E) :
    maximalIntegralCurve (I := 𝓘(ℝ, E)) v x 0 = x :=
  maximalIntegralCurve_zero

end VectorSpace

end
