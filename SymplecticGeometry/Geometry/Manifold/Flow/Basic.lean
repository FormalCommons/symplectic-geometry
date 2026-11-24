/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.Instances.Icc
public import TauCeti.Geometry.Manifold.Algebra.SMul
public import TauCeti.Geometry.Manifold.ContMDiff.Prod
public import TauCeti.Geometry.Manifold.Flow.Basic
public import TauCeti.Geometry.Manifold.Flow.Diffeomorph

/-!
# Maximal flows: differentials of the time maps, and integral curves

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
* `TauCeti.contDiffOn_flowOf_uncurry`, `TauCeti.hasFDerivAt_flowOf_uncurry_zero`: for a `C^n`
  field, `1 ≤ n`, on a complete normed space, the flow is `C^n` on its domain, and for a `C¹`
  field its derivative at time zero is `(r, u) ↦ r • v y + u`. They read Tau Ceti's
  `TauCeti.contMDiffOn_flowOf` and `TauCeti.mfderiv_flowOf_zero_apply` in the model space.
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

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {v : E → E}

/-- The flow of a `C^n` vector field on a normed space, `1 ≤ n`, is `C^n` on its domain. -/
theorem contDiffOn_flowOf_uncurry {n : ℕ∞} (hn : 1 ≤ n) (hv : ContDiff ℝ n v) :
    ContDiffOn ℝ n (fun p : ℝ × E ↦ flowOf (I := 𝓘(ℝ, E)) v p.1 p.2)
      (flowDomain (I := 𝓘(ℝ, E)) v) := by
  have h := contMDiffOn_flowOf (I := 𝓘(ℝ, E)) hn (contMDiff_vectorSpace_iff_contDiff.2 hv)
  rw [contMDiffOn_prod_modelWithCornersSelf_iff] at h
  exact contMDiffOn_iff_contDiffOn.1 h

/-- The derivative at time zero of the flow of a `C¹` vector field `v` on a normed space, as a
function of time and initial point, is `(r, u) ↦ r • v y + u`. -/
theorem hasFDerivAt_flowOf_uncurry_zero (hv : ContDiff ℝ 1 v) (y : E) :
    HasFDerivAt (fun p : ℝ × E ↦ flowOf (I := 𝓘(ℝ, E)) v p.1 p.2)
      ((ContinuousLinearMap.fst ℝ ℝ E).smulRight (v y) + ContinuousLinearMap.snd ℝ ℝ E)
      (0, y) := by
  have hv1 : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle 𝓘(ℝ, E) E)) :=
    contMDiff_vectorSpace_iff_contDiff.2 hv
  have hD := ((contDiffOn_flowOf_uncurry le_rfl hv).contDiffAt ((isOpen_flowDomain hv1).mem_nhds
    (mem_flowDomain_zero hv1 y))).differentiableAt one_ne_zero
  have h := mfderiv_flowOf_zero_apply hv1 y
  -- Name the flow map, so that the model of its source can be rewritten without retyping `v`.
  generalize (fun p : ℝ × E ↦ flowOf (I := 𝓘(ℝ, E)) v p.1 p.2) = G at h hD ⊢
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
  have hM := (mdifferentiableAt_iff_differentiableAt.2 hD).hasMFDerivAt
  rw [hasMFDerivAt_iff_hasFDerivAt] at hM
  refine hM.congr_fderiv (ContinuousLinearMap.ext fun ⟨a, u⟩ ↦ ?_)
  -- `h` is an equation in `E`, the goal one in the tangent space at `G (0, y)`, which is `E`.
  refine (h a u).trans ?_
  exact (show ((ContinuousLinearMap.fst ℝ ℝ E).smulRight (v y) + ContinuousLinearMap.snd ℝ ℝ E)
    (a, u) = a • v y + u by simp).symm

end NormedSpace

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

/-- If a `C¹` vector field `v` satisfies `df(v) = 1` on a set `W` where `f` is differentiable,
then `f (φ_t x) = f x + t` for the maximal flow `φ` of `v`, whenever `(t, x)` is in the flow
domain and the trajectory from time `0` to time `t` stays in `W`. -/
theorem apply_flowOf_eq_add
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    {f : M → ℝ} {W : Set M} (hf : ∀ y ∈ W, MDifferentiableAt I 𝓘(ℝ) f y)
    (hfv : ∀ y ∈ W, mfderiv I 𝓘(ℝ) f y (v y) = 1) {t : ℝ} {x : M}
    (ht : (t, x) ∈ flowDomain v) (htW : ∀ s ∈ uIcc 0 t, flowOf v s x ∈ W) :
    f (flowOf v t x) = f x + t := by
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

end Translation

end TauCeti

end
