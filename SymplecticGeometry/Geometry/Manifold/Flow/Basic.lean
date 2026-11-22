/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Prod
public import TauCeti.Geometry.Manifold.ContMDiff.Prod
public import TauCeti.Geometry.Manifold.Flow.Basic

/-!
# Differentials of the time maps of a maximal flow

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
* `TauCeti.contDiffOn_flowOf_uncurry`, `TauCeti.hasDerivAt_flowOf`,
  `TauCeti.hasFDerivAt_flowOf_uncurry_zero`: for a smooth field on a complete normed space, the
  flow is smooth on its domain, its trajectories have the field as derivative, and its derivative
  at time zero is `(r, u) ↦ r • v y + u`; the first two read Tau Ceti's
  `TauCeti.contMDiffOn_flowOf` and `TauCeti.isMIntegralCurveOn_flowOf` in the model space.
-/

public section

open scoped Manifold ContDiff

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

/-- The flow of a smooth vector field on a normed space is smooth on its domain. -/
theorem contDiffOn_flowOf_uncurry (hv : ContDiff ℝ ∞ v) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E ↦ flowOf (I := 𝓘(ℝ, E)) v p.1 p.2)
      (flowDomain (I := 𝓘(ℝ, E)) v) := by
  have h := contMDiffOn_flowOf (I := 𝓘(ℝ, E)) (n := ⊤) le_top
    (contMDiff_vectorSpace_iff_contDiff.2 hv)
  rw [contMDiffOn_prod_modelWithCornersSelf_iff] at h
  exact contMDiffOn_iff_contDiffOn.1 h

/-- A trajectory of the flow of a smooth vector field on a normed space has the field as its
derivative, at every time of the flow domain. -/
theorem hasDerivAt_flowOf (hv : ContDiff ℝ ∞ v) {t : ℝ} {y : E}
    (ht : (t, y) ∈ flowDomain (I := 𝓘(ℝ, E)) v) :
    HasDerivAt (fun s ↦ flowOf (I := 𝓘(ℝ, E)) v s y) (v (flowOf (I := 𝓘(ℝ, E)) v t y)) t := by
  have hv1 : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle 𝓘(ℝ, E) E)) :=
    contMDiff_vectorSpace_iff_contDiff.2 (hv.of_le (m := 1) (by simp))
  have hopen : IsOpen {s | (s, y) ∈ flowDomain (I := 𝓘(ℝ, E)) v} :=
    (isOpen_flowDomain hv1).preimage (continuous_id.prodMk continuous_const)
  exact (isMIntegralCurveOn_iff_isIntegralCurveOn.1 (isMIntegralCurveOn_flowOf hv1 y) t ht)
    |>.hasDerivAt (hopen.mem_nhds ht)

/-- The derivative at time zero of the flow of a smooth vector field `v` on a normed space, as a
function of time and initial point, is `(r, u) ↦ r • v y + u`. -/
theorem hasFDerivAt_flowOf_uncurry_zero (hv : ContDiff ℝ ∞ v) (y : E) :
    HasFDerivAt (fun p : ℝ × E ↦ flowOf (I := 𝓘(ℝ, E)) v p.1 p.2)
      ((ContinuousLinearMap.fst ℝ ℝ E).smulRight (v y) + ContinuousLinearMap.snd ℝ ℝ E)
      (0, y) := by
  have hv1 : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle 𝓘(ℝ, E) E)) :=
    contMDiff_vectorSpace_iff_contDiff.2 (hv.of_le (m := 1) (by simp))
  have h0 := mem_flowDomain_zero hv1 y
  have hD := ((contDiffOn_flowOf_uncurry hv).contDiffAt
    ((isOpen_flowDomain hv1).mem_nhds h0)).differentiableAt (by simp) |>.hasFDerivAt
  set D := fderiv ℝ (fun p : ℝ × E ↦ flowOf (I := 𝓘(ℝ, E)) v p.1 p.2) (0, y)
  -- In the time direction, the derivative is the field.
  have h1 : D (1, 0) = v y := by
    have hc : HasDerivAt (fun s : ℝ ↦ (s, y)) ((1 : ℝ), (0 : E)) 0 :=
      HasDerivAt.prodMk (hasDerivAt_id _) (hasDerivAt_const _ _)
    have ht := hD.comp_hasDerivAt (0 : ℝ) hc
    have ht' := hasDerivAt_flowOf hv h0
    have hz := flowOf_zero (I := 𝓘(ℝ, E)) v y
    rw [hz] at ht'
    exact ht.unique ht'
  -- In the space directions, it is the identity, since the time-zero map is the identity.
  have h2 (u : E) : D (0, u) = u := by
    have hs := hD.comp y (hasFDerivAt_prodMk_right (0 : ℝ) y)
    have hid : ((fun p : ℝ × E ↦ flowOf (I := 𝓘(ℝ, E)) v p.1 p.2) ∘ Prod.mk (0 : ℝ)) = id :=
      funext fun z ↦ flowOf_zero v z
    rw [hid] at hs
    exact (DFunLike.congr_fun (hs.unique (hasFDerivAt_id y)) u)
  refine hD.congr_fderiv (ContinuousLinearMap.ext fun q ↦ ?_)
  have hq : q = q.1 • ((1 : ℝ), (0 : E)) + ((0 : ℝ), q.2) := by ext <;> simp
  rw [hq, map_add, map_smul, h1, h2]
  simp

end NormedSpace

end TauCeti

end
