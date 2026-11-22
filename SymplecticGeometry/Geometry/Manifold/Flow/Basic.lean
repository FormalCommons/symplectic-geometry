/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

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
* `TauCeti.contDiffOn_flowOf_uncurry`, `TauCeti.hasFDerivAt_flowOf_uncurry_zero`: for a `C^n`
  field, `1 ≤ n`, on a complete normed space, the flow is `C^n` on its domain, and for a `C¹`
  field its derivative at time zero is `(r, u) ↦ r • v y + u`. They read Tau Ceti's
  `TauCeti.contMDiffOn_flowOf` and `TauCeti.mfderiv_flowOf_zero_apply` in the model space.
-/

public section

open scoped Manifold

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

end TauCeti

end
