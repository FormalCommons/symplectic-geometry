/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

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

end TauCeti

end
