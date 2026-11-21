/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.StrongUnitary.Basic

/-!
# Unitaries of `𝕜 →L[𝕜] 𝕜`

For `RCLike 𝕜`, a continuous `𝕜`-linear endomorphism of `𝕜` is multiplication by its value at
`1`, and it is unitary exactly when that value is. This file records the resulting isomorphism of
topological groups between `unitary (𝕜 →L[𝕜] 𝕜)`, with the operator-norm topology, and
`unitary 𝕜`.

## Main definitions

* `Unitary.continuousLinearMapSelfEquiv 𝕜 : unitary (𝕜 →L[𝕜] 𝕜) ≃ₜ* unitary 𝕜`: evaluation at
  `1`, with inverse sending `α` to multiplication by `α`. As a group isomorphism it is by
  definition Tau Ceti's identification `TauCeti.StrongUnitary.unitaryEquivStrongUnitary`
  composed with `TauCeti.StrongUnitary.mulEquivUnitary`, so that the library uses a single
  identification of the two groups; what is new is continuity for the operator norm.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.6
  (unitary frames of Hermitian line bundles).
-/

public section

noncomputable section

open TauCeti

namespace Unitary

variable (𝕜 : Type*) [RCLike 𝕜]

/-- Tau Ceti's group isomorphism between `unitary (𝕜 →L[𝕜] 𝕜)` and `unitary 𝕜`, through the
strong unitary group; the topological group isomorphism below upgrades it. -/
private def mulEquivAux : unitary (𝕜 →L[𝕜] 𝕜) ≃* unitary 𝕜 :=
  ((StrongUnitary.unitaryEquivStrongUnitary 𝕜).toMulEquiv.trans
    StrongUnitary.mulEquivUnitary).symm

private theorem coe_mulEquivAux_apply (u : unitary (𝕜 →L[𝕜] 𝕜)) :
    (mulEquivAux 𝕜 u : 𝕜) = (u : 𝕜 →L[𝕜] 𝕜) 1 := by
  rw [mulEquivAux, MulEquiv.symm_trans_apply, StrongUnitary.mulEquivUnitary_symm_apply]
  exact (StrongUnitary.coe_unitaryEquivStrongUnitary_symm _).trans
    (StrongUnitary.ofUnitary_apply u 1)

private theorem mulEquivAux_symm_apply (α : unitary 𝕜) (x : 𝕜) :
    ((mulEquivAux 𝕜).symm α : 𝕜 →L[𝕜] 𝕜) x = (α : 𝕜) * x := by
  rw [mulEquivAux, MulEquiv.symm_symm, MulEquiv.trans_apply, StrongUnitary.mulEquivUnitary_apply,
    StrongUnitary.coe_toUnitary, StrongUnitary.coe_toCLM]
  exact StrongUnitary.unitaryEquivStrongUnitary_apply α x

/-- The unitary group of the algebra `𝕜 →L[𝕜] 𝕜`, with the operator-norm topology, is isomorphic
as a topological group to `unitary 𝕜`: a unitary `u` goes to `u 1`, and `α` goes to
multiplication by `α`. -/
def continuousLinearMapSelfEquiv : unitary (𝕜 →L[𝕜] 𝕜) ≃ₜ* unitary 𝕜 where
  toMulEquiv := mulEquivAux 𝕜
  continuous_toFun := by
    have h : ⇑(mulEquivAux 𝕜) = fun u ↦ ⟨(u : 𝕜 →L[𝕜] 𝕜) 1, by
        simpa only [coe_mulEquivAux_apply] using (mulEquivAux 𝕜 u).property⟩ :=
      funext fun u ↦ Subtype.ext (coe_mulEquivAux_apply 𝕜 u)
    rw [show (mulEquivAux 𝕜).toFun = _ from h]
    exact ((continuous_eval_const (1 : 𝕜)).comp continuous_subtypeVal).subtype_mk _
  continuous_invFun := by
    have h : ⇑(mulEquivAux 𝕜).symm = fun α ↦ ⟨(α : 𝕜) • (1 : 𝕜 →L[𝕜] 𝕜), by
        convert ((mulEquivAux 𝕜).symm α).property
        ext
        simp [mulEquivAux_symm_apply]⟩ :=
      funext fun α ↦ Subtype.ext <| ContinuousLinearMap.ext fun x ↦ by
        simp [mulEquivAux_symm_apply, mul_comm]
    rw [show (mulEquivAux 𝕜).invFun = _ from h]
    exact (continuous_subtypeVal.smul continuous_const).subtype_mk _

variable {𝕜}

/-- As a group isomorphism, `Unitary.continuousLinearMapSelfEquiv` is Tau Ceti's identification
through the strong unitary group. -/
theorem toMulEquiv_continuousLinearMapSelfEquiv :
    (continuousLinearMapSelfEquiv 𝕜).toMulEquiv =
      ((StrongUnitary.unitaryEquivStrongUnitary 𝕜).toMulEquiv.trans
        StrongUnitary.mulEquivUnitary).symm :=
  (rfl)

@[simp]
theorem coe_continuousLinearMapSelfEquiv_apply (u : unitary (𝕜 →L[𝕜] 𝕜)) :
    (continuousLinearMapSelfEquiv 𝕜 u : 𝕜) = (u : 𝕜 →L[𝕜] 𝕜) 1 :=
  coe_mulEquivAux_apply 𝕜 u

@[simp]
theorem continuousLinearMapSelfEquiv_symm_apply (α : unitary 𝕜) (x : 𝕜) :
    ((continuousLinearMapSelfEquiv 𝕜).symm α : 𝕜 →L[𝕜] 𝕜) x = (α : 𝕜) * x :=
  mulEquivAux_symm_apply 𝕜 α x

end Unitary

end

end
