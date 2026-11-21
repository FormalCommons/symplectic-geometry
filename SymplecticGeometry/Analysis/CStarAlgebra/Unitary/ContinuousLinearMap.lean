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

/-- The unitary group of the algebra `𝕜 →L[𝕜] 𝕜`, with the operator-norm topology, is isomorphic
as a topological group to `unitary 𝕜`: a unitary `u` goes to `u 1`, and `α` goes to
multiplication by `α`. -/
def continuousLinearMapSelfEquiv : unitary (𝕜 →L[𝕜] 𝕜) ≃ₜ* unitary 𝕜 where
  toMulEquiv := ((StrongUnitary.unitaryEquivStrongUnitary 𝕜).toMulEquiv.trans
    StrongUnitary.mulEquivUnitary).symm
  continuous_toFun := continuous_induced_rng.2 <|
    ((continuous_eval_const (1 : 𝕜)).comp continuous_subtypeVal).congr fun u ↦ Eq.symm <|
      (StrongUnitary.coe_unitaryEquivStrongUnitary_symm _).trans <|
        (congrArg (fun v : StrongUnitary 𝕜 𝕜 ↦ v 1)
          (StrongUnitary.mulEquivUnitary_symm_apply u)).trans (StrongUnitary.ofUnitary_apply u 1)
  continuous_invFun := continuous_induced_rng.2 <|
    (continuous_subtypeVal.smul (continuous_const (y := (1 : 𝕜 →L[𝕜] 𝕜)))).congr fun α ↦
      ContinuousLinearMap.ext fun x ↦ Eq.symm <|
        (congrArg (fun v : unitary (𝕜 →L[𝕜] 𝕜) ↦ (v : 𝕜 →L[𝕜] 𝕜) x)
          (StrongUnitary.mulEquivUnitary_apply _)).trans <| by
            rw [StrongUnitary.coe_toUnitary, StrongUnitary.toCLM_apply]
            exact StrongUnitary.unitaryEquivStrongUnitary_apply α x

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
  (StrongUnitary.coe_unitaryEquivStrongUnitary_symm _).trans <|
    (congrArg (fun v : StrongUnitary 𝕜 𝕜 ↦ v 1) (StrongUnitary.mulEquivUnitary_symm_apply u)).trans
      (StrongUnitary.ofUnitary_apply u 1)

@[simp]
theorem continuousLinearMapSelfEquiv_symm_apply (α : unitary 𝕜) (x : 𝕜) :
    ((continuousLinearMapSelfEquiv 𝕜).symm α : 𝕜 →L[𝕜] 𝕜) x = (α : 𝕜) * x :=
  (congrArg (fun v : unitary (𝕜 →L[𝕜] 𝕜) ↦ (v : 𝕜 →L[𝕜] 𝕜) x)
    (StrongUnitary.mulEquivUnitary_apply _)).trans <| by
      rw [StrongUnitary.coe_toUnitary, StrongUnitary.toCLM_apply]
      exact StrongUnitary.unitaryEquivStrongUnitary_apply α x

end Unitary

end

end
