/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# A unit vector of a line as a linear isometry equivalence

A unit vector `v` of a normed space `E` of dimension one, over a nontrivially normed field `𝕜`,
spans `E`, and `a ↦ a • v` is then a linear isometry equivalence `𝕜 ≃ₗᵢ[𝕜] E`. This upgrades
Mathlib's `LinearIsometry.toSpanSingleton` from an isometric embedding to an equivalence.

## Main definitions

* `LinearIsometryEquiv.toSpanSingleton 𝕜 E h hv : 𝕜 ≃ₗᵢ[𝕜] E`, for `h : finrank 𝕜 E = 1` and
  `hv : ‖v‖ = 1`, sending `a` to `a • v`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.7
  (unitary frames of a Hermitian line bundle are its unit vectors).
-/

public section

noncomputable section

open Module

namespace LinearIsometryEquiv

variable (𝕜 E : Type*) [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- For a unit vector `v` of a normed space `E` of dimension one, the linear isometry
equivalence `𝕜 ≃ₗᵢ[𝕜] E` sending `a` to `a • v`. -/
def toSpanSingleton (h : finrank 𝕜 E = 1) {v : E} (hv : ‖v‖ = 1) : 𝕜 ≃ₗᵢ[𝕜] E :=
  haveI : FiniteDimensional 𝕜 E := Module.finite_of_finrank_eq_succ h
  (LinearIsometry.toSpanSingleton 𝕜 E hv).toLinearIsometryEquiv (by rw [finrank_self, h])

variable {𝕜 E}

@[simp]
theorem toSpanSingleton_apply (h : finrank 𝕜 E = 1) {v : E} (hv : ‖v‖ = 1) (a : 𝕜) :
    toSpanSingleton 𝕜 E h hv a = a • v :=
  (rfl)

@[simp]
theorem toLinearIsometry_toSpanSingleton (h : finrank 𝕜 E = 1) {v : E} (hv : ‖v‖ = 1) :
    (toSpanSingleton 𝕜 E h hv).toLinearIsometry = LinearIsometry.toSpanSingleton 𝕜 E hv :=
  (rfl)

theorem toSpanSingleton_one (h : finrank 𝕜 E = 1) {v : E} (hv : ‖v‖ = 1) :
    toSpanSingleton 𝕜 E h hv 1 = v := by
  rw [toSpanSingleton_apply, one_smul]

end LinearIsometryEquiv

end

end
