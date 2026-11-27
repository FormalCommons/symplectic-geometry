/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Flow
import SymplecticGeometry.Analysis.ODE.Basic
import SymplecticGeometry.Geometry.Manifold.Flow.Basic
import TauCeti.Geometry.Manifold.IntegralCurve.Monotone

/-!
# Compactly supported flow diffeotopies on a normed space

Facts about Tau Ceti's `TauCeti.compactlySupportedFlowDiffeotopy` of a compactly supported vector
field `v : E → E` on a finite-dimensional real normed space `E`: a bound on how far it moves a
point, and the quantities it keeps.

## Main results

* `SymplecticGeometry.norm_compactlySupportedFlowDiffeotopy_sub_le`: the compactly supported flow
  diffeotopy of a field of norm at most `M`, run for a duration `a ≥ 0`, moves each point by at
  most `a * t * M` at time `t`.
* `SymplecticGeometry.map_compactlySupportedFlowDiffeotopy`: a continuous linear map that kills
  a compactly supported field keeps its value along the flow diffeotopy of the field.
-/

public section

open Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace SymplecticGeometry

variable [FiniteDimensional ℝ E]

/-- **Displacement of a compactly supported flow.** If a compactly supported `C^n` vector field
`v` on a finite-dimensional real normed space has norm at most `M` everywhere, then its flow
diffeotopy run for a duration `a ≥ 0` moves each point by at most `a * t * M` at time `t`. -/
theorem norm_compactlySupportedFlowDiffeotopy_sub_le {v : E → E}
    {K : Set E} {n : ℕ∞} (hn : 1 ≤ n)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent (n : WithTop ℕ∞)
      (fun y ↦ (⟨y, v y⟩ : TangentBundle 𝓘(ℝ, E) E)))
    (hK : IsCompact K) (hzero : ∀ y ∉ K, v y = 0) {a M : ℝ} (ha : 0 ≤ a)
    (hM : ∀ y, ‖v y‖ ≤ M) (t : unitInterval) (x : E) :
    ‖TauCeti.compactlySupportedFlowDiffeotopy hn hv hK hzero a (t, x) - x‖ ≤ a * t * M := by
  have := ((TauCeti.isIntegralCurve_maximalIntegralCurve_of_isCompact
    (hv.of_le (m := 1) (by exact_mod_cast hn)) hK hzero x).isIntegralCurveOn _).norm_sub_le_mul
    (fun s _ ↦ hM _) (mul_nonneg ha t.property.1)
  rw [maximalIntegralCurve_zero_of_vectorSpace, sub_zero] at this
  rw [TauCeti.compactlySupportedFlowDiffeotopy_apply hn hv hK hzero a (t, x)]
  linarith

/-- **Quantities kept by a compactly supported flow.** If a continuous linear map `L` kills a
compactly supported `C^n` vector field `v` on a finite-dimensional real normed space, then the
flow diffeotopy of `v`, run for any duration `a`, keeps the value of `L`. -/
theorem map_compactlySupportedFlowDiffeotopy {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {v : E → E} {K : Set E} {n : ℕ∞} (hn : 1 ≤ n)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent (n : WithTop ℕ∞)
      (fun y ↦ (⟨y, v y⟩ : TangentBundle 𝓘(ℝ, E) E)))
    (hK : IsCompact K) (hzero : ∀ y ∉ K, v y = 0) (a : ℝ) (L : E →L[ℝ] F)
    (hL : ∀ y, L (v y) = 0) (t : unitInterval) (x : E) :
    L (TauCeti.compactlySupportedFlowDiffeotopy hn hv hK hzero a (t, x)) = L x := by
  have := (TauCeti.isMIntegralCurveOn_iff_isIntegralCurveOn.2
    ((TauCeti.isIntegralCurve_maximalIntegralCurve_of_isCompact (hv.of_le (m := 1)
      (by exact_mod_cast hn)) hK hzero x).isIntegralCurveOn univ)
    ).apply_eq_add_smul_of_mvfderiv_apply_eq (g := L) (c := 0) isPreconnected_univ
      (fun _ _ ↦ L.mdifferentiableAt)
      (fun s _ ↦ by simp only [mvfderiv_eq_fderiv, L.fderiv]; exact hL _) (mem_univ 0)
      (mem_univ (a * t))
  rw [maximalIntegralCurve_zero_of_vectorSpace, smul_zero, add_zero] at this
  rw [TauCeti.compactlySupportedFlowDiffeotopy_apply hn hv hK hzero a (t, x)]
  exact this

end SymplecticGeometry

end
