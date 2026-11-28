/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Complete
import TauCeti.Geometry.Manifold.IntegralCurve.Reparam

/-!
# Completeness of rescaled vector fields

Let `X` be a complete `C¹` vector field on a Hausdorff boundaryless manifold, and `a` a continuous
real function that is bounded and never zero. Then `a • X` is complete. Along a global integral
curve `γ` of `X`, the field `a • X` is `(a ∘ γ) • X`, and Tau Ceti's reparametrization
`IsMIntegralCurve.exists_homeomorph_isMIntegralCurve_comp_of_abs_le` turns `γ` into a global
integral curve `γ ∘ ψ` of `a • X` through the same point, since `ψ 0 = 0`. No regularity of `a`
beyond continuity is needed, and `a • X` need not be `C¹`.

## Main results

* `TauCeti.IsCompleteVectorField.smul_of_ne_zero_of_abs_le`: `a • X` is complete when `a` is
  continuous, nowhere zero and `|a| ≤ c`.
* `TauCeti.IsCompleteVectorField.smul_of_pos_of_le`: `a • X` is complete when `a` is continuous
  and `0 < a ≤ c`.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Lemma 12.1 (i), whose rescaled Liouville field is such a multiple, with `0 < a ≤ 1`.
-/

public section

open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [BoundarylessManifold I M] [IsManifold I 1 M]

namespace IsCompleteVectorField

/-- A complete `C¹` vector field `X` multiplied by a continuous nowhere vanishing function `a`
with `|a| ≤ c` is complete. -/
theorem smul_of_ne_zero_of_abs_le {X : (x : M) → TangentSpace I x}
    (hX : IsCompleteVectorField X)
    (hXd : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, X x⟩ : TangentBundle I M)))
    {a : M → ℝ} (ha : Continuous a) (ha0 : ∀ x, a x ≠ 0) {c : ℝ} (hc : ∀ x, |a x| ≤ c) :
    IsCompleteVectorField fun x ↦ a x • X x :=
  isCompleteVectorField_of_forall_exists_isMIntegralCurve fun x ↦
    let ⟨γ, hγ0, hγ⟩ := hX.exists_isMIntegralCurve hXd x
    let ⟨ψ, hψ0, hψ⟩ := hγ.exists_homeomorph_isMIntegralCurve_comp_of_abs_le
      (ha.comp hγ.continuous) (fun t ↦ ha0 (γ t)) (fun t ↦ hc (γ t)) fun _ ↦ rfl
    ⟨γ ∘ ψ, by simp [hψ0, hγ0], hψ⟩

/-- A complete `C¹` vector field `X` multiplied by a continuous function `a` with `0 < a ≤ c` is
complete. -/
theorem smul_of_pos_of_le {X : (x : M) → TangentSpace I x}
    (hX : IsCompleteVectorField X)
    (hXd : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, X x⟩ : TangentBundle I M)))
    {a : M → ℝ} (ha : Continuous a) (hpos : ∀ x, 0 < a x) {c : ℝ} (hc : ∀ x, a x ≤ c) :
    IsCompleteVectorField fun x ↦ a x • X x :=
  hX.smul_of_ne_zero_of_abs_le hXd ha (fun x ↦ (hpos x).ne') fun x ↦
    (abs_of_pos (hpos x)).trans_le (hc x)

end IsCompleteVectorField

end TauCeti

end
