/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Interior
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
public import TauCeti.Geometry.Symplectic.Liouville.VectorField

/-!
# Pulling Liouville vector fields back along related fields

Let `Φ : M' → M` be a smooth map, `σ` a smooth closed two-form on `M` and `X` a Liouville vector
field of `σ`. If a vector field `Y` on `M'` is `Φ`-related to `X`, that is
`dΦ_x (Y x) = X (Φ x)` for every `x`, then `Y` is a Liouville vector field of `Φ^* σ`
(`TauCeti.IsLiouvilleVectorField.mpullback`). The differential of `Φ` need not be invertible,
and the models are arbitrary models with corners, so this applies for instance to the inclusion
of a regular sublevel set, a manifold with boundary, into the ambient manifold.

The proof uses the characterization of Liouville fields of closed forms by Cartan's formula,
`TauCeti.isLiouvilleVectorField_iff_mextDeriv_interior_eq`: the claim is
`d (ι_Y Φ^* σ) = Φ^* σ`, and `ι_Y Φ^* σ = Φ^* (ι_X σ)` (`TauCeti.mpullback_interior`), while the
exterior derivative commutes with pullback (`TauCeti.mpullback_mextDeriv`).

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.5
  (Liouville vector fields)
* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Chapter 11 (Liouville and Weinstein structures)
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

variable {E H M E' H' M' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {I' : ModelWithCorners ℝ E' H'}
  [IsManifold I 2 M] [IsManifold I' 2 M']

/-- **Liouville fields pull back along related fields.** Let `Φ : M' → M` be smooth, `σ` a
smooth closed two-form on `M`, and `X` a `C¹` Liouville vector field of `σ`. A differentiable
vector field `Y` on `M'` with `dΦ_x (Y x) = X (Φ x)` for every `x` is a Liouville vector field
of the pulled-back form `Φ^* σ`. No invertibility of `dΦ` is assumed, and `M'` may have a
boundary. -/
theorem IsLiouvilleVectorField.mpullback {Φ : M' → M} (hΦ : ContMDiff I' I ∞ Φ)
    {σ : SmoothForm I M ℝ 2} (hσ : mextDeriv σ.val = 0) {X : (x : M) → TangentSpace I x}
    (hX : ContMDiff I I.tangent 1 (fun y ↦ (X y : TangentBundle I M)))
    (hXσ : IsLiouvilleVectorField σ.val X) {Y : (x : M') → TangentSpace I' x}
    (hY : MDifferentiable I' I'.tangent (fun y ↦ (Y y : TangentBundle I' M')))
    (hXY : ∀ x, mfderiv I' I Φ x (Y x) = X (Φ x)) :
    IsLiouvilleVectorField (SmoothForm.mpullback Φ hΦ σ).val Y := by
  have hσ' : IsSmoothForm I 1 σ.val := σ.isSmoothForm.of_le (by simp)
  rw [isLiouvilleVectorField_iff_mextDeriv_interior_eq
    ((SmoothForm.mpullback Φ hΦ σ).mdifferentiable) hY
    (SmoothForm.coe_mpullback Φ hΦ σ ▸ hσ'.mextDeriv_mpullback_eq_zero hσ (hΦ.of_le (by simp)))]
  rw [isLiouvilleVectorField_iff_mextDeriv_interior_eq (σ.mdifferentiable)
    (hX.mdifferentiable one_ne_zero) hσ] at hXσ
  rw [SmoothForm.coe_mpullback, ← mpullback_interior Φ Y X σ.val hXY,
    ← mpullback_mextDeriv (hΦ.of_le (by simp))
      ((isSmoothBundleForm_def 1 _).mpr (hσ'.interior hX).contMDiff), hXσ]

end TauCeti

end
